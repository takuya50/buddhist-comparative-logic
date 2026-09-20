#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regenerate bounded dependency and witness audits after the full proof build."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "audit"
LEAN_INPUT = "verification/representative_axioms.lean"
ISABELLE_INPUT = "verification/Representative_Oracles.thy"
ALLOWED_LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def default_lake() -> str:
    if os.environ.get("LAKE_BIN"):
        return os.environ["LAKE_BIN"]
    if os.environ.get("LEAN_BIN"):
        return str(Path(os.environ["LEAN_BIN"]).parent / "lake")
    if shutil.which("lake"):
        return shutil.which("lake") or "lake"
    machine = platform.machine().lower()
    system = platform.system()
    target = {
        ("Linux", "x86_64"): "linux", ("Linux", "amd64"): "linux",
        ("Linux", "aarch64"): "linux_aarch64", ("Linux", "arm64"): "linux_aarch64",
        ("Darwin", "x86_64"): "darwin", ("Darwin", "amd64"): "darwin",
        ("Darwin", "aarch64"): "darwin_aarch64", ("Darwin", "arm64"): "darwin_aarch64",
    }.get((system, machine))
    if target:
        version = (ROOT / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
        prefix = Path(os.environ.get("LEAN_PREFIX", str(Path.home() / ".local/opt")))
        return str(prefix / f"lean-{version}-{target}" / "bin/lake")
    return "lake"


def default_isabelle() -> str:
    if os.environ.get("ISABELLE_HOME"):
        return str(Path(os.environ["ISABELLE_HOME"]) / "bin/isabelle")
    if shutil.which("isabelle"):
        return shutil.which("isabelle") or "isabelle"
    prefix = Path(os.environ.get("ISABELLE_PREFIX", str(Path.home() / ".local/opt")))
    app = "Isabelle2025-2.app" if platform.system() == "Darwin" else "Isabelle2025-2"
    return str(prefix / app / "bin/isabelle")


def check_lean_report(output: str, source: str) -> int:
    expected = re.findall(r"^#print axioms (\S+)$", source, re.MULTILINE)
    found = re.findall(
        r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|"
        r"does not depend on any axioms)\s*$", output, re.MULTILINE,
    )
    if [name for name, _ in found] != expected or not expected:
        raise ValueError("Lean report does not cover exactly the requested declarations")
    for name, dependencies in found:
        axioms = {item.strip() for item in dependencies.split(",") if item.strip()}
        if not axioms <= ALLOWED_LEAN_AXIOMS:
            raise ValueError(f"unexpected Lean axiom dependency for {name}: {sorted(axioms)}")
    return len(expected)


def check_isabelle_report(output: str, source: str) -> int:
    reports = re.findall(r"^oracles:(.*?)(?=^Finished Draft\b|\Z)",
                         output, re.MULTILINE | re.DOTALL)
    if len(reports) != 1 or reports[0].strip():
        raise ValueError("expected exactly one empty Isabelle oracle report")
    selection = re.search(r"\bthm_oracles\s+(.*?)\s+end\s*$", source, re.DOTALL)
    if not selection:
        raise ValueError("cannot identify the Isabelle representative selection")
    return len(selection.group(1).split())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=default_lake(), help="Lake executable (or LAKE_BIN)")
    parser.add_argument("--isabelle", default=default_isabelle(), help="Isabelle2025-2 executable")
    parser.add_argument("--cbeta-xml", type=Path, help="separately acquired pinned CBETA XML")
    args = parser.parse_args()
    AUDIT.mkdir(parents=True, exist_ok=True)
    replacements = {str(ROOT): ".", str(Path.home()): "<home>", sys.executable: "python3"}
    if sys.prefix != sys.base_prefix:
        replacements[sys.prefix] = "<python-env>"
    for executable, label in ((args.lake, "<lake-bin>"), (args.isabelle, "<isabelle-bin>")):
        if Path(executable).is_absolute():
            replacements[str(Path(executable))] = label
            replacements[str(Path(executable).parent.parent)] = label.replace("-bin", "-home")
    if args.cbeta_xml:
        replacements[str(args.cbeta_xml.resolve())] = "<external-cbeta.xml>"

    def sanitize(value: str) -> str:
        for original, replacement in sorted(replacements.items(), key=lambda pair: -len(pair[0])):
            value = value.replace(original, replacement)
        return value

    summary = {
        "schema": 1,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "status": "INCOMPLETE",
        "scope": "Representative dependencies and optional pinned-witness comparison; not a full build receipt.",
        "steps": [],
        "cbeta": ("NOT RUN (earlier steps not completed)" if args.cbeta_xml
                  else "NOT RUN (no --cbeta-xml supplied)"),
    }

    def save_summary() -> None:
        (AUDIT / "representative-receipt.json").write_text(
            json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8",
        )

    def run(name: str, command: list[str], report: str) -> str:
        print(f"{name} ...", flush=True)
        env = os.environ.copy()
        env.pop("JAVA_TOOL_OPTIONS", None)
        result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = sanitize(result.stdout)
        (AUDIT / report).write_text(output, encoding="utf-8")
        summary["steps"].append({
            "name": name, "command": sanitize(shlex.join(command)),
            "exit_code": result.returncode, "report": f"audit/{report}",
            "report_sha256": hashlib.sha256(output.encode("utf-8")).hexdigest(),
        })
        save_summary()
        if result.returncode:
            raise subprocess.CalledProcessError(result.returncode, command)
        return output

    save_summary()
    # Prevent a prior successful optional report from appearing to belong to this run.
    (AUDIT / "cbeta-comparison.txt").write_text(summary["cbeta"] + "\n", encoding="utf-8")
    try:
        expected_lean = (ROOT / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
        lean_version = run("Lean version", [args.lake, "env", "lean", "--version"], "lean-version.txt")
        if not re.search(r"\bversion " + re.escape(expected_lean) + r"(?:\s|,|$)", lean_version):
            raise ValueError("Lean version does not match lean-toolchain")
        isabelle_version = run("Isabelle version", [args.isabelle, "version"], "isabelle-version.txt")
        if isabelle_version.strip() != "Isabelle2025-2":
            raise ValueError("expected Isabelle2025-2")
        run("Lake import build", [args.lake, "build"], "lake-build.txt")
        output = run("Lean representative dependencies", [args.lake, "env", "lean", LEAN_INPUT],
                     "lean-axioms.txt")
        summary["lean_declarations"] = check_lean_report(
            output, (ROOT / LEAN_INPUT).read_text(encoding="utf-8"))
        output = run("Isabelle representative oracles", [args.isabelle, "process_theories",
                     "-D", "verification", "-d", "isabelle", "-l", "Buddhist_Comparative_Logic",
                     "-O", "-U", "Representative_Oracles"], "isabelle-oracles.txt")
        summary["isabelle_declarations"] = check_isabelle_report(
            output, (ROOT / ISABELLE_INPUT).read_text(encoding="utf-8"))
        if args.cbeta_xml:
            summary["cbeta"] = "INCOMPLETE"
            run("Pinned CBETA witness comparison", [sys.executable, "tools/compare_cbeta_witness.py",
                str(args.cbeta_xml.resolve())], "cbeta-comparison.txt")
            summary["cbeta"] = "PASS (pinned external XML; not redistributed)"
        run("Software source snapshot", [sys.executable, "tools/make_snapshot.py"], "snapshot.txt")
        summary["status"] = "PASS"
        summary["meaning"] = (
            "Requested representative dependency checks passed. Lean dependencies are restricted to "
            "propext, Classical.choice and Quot.sound; the selected Isabelle oracle list is empty. "
            "Record fields and theorem arguments remain premises. CBETA is separate and may be NOT RUN."
        )
        save_summary()
        print("PASS: representative audit checks; see audit/representative-receipt.json")
        print("CBETA: " + summary["cbeta"])
        return 0
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        summary["status"] = "FAIL"
        summary["error"] = sanitize(str(error))
        save_summary()
        print("FAIL: " + summary["error"], file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and 0 < error.returncode < 256:
            return error.returncode
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
