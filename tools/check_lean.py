#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Type-check every module in the Buddhist comparative logic library.

Local imports are topologically sorted from the source files themselves, so
adding a module does not require maintaining a second build-order manifest.
Compiled artefacts live in a temporary directory and never touch the source
tree.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = REPO_ROOT / "lean"
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)
# Scan comment/string-erased source for proof admissions and declarations that
# can introduce unproved or code-generation-backed constants.  Matching these
# keywords anywhere also catches attributed and private declarations, rather
# than only a line-leading `axiom`.
TRUST_BYPASS = re.compile(
    r"\b(?:sorry|admit|sorryAx|axiom|constant|opaque|unsafe|partial"
    r"|native_decide|ofReduceBool|implemented_by|extern)\b"
)
TOOLCHAIN = (REPO_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
EXPECTED_VERSION = TOOLCHAIN.rsplit(":v", 1)[-1]
LAKEFILE = REPO_ROOT / "lakefile.toml"


def module_name(path: Path) -> str:
    """Return the dotted Lean module name for a source below ``lean/``."""
    return ".".join(path.relative_to(LEAN_DIR).with_suffix("").parts)


def local_imports(path: Path, modules: set[str]) -> set[str]:
    imports: set[str] = set()
    source = erase_comments_and_strings(path.read_text(encoding="utf-8"))
    for declaration in IMPORT.findall(source):
        for name in declaration.split():
            if name in modules:
                imports.add(name)
    return imports


def dependency_graph(files: dict[str, Path]) -> dict[str, set[str]]:
    return {name: local_imports(path, set(files)) for name, path in files.items()}


def check_aggregate_closure(dependencies: dict[str, set[str]]) -> None:
    aggregate = "BuddhistComparativeLogic"
    if aggregate not in dependencies:
        raise ValueError("aggregate module BuddhistComparativeLogic.lean is missing")
    reachable: set[str] = set()
    pending = [aggregate]
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        pending.extend(dependencies[module])
    missing = sorted(set(dependencies) - reachable)
    if missing:
        raise ValueError(
            "aggregate BuddhistComparativeLogic.lean does not import: "
            + ", ".join(missing)
        )


def build_order(dependencies: dict[str, set[str]]) -> list[str]:
    visiting: set[str] = set()
    visited: set[str] = set()
    order: list[str] = []

    def visit(name: str, trail: tuple[str, ...] = ()) -> None:
        if name in visited:
            return
        if name in visiting:
            cycle = " -> ".join((*trail, name))
            raise ValueError(f"local import cycle: {cycle}")
        visiting.add(name)
        for dependency in sorted(dependencies[name]):
            visit(dependency, (*trail, name))
        visiting.remove(name)
        visited.add(name)
        order.append(name)

    for module in sorted(dependencies):
        visit(module)
    return order


def erase_comments_and_strings(source: str) -> str:
    """Blank comments and strings while preserving offsets and line numbers.

    Lean block comments nest.  Keeping every newline lets diagnostics point to
    the original source even after lexical material has been erased.
    """
    chars = list(source)
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    while index < len(chars):
        pair = source[index : index + 2]
        char = source[index]
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
            else:
                chars[index] = " "
            index += 1
            continue
        if block_depth:
            if pair == "/-":
                chars[index] = chars[index + 1] = " "
                block_depth += 1
                index += 2
            elif pair == "-/":
                chars[index] = chars[index + 1] = " "
                block_depth -= 1
                index += 2
            else:
                if char != "\n":
                    chars[index] = " "
                index += 1
            continue
        if in_string:
            if char != "\n":
                chars[index] = " "
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "--":
            chars[index] = chars[index + 1] = " "
            in_line_comment = True
            index += 2
        elif pair == "/-":
            chars[index] = chars[index + 1] = " "
            block_depth = 1
            index += 2
        elif char == '"':
            chars[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    return "".join(chars)


def check_admissions(files: dict[str, Path]) -> None:
    problems: list[str] = []
    for path in files.values():
        text = erase_comments_and_strings(path.read_text(encoding="utf-8"))
        for match in TRUST_BYPASS.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            source = path.relative_to(REPO_ROOT).as_posix()
            problems.append(f"{source}:{line}: {match.group(0).strip()}")
    if problems:
        joined = "\n  ".join(problems)
        raise ValueError(f"trust-bypassing declaration found:\n  {joined}")


def check_lake_roots(files: dict[str, Path]) -> None:
    # The supported Python on older macOS installations predates tomllib.
    # This deliberately parses only Lake's quoted roots array, after removing
    # TOML comments outside strings.
    lines: list[str] = []
    for line in LAKEFILE.read_text(encoding="utf-8").splitlines():
        in_string = False
        escaped = False
        kept: list[str] = []
        for char in line:
            if char == "#" and not in_string:
                break
            kept.append(char)
            if in_string and escaped:
                escaped = False
            elif in_string and char == "\\":
                escaped = True
            elif char == '"':
                in_string = not in_string
        lines.append("".join(kept))
    text = "\n".join(lines)
    match = re.search(r"^roots\s*=\s*\[(.*?)^\]", text, re.MULTILINE | re.DOTALL)
    if not match:
        raise ValueError("lakefile.toml has no roots list")
    root_entries = re.findall(r'"([A-Za-z][A-Za-z0-9_.]*)"', match.group(1))
    roots = set(root_entries)
    duplicates = sorted(name for name in roots if root_entries.count(name) > 1)
    missing = sorted(set(files) - roots)
    stale = sorted(roots - set(files))
    if missing or stale or duplicates:
        details = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if stale:
            details.append("unknown " + ", ".join(stale))
        if duplicates:
            details.append("duplicate " + ", ".join(duplicates))
        raise ValueError("lakefile.toml roots mismatch: " + "; ".join(details))

    default_match = re.search(r"^defaultTargets\s*=\s*\[(.*?)\]", text, re.M)
    defaults = re.findall(r'"([A-Za-z][A-Za-z0-9_.]*)"', default_match.group(1)) if default_match else []
    if defaults != ["BuddhistComparativeLogic"]:
        raise ValueError(
            "lakefile.toml defaultTargets must be [\"BuddhistComparativeLogic\"]"
        )


def check_lean_executable(lean: str) -> None:
    result = subprocess.run(
        [lean, "--version"], capture_output=True, text=True, check=False
    )
    version_text = (result.stdout + result.stderr).strip()
    expected = re.compile(rf"\bLean \(version {re.escape(EXPECTED_VERSION)}(?:[ ,)])")
    if result.returncode != 0 or not expected.search(version_text):
        raise ValueError(
            f"{lean!r} is not Lean {EXPECTED_VERSION}; got {version_text!r}"
        )


def compile_all(lean: str) -> None:
    files = {module_name(path): path for path in sorted(LEAN_DIR.rglob("*.lean"))}
    if not files:
        raise ValueError(f"no Lean sources under {LEAN_DIR}")
    check_lean_executable(lean)
    check_admissions(files)
    check_lake_roots(files)
    dependencies = dependency_graph(files)
    check_aggregate_closure(dependencies)
    order = build_order(dependencies)
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="buddhist-comparative-logic-lean-") as build:
        env = os.environ.copy()
        # Only modules compiled in this run may satisfy local imports.  Lean's
        # own Init/Lake packages are resolved from its sysroot, independently
        # of LEAN_PATH.
        env["LEAN_PATH"] = build
        for number, module in enumerate(order, 1):
            print(f"[{number:02d}/{len(order):02d}] {module}", flush=True)
            output = Path(build).joinpath(*module.split(".")).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                [
                    lean,
                    "-DwarningAsError=true",
                    "-o",
                    str(output),
                    str(files[module]),
                ],
                check=True,
                env=env,
            )
            if not output.is_file() or output.stat().st_size == 0:
                raise ValueError(f"Lean produced no .olean for {module}")
    elapsed = time.monotonic() - started
    print(f"Lean check OK: {len(order)} modules in {elapsed:.1f}s")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("lean", help="path to the Lean executable")
    args = parser.parse_args()
    try:
        compile_all(args.lean)
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"check_lean.py: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
