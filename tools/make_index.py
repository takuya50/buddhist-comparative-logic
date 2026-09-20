#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Generate catalog/index.json from the Heart Sutra case-study sources.

The two tables in docs/STATUS.md are the human-facing view: the clause table
and the Isabelle extensions table.  This script renders the same information
for tools to consume and validates the explicit Isabelle-to-Lean port map.
Generated data is never edited by hand.

    python3 tools/make_index.py
    python3 tools/make_index.py --check
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from check_lean import erase_comments_and_strings

REPO_ROOT = Path(__file__).resolve().parents[1]
ISABELLE = REPO_ROOT / "isabelle"
LEAN = REPO_ROOT / "lean"
STATUS = REPO_ROOT / "docs" / "STATUS.md"
INDEX = REPO_ROOT / "catalog" / "index.json"
ROOT = ISABELLE / "ROOT"
SESSION_NAME = "Buddhist_Comparative_Logic"
EXPECTED_CLAUSES = 31
EXPECTED_BODY_CHARACTERS = 262
EXPECTED_EXTENSION_RESULTS = 26

ROW = re.compile(
    r"^\|\s*(HS\d\d)\s*\|\s*([^|]*?)\s*\|\s*(\d+)\s*\|\s*([^|]*?)\s*\|"
    r"\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|\s*$",
    re.M,
)
NAME = re.compile(r"`([A-Za-z][A-Za-z0-9_.']*)`")
EXT_ROW = re.compile(
    r"^\|\s*`(?:[A-Za-z0-9_/-]+/)?([A-Za-z_][A-Za-z0-9_]*)\.thy`\s*\|"
    r"\s*([^|]*?)\s*\|"
    r"\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|\s*$",
    re.M,
)
DECL = re.compile(
    r"^\s*(?:theorem|lemma|corollary|definition|fun|abbreviation|locale|datatype"
    r"|primrec|inductive|lemmas|type_synonym|schematic_goal)\s+([A-Za-z][A-Za-z0-9_']*)",
    re.M,
)
LEAN_IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.M)

# Every entry is explicit so a renamed theory cannot silently fall back to a
# guessed Lean module. Paths are relative to isabelle/.
PORTS: dict[str, tuple[str, str]] = {
    "HeartSutra_Text": (
        "Buddhist/HeartSutra/HeartSutra_Text.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.Text",
    ),
    "HeartSutra_Dharma": (
        "Buddhist/HeartSutra/HeartSutra_Dharma.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.Dharma",
    ),
    "ManyValuedLogic": (
        "Core/ManyValuedLogic.thy",
        "BuddhistComparativeLogic.Core.MVLogic",
    ),
    "FiniteLogics": (
        "Core/FiniteLogics.thy",
        "BuddhistComparativeLogic.Core.Foundation",
    ),
    "Catuskoti": (
        "Core/Catuskoti.thy",
        "BuddhistComparativeLogic.Core.Foundation",
    ),
    "HeartSutra_Emptiness": (
        "Buddhist/HeartSutra/HeartSutra_Emptiness.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.Emptiness",
    ),
    "HeartSutra_Path": (
        "Buddhist/HeartSutra/HeartSutra_Path.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.Path",
    ),
    "HeartSutra_Mantra": (
        "Buddhist/HeartSutra/HeartSutra_Mantra.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.Mantra",
    ),
    "HeartSutra_Coverage": (
        "Buddhist/HeartSutra/HeartSutra_Coverage.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.Coverage",
    ),
    "Madhyamaka_MMK24": (
        "Buddhist/Madhyamaka/Madhyamaka_MMK24.thy",
        "BuddhistComparativeLogic.Buddhist.Madhyamaka.MMK",
    ),
    "HeartSutra_TwoTruths": (
        "Buddhist/HeartSutra/HeartSutra_TwoTruths.thy",
        "BuddhistComparativeLogic.Buddhist.Madhyamaka.TwoTruths",
    ),
    "HeartSutra_Connexive": (
        "Buddhist/HeartSutra/HeartSutra_Connexive.thy",
        "BuddhistComparativeLogic.Core.Connexive",
    ),
    "PlurivalentSemantics": (
        "Core/PlurivalentSemantics.thy",
        "BuddhistComparativeLogic.Core.Plurivalent",
    ),
    "Dignaga_Hetucakra": (
        "Buddhist/Pramana/Dignaga_Hetucakra.thy",
        "BuddhistComparativeLogic.Buddhist.Pramana.Hetucakra",
    ),
    "UniversalDesignation": (
        "Core/UniversalDesignation.thy",
        "BuddhistComparativeLogic.Core.UniversalDesignation",
    ),
    "DiamondSutra_Sokuhi": (
        "Buddhist/DiamondSutra/DiamondSutra_Sokuhi.thy",
        "BuddhistComparativeLogic.Buddhist.Madhyamaka.Sokuhi",
    ),
    "Madhyamaka_Jizang": (
        "Buddhist/Madhyamaka/Madhyamaka_Jizang.thy",
        "BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang",
    ),
    "UniversalDesignationFDE": (
        "Core/UniversalDesignationFDE.thy",
        "BuddhistComparativeLogic.Core.UniversalDesignationFDE",
    ),
    "HeartSutra_Sanskrit": (
        "Buddhist/HeartSutra/HeartSutra_Sanskrit.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.Sanskrit",
    ),
    "HeartSutra_PathModel": (
        "Buddhist/HeartSutra/HeartSutra_PathModel.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.PathModel",
    ),
    "HeartSutra_Anumana": (
        "Buddhist/HeartSutra/HeartSutra_Anumana.thy",
        "BuddhistComparativeLogic.Buddhist.Pramana.Anumana",
    ),
    "Madhyamaka_MMK1": (
        "Buddhist/Madhyamaka/Madhyamaka_MMK1.thy",
        "BuddhistComparativeLogic.Buddhist.Madhyamaka.MMK1",
    ),
    "FiniteDecisionProcedures": (
        "Core/FiniteDecisionProcedures.thy",
        "BuddhistComparativeLogic.Core.Decide",
    ),
    "Dharmakirti_Reasons": (
        "Buddhist/Pramana/Dharmakirti_Reasons.thy",
        "BuddhistComparativeLogic.Buddhist.Pramana.Dharmakirti",
    ),
    "Avyakata": (
        "Buddhist/EarlyBuddhism/Avyakata.thy",
        "BuddhistComparativeLogic.Buddhist.EarlyBuddhism.Avyakata",
    ),
    "Madhyamaka_StandpointSemantics": (
        "Buddhist/Madhyamaka/Madhyamaka_StandpointSemantics.thy",
        "BuddhistComparativeLogic.Buddhist.Madhyamaka.Standpoints",
    ),
    "Madhyamaka_Vigrahavyavartani": (
        "Buddhist/Madhyamaka/Madhyamaka_Vigrahavyavartani.thy",
        "BuddhistComparativeLogic.Buddhist.Madhyamaka.Vigraha",
    ),
    "FDEProofTheory": (
        "Core/FDEProofTheory.thy",
        "BuddhistComparativeLogic.Core.FDEProof",
    ),
    "HeartSutra_LongerRecension": (
        "Buddhist/HeartSutra/HeartSutra_LongerRecension.thy",
        "BuddhistComparativeLogic.Buddhist.HeartSutra.Longer",
    ),
    "Jaina_Saptabhangi": (
        "Comparative/Jaina/Jaina_Saptabhangi.thy",
        "BuddhistComparativeLogic.Comparative.Jaina.Saptabhangi",
    ),
    "Dignaga_Apoha": (
        "Buddhist/Pramana/Dignaga_Apoha.thy",
        "BuddhistComparativeLogic.Buddhist.Pramana.Apoha",
    ),
    "Yogacara_Vimsatika": (
        "Buddhist/Yogacara/Yogacara_Vimsatika.thy",
        "BuddhistComparativeLogic.Buddhist.Yogacara.Vimsatika",
    ),
    "Sarvastivada_ThreeTimes": (
        "Buddhist/Abhidharma/Sarvastivada_ThreeTimes.thy",
        "BuddhistComparativeLogic.Buddhist.Abhidharma.Sarvastivada",
    ),
    "Madhyamaka_Gamana": (
        "Buddhist/Madhyamaka/Madhyamaka_Gamana.thy",
        "BuddhistComparativeLogic.Buddhist.Madhyamaka.Gamana",
    ),
    "ManyValuedLogicExample": (
        "Core/ManyValuedLogicExample.thy",
        "BuddhistComparativeLogic.Core.MVExample",
    ),
}


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(LEAN).with_suffix("").parts)


def declared_names() -> set[str]:
    """Return every declaration name in the recursive Isabelle tree."""
    names: set[str] = set()
    for path in sorted(ISABELLE.rglob("*.thy")):
        names.update(DECL.findall(path.read_text(encoding="utf-8")))
    return names


def session_name() -> str:
    text = ROOT.read_text(encoding="utf-8")
    match = re.search(r"^\s*session\s+([A-Za-z][A-Za-z0-9_']*)\s*=", text, re.M)
    if not match:
        raise SystemExit("error: isabelle/ROOT has no session declaration")
    if match.group(1) != SESSION_NAME:
        raise SystemExit(
            f"error: expected Isabelle session {SESSION_NAME}, found {match.group(1)}"
        )
    return match.group(1)


def theory_order() -> list[str]:
    """Return theory names in the order isabelle/ROOT builds them."""
    text = ROOT.read_text(encoding="utf-8")
    if "theories" not in text or "document_files" not in text:
        raise SystemExit("error: isabelle/ROOT lacks theories or document_files")
    body = text.split("theories", 1)[1].split("document_files", 1)[0]
    theories: list[str] = []
    for line in body.splitlines():
        entry = line.strip()
        if not entry or entry.startswith("(*"):
            continue
        if entry.startswith('"') and entry.endswith('"'):
            entry = entry[1:-1]
        entry = entry.removesuffix(".thy")
        name = entry.rsplit("/", 1)[-1]
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", name):
            theories.append(name)
    if len(theories) != len(set(theories)):
        raise SystemExit("error: isabelle/ROOT contains duplicate theory entries")
    expected = set(PORTS)
    actual = set(theories)
    if actual != expected:
        raise SystemExit(
            "error: Isabelle port map and ROOT differ: "
            f"missing={sorted(expected - actual)}, extra={sorted(actual - expected)}"
        )
    return theories


def validate_port_paths() -> None:
    actual_paths = {
        path.relative_to(ISABELLE).as_posix()
        for path in ISABELLE.rglob("*.thy")
    }
    expected_paths = {isabelle_path for isabelle_path, _lean in PORTS.values()}
    if actual_paths != expected_paths:
        raise SystemExit(
            "error: Isabelle theory tree and port map differ: "
            f"missing={sorted(expected_paths - actual_paths)}, "
            f"extra={sorted(actual_paths - expected_paths)}"
        )


def lean_port(theories: list[str]) -> dict:
    mapping = [
        {"isabelle_theory": theory, "lean_module": PORTS[theory][1]}
        for theory in theories
    ]
    modules = sorted({entry["lean_module"] for entry in mapping})
    local_files = {
        module_name(path): path
        for path in sorted(LEAN.rglob("*.lean"))
    }
    missing = sorted(set(modules) - set(local_files))
    aggregate_name = "BuddhistComparativeLogic"
    if missing:
        raise SystemExit(
            "error: Lean port modules missing for ROOT theories: " + ", ".join(missing)
        )
    if aggregate_name not in local_files:
        raise SystemExit(
            "error: Lean aggregate module is missing: lean/BuddhistComparativeLogic.lean"
        )

    dependencies: dict[str, set[str]] = {}
    for name, path in local_files.items():
        source = erase_comments_and_strings(path.read_text(encoding="utf-8"))
        imports = {
            token
            for declaration in LEAN_IMPORT.findall(source)
            for token in declaration.split()
            if token in local_files
        }
        dependencies[name] = imports
    reachable: set[str] = set()
    pending = [aggregate_name]
    while pending:
        name = pending.pop()
        if name in reachable:
            continue
        reachable.add(name)
        pending.extend(dependencies.get(name, set()))
    outside_aggregate = sorted(set(modules) - reachable)
    if outside_aggregate:
        raise SystemExit(
            "error: lean/BuddhistComparativeLogic.lean does not import mapped modules: "
            + ", ".join(outside_aggregate)
        )
    return {
        "aggregate": local_files[aggregate_name].name,
        "theory_units": len(theories),
        "subject_modules": len(modules),
        "mapping": mapping,
    }


def cited(cell: str, declared: set[str]) -> list[str]:
    """Return identifiers in a table cell that an Isabelle theory declares."""
    out: list[str] = []
    for token in NAME.findall(cell):
        name = token if token in declared else token.rsplit(".", 1)[-1]
        if name in declared and name not in out:
            out.append(name)
    return out


def extensions(declared: set[str]) -> list[dict]:
    rows = EXT_ROW.findall(STATUS.read_text(encoding="utf-8"))
    return [
        {
            "theory": theory,
            "question": question,
            "theorems": cited(result, declared),
            "evidence_labels": [
                label.strip().replace("`", "")
                for label in labels.split(",")
                if label.strip()
            ],
        }
        for theory, question, result, labels in rows
    ]


def status_of() -> dict[str, str]:
    path = ISABELLE / "Buddhist" / "HeartSutra" / "HeartSutra_Coverage.thy"
    text = path.read_text(encoding="utf-8")
    return dict(re.findall(r"status_of (HS\d\d) = (\w+)", text))


def build() -> dict:
    validate_port_paths()
    session = session_name()
    status = status_of()
    declared = declared_names()
    rows = ROW.findall(STATUS.read_text(encoding="utf-8"))
    clauses = []
    for cid, text, count, counterpart, label, dependence, note in rows:
        clauses.append(
            {
                "id": cid,
                "text": text,
                "characters": int(count),
                "theorems": NAME.findall(counterpart),
                "evidence_label": label.replace("`", ""),
                "coverage_status": status.get(cid, "unknown"),
                "logic_dependence": dependence,
                "note": note,
            }
        )
    body = [clause for clause in clauses if clause["id"] not in ("HS00", "HS30")]
    extension_rows = extensions(declared)
    if len(clauses) != EXPECTED_CLAUSES:
        raise SystemExit(
            f"error: expected {EXPECTED_CLAUSES} clause rows, found {len(clauses)}"
        )
    body_characters = sum(clause["characters"] for clause in body)
    if body_characters != EXPECTED_BODY_CHARACTERS:
        raise SystemExit(
            "error: expected Heart Sutra body count "
            f"{EXPECTED_BODY_CHARACTERS}, found {body_characters}"
        )
    if len(extension_rows) != EXPECTED_EXTENSION_RESULTS:
        raise SystemExit(
            f"error: expected {EXPECTED_EXTENSION_RESULTS} extension rows, "
            f"found {len(extension_rows)}"
        )
    theories = theory_order()
    return {
        "schema": 3,
        "work": "Prajnaparamitahrdaya, Xuanzang's short recension (T251)",
        "isabelle_session": session,
        "theories": theories,
        "clauses": clauses,
        "body_clauses": len(body),
        "body_characters": body_characters,
        "extensions": extension_rows,
        "extension_results": len(extension_rows),
        "lean_port": lean_port(theories),
        "generated_by": "tools/make_index.py",
    }


def main() -> int:
    data = build()
    rendered = json.dumps(data, ensure_ascii=False, indent=2) + "\n"
    if "--check" in sys.argv:
        if not INDEX.exists():
            print("make_index.py: catalog/index.json is missing", file=sys.stderr)
            return 1
        if INDEX.read_text(encoding="utf-8") != rendered:
            print(
                "make_index.py: catalog/index.json is stale; "
                "run python3 tools/make_index.py",
                file=sys.stderr,
            )
            return 1
        print(
            f"make_index.py: catalog/index.json current "
            f"({data['body_clauses']} body clauses, "
            f"{data['body_characters']} characters, "
            f"{len(data['theories'])} theories, "
            f"{data['extension_results']} extension results)"
        )
        return 0
    INDEX.write_text(rendered, encoding="utf-8")
    print(
        f"make_index.py: wrote catalog/index.json ({len(data['clauses'])} clauses, "
        f"{data['extension_results']} extension results)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
