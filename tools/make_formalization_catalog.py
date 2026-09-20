#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Build the machine-readable and human-readable Lean module catalogues.

Historical/source judgments live in catalog/catalog_annotations.json. Mechanical
facts (imports, declaration names, counts, and source hashes) are regenerated
from the Lean files.  `--check` fails if either generated file is stale.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path

from check_lean import erase_comments_and_strings

HERE = Path(__file__).resolve().parents[1]
LEAN = HERE / "lean"
ANNOTATIONS = HERE / "catalog" / "catalog_annotations.json"
JSON_OUTPUT = HERE / "catalog" / "formalizations.json"
MARKDOWN_OUTPUT = HERE / "catalog" / "FORMALIZATION_CATALOG.md"

IMPORT = re.compile(r"^import\s+([A-Za-z][A-Za-z0-9_.']*)\s*$", re.M)
RESULT = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z][A-Za-z0-9_']*)", re.M)
DEFINITION = re.compile(
    r"^(?:def|abbrev|inductive|structure|class)\s+([A-Za-z][A-Za-z0-9_']*)",
    re.M,
)
EXAMPLE = re.compile(r"^example\b", re.M)


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(LEAN).with_suffix("").parts)


def module_header(text: str, path: Path) -> tuple[str, str]:
    match = re.search(r"/-!\s*(.*?)\s*-/", text, re.S)
    if not match:
        raise ValueError(f"{path}: missing module documentation block")
    body = match.group(1).strip()
    title_match = re.search(r"^#\s+(.+?)\s*$", body, re.M)
    if not title_match:
        raise ValueError(f"{path}: module documentation has no level-one title")
    title = title_match.group(1).strip()
    remainder = body[title_match.end() :].strip()
    paragraphs = [p.strip() for p in re.split(r"\n\s*\n", remainder) if p.strip()]
    summary = ""
    for paragraph in paragraphs:
        if paragraph.startswith("#"):
            continue
        summary = " ".join(line.strip() for line in paragraph.splitlines())
        break
    if not summary:
        raise ValueError(f"{path}: module documentation has no summary paragraph")
    return title, summary


def build_catalog() -> dict:
    annotation_doc = json.loads(ANNOTATIONS.read_text(encoding="utf-8"))
    annotation_items = annotation_doc["modules"]
    annotation_names = [item["module"] for item in annotation_items]
    duplicate_annotations = sorted(
        name for name, count in Counter(annotation_names).items() if count > 1
    )
    if duplicate_annotations:
        raise ValueError(
            "duplicate catalog annotations: " + ", ".join(duplicate_annotations)
        )
    annotations = {item["module"]: item for item in annotation_items}
    paths = sorted(LEAN.rglob("*.lean"))
    present = {module_name(path) for path in paths}
    if set(annotations) != present:
        missing = sorted(present - set(annotations))
        extra = sorted(set(annotations) - present)
        raise ValueError(f"catalog annotation coverage mismatch: missing={missing}, extra={extra}")

    source_doc = json.loads((HERE / "sources" / "registry.json").read_text(encoding="utf-8"))
    source_names = [source["id"] for source in source_doc["sources"]]
    duplicate_sources = sorted(
        name for name, count in Counter(source_names).items() if count > 1
    )
    if duplicate_sources:
        raise ValueError("duplicate source ids: " + ", ".join(duplicate_sources))
    source_ids = set(source_names)
    records = []
    for path in paths:
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        title, summary = module_header(text, path)
        code = erase_comments_and_strings(text)
        module = module_name(path)
        annotation = annotations[module]
        protected_fields = {
            "path",
            "sha256",
            "title",
            "formal_scope",
            "imports",
            "public_results",
            "declaration_counts",
        }
        overwritten = sorted(protected_fields & set(annotation))
        if overwritten:
            raise ValueError(
                f"{path.name}: annotation overrides generated fields {overwritten}"
            )
        cited_sources = annotation["primary_sources"] + annotation["secondary_or_formal_sources"]
        unknown_sources = sorted(set(cited_sources) - source_ids)
        if unknown_sources:
            raise ValueError(f"{path.name}: unknown source ids {unknown_sources}")
        results = RESULT.findall(code)
        definitions = DEFINITION.findall(code)
        record = {
            "module": module,
            "path": path.relative_to(HERE).as_posix(),
            "sha256": hashlib.sha256(raw).hexdigest(),
            "title": title,
            "formal_scope": summary,
            "imports": IMPORT.findall(code),
            "public_results": results,
            "declaration_counts": {
                "definitions_and_types": len(definitions),
                "theorems_and_lemmas": len(results),
                "examples": len(EXAMPLE.findall(code)),
            },
            **annotation,
        }
        records.append(record)

    ordinary = [record for record in records if record["family"] != "Aggregates"]
    aggregates = [record for record in records if record["family"] == "Aggregates"]

    def historical_counts(items: list[dict]) -> dict:
        return dict(sorted(Counter(item["historical_status"] for item in items).items()))

    return {
        "schema": 1,
        "project": "Buddhist and Comparative Asian Logic Formalizations",
        "lean_toolchain": (HERE / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "generation": {
            "script": "tools/make_formalization_catalog.py",
            "annotations": "catalog/catalog_annotations.json",
            "source_registry": "sources/registry.json",
            "deterministic": True,
        },
        "summary": {
            "modules": len(records),
            "families": dict(sorted(Counter(record["family"] for record in records).items())),
            "release_statuses": dict(
                sorted(Counter(record["release_status"] for record in records).items())
            ),
            "historical_statuses": dict(
                sorted(Counter(record["historical_status"] for record in records).items())
            ),
            "ordinary_modules": len(ordinary),
            "aggregate_modules": len(aggregates),
            "ordinary_historical_statuses": historical_counts(ordinary),
            "aggregate_historical_statuses": historical_counts(aggregates),
            "declaration_counts": {
                key: sum(record["declaration_counts"][key] for record in records)
                for key in ("definitions_and_types", "theorems_and_lemmas", "examples")
            },
        },
        "modules": records,
    }


def markdown(catalog: dict) -> str:
    lines = [
        "<!-- SPDX-License-Identifier: CC0-1.0 -->",
        "",
        "# Formalization catalogue",
        "",
        "This generated catalogue gives every Lean module a public boundary: its target,",
        "formal scope, explicit-assumption policy, historical-source status, and release",
        "status.  Mechanical facts come from the source files; interpretive judgments",
        "come from `catalog/catalog_annotations.json`.  Regenerate with",
        "`python3 tools/make_formalization_catalog.py`.",
        "",
        "The labels are deliberately conservative:",
        "",
        "- `passage_aligned` identifies a passage or adopted witness, but does not imply",
        "  that the cited edition or interpretation is uncontested;",
        "- `work_level` names a work or argument family without a theorem-to-passage map;",
        "- `unverified` records missing passage-level evidence and is never filled by guesswork;",
        "- `not_applicable` is used for pure logic and import infrastructure.",
        "",
        "Source IDs resolve in [`sources/registry.json`](../sources/registry.json).  The",
        "software-release boundary is explained in",
        "[`RELEASE_SCOPE.md`](../docs/RELEASE_SCOPE.md).  Exact theorem statements remain in the",
        "linked Lean files; the catalogue records their names and counts in",
        "[`formalizations.json`](formalizations.json).",
        "",
    ]
    lines.extend([
        "## Inventory populations", "",
        "Historical-source statuses are counted separately for ordinary modules and",
        "aggregate import files; they are not a common denominator of subject coverage.", "",
        "| Population | Total | Passage-aligned | Work-level | Not applicable |",
        "| --- | ---: | ---: | ---: | ---: |",
    ])
    for label, prefix in (("Ordinary modules", "ordinary"), ("Aggregate imports", "aggregate")):
        counts = catalog["summary"][f"{prefix}_historical_statuses"]
        lines.append(f"| {label} | {catalog['summary'][f'{prefix}_modules']} | "
                     f"{counts.get('passage_aligned', 0)} | {counts.get('work_level', 0)} | "
                     f"{counts.get('not_applicable', 0)} |")
    lines.extend(["", "The declaration totals are lexical counts, not measures of mathematical depth.", ""])
    preferred = [
        "Aggregates",
        "Logic/Core",
        "Heart Sutra",
        "Madhyamaka",
        "Pramana",
        "Yogacara",
        "Comparative",
    ]
    present_families = {record["family"] for record in catalog["modules"]}
    families = [family for family in preferred if family in present_families]
    families.extend(sorted(present_families - set(families)))
    records_by_family = {
        family: [record for record in catalog["modules"] if record["family"] == family]
        for family in families
    }
    for family in families:
        records = records_by_family[family]
        lines.extend([f"## {family} ({len(records)})", ""])
        for record in records:
            primary = ", ".join(f"`{source}`" for source in record["primary_sources"]) or "none registered"
            secondary = ", ".join(
                f"`{source}`" for source in record["secondary_or_formal_sources"]
            ) or "none registered"
            docs = ", ".join(f"[{doc}](../{doc})" for doc in record["documentation"])
            theories = ", ".join(f"`{name}`" for name in record["isabelle_theories"]) or "none"
            counts = record["declaration_counts"]
            lines.extend(
                [
                    f"### [`{record['module']}`](../{record['path']})",
                    "",
                    f"- **Target:** {record['title']}",
                    f"- **Formal scope:** {record['formal_scope']}",
                    f"- **Assumption boundary:** {record['assumption_boundary']}",
                    f"- **Checked inventory:** {counts['definitions_and_types']} definitions/types, "
                    f"{counts['theorems_and_lemmas']} theorems/lemmas, {counts['examples']} examples; "
                    f"imports {len(record['imports'])} direct module(s).",
                    f"- **Provenance:** `{record['provenance']}`; Isabelle theory units: {theories}.",
                    f"- **Historical status:** `{record['historical_status']}`; primary: {primary}; "
                    f"secondary/formal: {secondary}. {record['source_note']}",
                    f"- **Limit:** {record['claim_limit']}",
                    f"- **Release:** `{record['release_status']}`. Documentation: {docs}.",
                    "",
                ]
            )
    return "\n".join(lines).rstrip() + "\n"


def write_or_check(path: Path, expected: str, check: bool) -> bool:
    if check:
        actual = path.read_text(encoding="utf-8") if path.exists() else None
        if actual != expected:
            print(
                f"error: {path.relative_to(HERE)} is stale; "
                "run python3 tools/make_formalization_catalog.py",
                file=sys.stderr,
            )
            return False
        return True
    path.write_text(expected, encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail rather than rewrite stale outputs")
    args = parser.parse_args()
    try:
        catalog = build_catalog()
        json_text = json.dumps(catalog, ensure_ascii=False, indent=2) + "\n"
        markdown_text = markdown(catalog)
        ok = write_or_check(JSON_OUTPUT, json_text, args.check)
        ok = write_or_check(MARKDOWN_OUTPUT, markdown_text, args.check) and ok
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    if not ok:
        return 1
    action = "current" if args.check else "wrote"
    print(f"make_formalization_catalog.py: {action}; {catalog['summary']['modules']} Lean modules")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
