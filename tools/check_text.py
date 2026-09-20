#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Cross-check the formal clause counts and the adopted text witness.

The vendored witness is the project's explicitly documented received text,
not a critical edition.  This check keeps its exact bytes, checksum, clause
segmentation, Isabelle counts, Lean counts, STATUS table, and pinned external
comparison metadata from drifting independently.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]


def parse_thy_counts(path: Path) -> dict[str, int]:
    text = path.read_text(encoding="utf-8")
    m = re.search(r"fun char_count.*?where(.*?)\n\n", text, re.S)
    if not m:
        raise SystemExit(f"error: could not find char_count equations in {path}")
    pairs = re.findall(r'char_count (HS\d\d) = (\d+)', m.group(1))
    if len(pairs) != 31:
        raise SystemExit(f"error: expected 31 char_count equations, found {len(pairs)}")
    return {cid: int(n) for cid, n in pairs}


def parse_lean_counts(path: Path) -> dict[str, int]:
    text = path.read_text(encoding="utf-8")
    m = re.search(r"def char_count.*?(?=\n\n/--)", text, re.S)
    if not m:
        raise SystemExit(f"error: could not find char_count equations in {path}")
    pairs = re.findall(r"\|\s*(HS\d\d)\s*=>\s*(\d+)", m.group(0))
    if len(pairs) != 31:
        raise SystemExit(f"error: expected 31 Lean char_count equations, found {len(pairs)}")
    return {cid: int(n) for cid, n in pairs}


def parse_status_rows(path: Path) -> dict[str, tuple[str, int]]:
    text = path.read_text(encoding="utf-8")
    rows = re.findall(
        r"^\|\s*(HS\d\d)\s*\|\s*([^|]+?)\s*\|\s*(\d+)\s*\|",
        text,
        re.M,
    )
    if not rows:
        raise SystemExit(f"error: could not find a clause table in {path}")
    return {cid: (clause_text, int(n)) for cid, clause_text, n in rows}


def check_adopted_text(status_rows: dict[str, tuple[str, int]]) -> list[str]:
    problems: list[str] = []
    source_path = HERE / "sources" / "text" / "heart-sutra-t251-received-262.txt"
    digest_path = source_path.with_suffix(".sha256")
    manifest_path = HERE / "sources" / "manifest.json"

    raw = source_path.read_bytes()
    if raw.startswith(b"\xef\xbb\xbf"):
        problems.append(f"{source_path}: UTF-8 BOM is not permitted")
    if not raw.endswith(b"\n") or raw.endswith(b"\n\n"):
        problems.append(f"{source_path}: expected exactly one final LF")
    try:
        body = raw.decode("utf-8").removesuffix("\n")
    except UnicodeDecodeError as error:
        problems.append(f"{source_path}: invalid UTF-8: {error}")
        return problems
    if any(character.isspace() for character in body):
        problems.append(f"{source_path}: body must contain no whitespace")

    status_body = "".join(
        clause_text.replace(" ", "")
        for cid, (clause_text, _count) in sorted(status_rows.items())
        if cid not in {"HS00", "HS30"}
    )
    if body != status_body:
        problems.append(
            f"{source_path}: text does not equal the concatenated HS01--HS29 STATUS.md witness"
        )
    if len(body) != 262:
        problems.append(f"{source_path}: has {len(body)} codepoints, expected 262")

    digest = hashlib.sha256(raw).hexdigest()
    digest_line = digest_path.read_text(encoding="ascii").strip().split()
    if len(digest_line) != 2 or digest_line[1] != source_path.name:
        problems.append(f"{digest_path}: expected '<sha256>  {source_path.name}'")
    elif digest_line[0] != digest:
        problems.append(f"{digest_path}: digest does not match {source_path.name}")

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    witness = manifest.get("adopted_text_witness", {})
    if witness.get("sha256_including_final_lf") != digest:
        problems.append(f"{manifest_path}: recorded SHA-256 does not match the adopted text")
    if witness.get("body_codepoints_excluding_final_lf") != len(body):
        problems.append(f"{manifest_path}: recorded codepoint count does not match the adopted text")
    comparison = witness.get("external_comparison", {})
    commit = comparison.get("repository_commit", "")
    url = comparison.get("url", "")
    if not re.fullmatch(r"[0-9a-f]{40}", commit) or commit not in url:
        problems.append(f"{manifest_path}: external comparison URL must be pinned to its commit")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", comparison.get("accessed", "")):
        problems.append(f"{manifest_path}: external comparison needs an ISO access date")

    return problems


def main() -> int:
    thy_counts = parse_thy_counts(
        HERE / "isabelle" / "Buddhist" / "HeartSutra" / "HeartSutra_Text.thy"
    )
    lean_counts = parse_lean_counts(
        HERE
        / "lean"
        / "BuddhistComparativeLogic"
        / "Buddhist"
        / "HeartSutra"
        / "Text.lean"
    )
    status_rows = parse_status_rows(HERE / "docs" / "STATUS.md")
    status_counts = {cid: count for cid, (_text, count) in status_rows.items()}

    missing_in_status = sorted(set(thy_counts) - set(status_counts))
    missing_in_thy = sorted(set(status_counts) - set(thy_counts))
    if missing_in_status:
        print(f"error: clauses in HeartSutra_Text.thy but not in STATUS.md: {missing_in_status}", file=sys.stderr)
        return 1
    if missing_in_thy:
        print(f"error: clauses in STATUS.md but not in HeartSutra_Text.thy: {missing_in_thy}", file=sys.stderr)
        return 1

    mismatches = [
        (cid, thy_counts[cid], status_counts[cid])
        for cid in sorted(thy_counts)
        if thy_counts[cid] != status_counts[cid]
    ]
    if mismatches:
        print("error: char_count mismatches between HeartSutra_Text.thy and STATUS.md:", file=sys.stderr)
        for cid, thy_n, status_n in mismatches:
            print(f"  {cid}: HeartSutra_Text.thy={thy_n} STATUS.md={status_n}", file=sys.stderr)
        return 1

    lean_mismatches = [
        (cid, thy_counts[cid], lean_counts.get(cid))
        for cid in sorted(thy_counts)
        if lean_counts.get(cid) != thy_counts[cid]
    ]
    if lean_mismatches:
        print("error: char_count mismatches between Isabelle and Lean:", file=sys.stderr)
        for cid, thy_n, lean_n in lean_mismatches:
            print(f"  {cid}: Isabelle={thy_n} Lean={lean_n}", file=sys.stderr)
        return 1

    text_length_mismatches = [
        (cid, count, len(clause_text.replace(" ", "")))
        for cid, (clause_text, count) in sorted(status_rows.items())
        if len(clause_text.replace(" ", "")) != count
    ]
    if text_length_mismatches:
        print("error: STATUS.md clause text/count mismatches:", file=sys.stderr)
        for cid, declared, actual in text_length_mismatches:
            print(f"  {cid}: declared={declared} actual={actual}", file=sys.stderr)
        return 1

    body_total = sum(n for cid, n in thy_counts.items() if cid not in {"HS00", "HS30"})
    if body_total != 262:
        print(f"error: body character total is {body_total}, expected 262", file=sys.stderr)
        return 1

    source_problems = check_adopted_text(status_rows)
    if source_problems:
        print("error: adopted text witness failed validation:", file=sys.stderr)
        for problem in source_problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    print(
        f"check_text.py: {len(thy_counts)} Isabelle/Lean/STATUS clauses agree, "
        f"adopted text and SHA-256 agree, body total = {body_total}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
