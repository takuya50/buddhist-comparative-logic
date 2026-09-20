#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Guard the documentation against drift from the theories.

Three checks, all of which the build runs:

1. every Isabelle/Lean-looking identifier quoted in the maintained prose is
   actually declared somewhere in isabelle/ (or lean/, for the port's names), and
   every Isabelle result cited in README.md or STATUS.md has a same-named Lean
   theorem or lemma;
2. the theory list in isabelle/ROOT and the recursive theory tree agree;
3. every locale has a model witness, so that no theorem proved inside a
   locale can be vacuously true. A witness is an `interpretation`, a
   `sublocale` whose target it is, or a lemma whose statement begins with
   the locale name (by convention `..._nonvacuous` or `..._consistent`).

A fourth, cheaper check: `oops` may only close a Nitpick regression.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from check_lean import erase_comments_and_strings

HERE = Path(__file__).resolve().parents[1]
ISABELLE = HERE / "isabelle"
THY = sorted(ISABELLE.rglob("*.thy"))
LEAN = sorted((HERE / "lean").rglob("*.lean"))
EXPECTED_ISABELLE_THEORIES = 35
DOCS = [
    HERE / "docs" / "STATUS.md",
    HERE / "README.md",
    HERE / "docs" / "REUSE.md",
    HERE / "docs" / "PORTING.md",
    HERE / "docs" / "LEAN_PROGRESS.md",
    HERE / "docs" / "ARGUMENTS.md",
    HERE / "docs" / "CATUSKOTI_K3_FDE.md",
    HERE / "docs" / "COMPARATIVE_LOGIC.md",
    HERE / "docs" / "PRAMANA_TREATISES.md",
    HERE / "docs" / "INFERENCE_DEBATE.md",
    HERE / "docs" / "OPEN_PROBLEMS.md",
    HERE / "docs" / "PRAMANA_YOGACARA.md",
    HERE / "docs" / "PUBLISHING.md",
]

# Backticked tokens that are prose or tooling, not Isabelle names.
ALLOW = {
    "build_sh", "check_text", "check_names", "check_lean", "verify_sh",
    "document_build", "document_output", "isabelle_theorem", "lean_toolchain",
    "install_isabelle", "root_tex", "root_bib", "make_index", "index_json",
    # Isabelle and Lean syntax quoted as syntax, not as names of this development
    "global_interpretation", "smt_oracle", "type_synonym", "unfold_locales",
}

DECL = re.compile(
    r"^\s*(?:theorem|lemma|corollary|definition|fun|abbreviation|locale|datatype"
    r"|primrec|inductive|lemmas|type_synonym|schematic_goal)\s+([A-Za-z][A-Za-z0-9_']*)",
    re.M,
)
NAMED = re.compile(r"^\s*(?:assumes|and|fixes|shows|obtains)\s+([a-z][A-Za-z0-9_']*)\s*:", re.M)
CONSTR = re.compile(r"^\s*[|]\s*([A-Za-z][A-Za-z0-9_']*)", re.M)
LEANDECL = re.compile(
    r"^\s*(?:@\[[^\n]*\]\s*)*"
    r"(?:theorem|lemma|def|abbrev|inductive|structure|class|instance)"
    r"\s+([A-Za-z][A-Za-z0-9_']*)",
    re.M,
)
RESULT_DECL = re.compile(
    r"^\s*(?:theorem|lemma|corollary)\s+([A-Za-z][A-Za-z0-9_']*)", re.M
)
LEAN_RESULT_DECL = re.compile(
    r"^\s*(?:@\[[^\n]*\]\s*)*(?:theorem|lemma)"
    r"\s+([A-Za-z][A-Za-z0-9_']*)", re.M
)
LOCALE = re.compile(r"^locale\s+([A-Za-z][A-Za-z0-9_']*)", re.M)
# Isabelle theory headers are unindented. Requiring column zero avoids prose
# lines such as "  theory adds ..." inside cartouches.
THEORY_DECL = re.compile(r"^theory[ \t]+([A-Za-z][A-Za-z0-9_']*)", re.M)
TOKEN = re.compile(r"`([^`\n]+)`")

SKIP_SUFFIX = (".thy", ".py", ".sh", ".lean", ".md", ".tex", ".bib", ".pdf", ".json")


def declared_names() -> set[str]:
    names: set[str] = set()
    root = (ISABELLE / "ROOT").read_text(encoding="utf-8")
    names.update(
        re.findall(r"^session[ \t]+([A-Za-z][A-Za-z0-9_']*)[ \t]*=", root, re.M)
    )
    for path in THY:
        text = path.read_text(encoding="utf-8")
        names |= set(DECL.findall(text))
        names |= set(NAMED.findall(text))
        names |= set(CONSTR.findall(text))
        names.add(path.stem)
    for path in LEAN:
        text = erase_comments_and_strings(path.read_text(encoding="utf-8"))
        names |= set(LEANDECL.findall(text))
        names.add(path.stem)
    return names


def quoted_identifiers(path: Path) -> list[tuple[int, str]]:
    out: list[tuple[int, str]] = []
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        for raw in TOKEN.findall(line):
            tok = raw.strip()
            if "/" in tok or " " in tok or tok.endswith(SKIP_SUFFIX):
                continue
            tok = tok.split(".")[-1]
            if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", tok):
                continue
            if "_" not in tok or tok in ALLOW:
                continue
            out.append((lineno, tok))
    return out


def check_docs(names: set[str]) -> list[str]:
    problems = []
    for doc in DOCS:
        for lineno, tok in quoted_identifiers(doc):
            if tok not in names:
                problems.append(f"{doc.name}:{lineno}: unknown identifier `{tok}`")
    return problems


def check_headline_lean_counterparts() -> tuple[list[str], int]:
    """Require cited Isabelle results to remain visible in the Lean port."""
    isabelle_results = {
        name
        for path in THY
        for name in RESULT_DECL.findall(path.read_text(encoding="utf-8"))
    }
    lean_results = {
        name
        for path in LEAN
        for name in LEAN_RESULT_DECL.findall(
            erase_comments_and_strings(path.read_text(encoding="utf-8"))
        )
    }
    problems: list[str] = []
    cited_results: set[str] = set()
    for doc in (HERE / "README.md", HERE / "docs" / "STATUS.md"):
        for lineno, token in quoted_identifiers(doc):
            if token in isabelle_results:
                cited_results.add(token)
                if token not in lean_results:
                    problems.append(
                        f"{doc.name}:{lineno}: cited Isabelle result `{token}` "
                        "has no same-named Lean theorem or lemma"
                    )
    return problems, len(cited_results)


def check_root() -> list[str]:
    root_path = ISABELLE / "ROOT"
    root = root_path.read_text(encoding="utf-8")
    try:
        body = root.split("theories", 1)[1].split("document_files", 1)[0]
    except IndexError:
        return ["isabelle/ROOT has no theories/document_files section"]

    listed_order: list[str] = []
    for line in body.splitlines():
        entry = line.strip()
        if not entry or entry.startswith("(*"):
            continue
        if entry.startswith('"') and entry.endswith('"'):
            entry = entry[1:-1]
        entry = entry.removesuffix(".thy")
        name = entry.rsplit("/", 1)[-1]
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", name):
            listed_order.append(name)

    listed = set(listed_order)
    present = {path.stem for path in THY}
    problems: list[str] = []
    duplicates = sorted(
        name for name in listed if listed_order.count(name) > 1
    )
    if duplicates:
        problems.append("isabelle/ROOT lists duplicate theories: " + ", ".join(duplicates))
    if len(THY) != EXPECTED_ISABELLE_THEORIES:
        problems.append(
            "unexpected Isabelle theory count: "
            f"expected {EXPECTED_ISABELLE_THEORIES}, found {len(THY)}"
        )
    for missing in sorted(listed - present):
        problems.append(f"ROOT lists {missing}, but no matching Isabelle theory exists")
    for extra in sorted(present - listed):
        problems.append(f"Isabelle theory {extra} exists, but ROOT does not list it")
    for path in THY:
        declarations = THEORY_DECL.findall(path.read_text(encoding="utf-8"))
        rel = path.relative_to(HERE).as_posix()
        if declarations != [path.stem]:
            problems.append(
                f"{rel}: expected theory declaration {path.stem}, found {declarations}"
            )
    return problems


def check_locales() -> list[str]:
    corpus = "\n".join(p.read_text(encoding="utf-8") for p in THY)
    problems = []
    for path in THY:
        for loc in LOCALE.findall(path.read_text(encoding="utf-8")):
            witness = (
                re.search(rf"^interpretation\s+([A-Za-z][A-Za-z0-9_']*:\s*)?{loc}\b", corpus, re.M)
                or re.search(rf"sublocale\s+[^\n]*?[⊆]\s*([A-Za-z][A-Za-z0-9_']*:\s*)?{loc}\b", corpus)
                or re.search(rf"sublocale\s+[^\n]*?\\<subseteq>\s*([A-Za-z][A-Za-z0-9_']*:\s*)?{loc}\b", corpus)
                or re.search(rf"^(?:lemma|theorem)\s+[A-Za-z][A-Za-z0-9_']*:\s*\n?\s*\"{loc}\s", corpus, re.M)
            )
            if not witness:
                problems.append(
                    f"locale {loc} ({path.name}) has no model witness: add an interpretation "
                    f"or a lemma \"{loc} ...\" named {loc}_nonvacuous"
                )
    return problems


def check_oops() -> list[str]:
    problems = []
    for path in THY:
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if re.match(r"\s*oops\s*$", line):
                window = "\n".join(lines[max(0, i - 6) : i])
                if "nitpick" not in window:
                    problems.append(f"{path.name}:{i + 1}: oops outside a Nitpick regression")
    return problems


def main() -> int:
    names = declared_names()
    lean_problems, cited_results = check_headline_lean_counterparts()
    problems = (
        check_docs(names)
        + lean_problems
        + check_root()
        + check_locales()
        + check_oops()
    )
    if problems:
        print("check_names.py: failed", file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1
    locales = sum(len(LOCALE.findall(p.read_text(encoding="utf-8"))) for p in THY)
    print(
        f"check_names.py: {len(THY)} theories, {locales} locales all with model witnesses, "
        f"documentation identifiers resolve, {cited_results} cited results have Lean counterparts"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
