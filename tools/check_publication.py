#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check that this repository is a self-contained software-release candidate.

The checks resolve all paths from this file's repository root and do not depend
on Git metadata.
"""

from __future__ import annotations

import ast
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from urllib.parse import unquote, urlsplit

from check_lean import erase_comments_and_strings

HERE = Path(__file__).resolve().parents[1]

CORE_FILES = (
    ".gitignore",
    ".github/workflows/verify.yml",
    "ci/verify.yml",
    "README.md",
    "docs/STATUS.md",
    "docs/PUBLISHING.md",
    "docs/RELEASE_SCOPE.md",
    "catalog/FORMALIZATION_CATALOG.md",
    "docs/SOURCES.md",
    "CITATION.cff",
    "LICENSE",
    "LICENSE-CC0",
    "docs/LICENSE_SCOPE.md",
    "LICENSES/Apache-2.0.txt",
    "LICENSES/CC0-1.0.txt",
    "REUSE.toml",
    "isabelle/ROOT",
    "isabelle/document/root.tex",
    "isabelle/document/root.bib",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "verify.sh",
    "tools/build.sh",
    "tools/check-lean.sh",
    "tools/check_lean.py",
    "tools/check_names.py",
    "tools/check_text.py",
    "tools/check_publication.py",
    "tools/check_audits.py",
    "tools/check_license.py",
    "tools/compare_cbeta_witness.py",
    "tools/make_snapshot.py",
    "docs/AUDITS.md",
    "verification/representative_axioms.lean",
    "verification/Representative_Oracles.thy",
    "tools/make_index.py",
    "tools/make_formalization_catalog.py",
    "catalog/index.json",
    "catalog/catalog_annotations.json",
    "catalog/formalizations.json",
    "sources/manifest.json",
    "sources/registry.json",
    "sources/text/heart-sutra-t251-received-262.txt",
    "sources/text/heart-sutra-t251-received-262.sha256",
    "lean/BuddhistComparativeLogic.lean",
    "lean/BuddhistComparativeLogic/Release.lean",
    "lean/BuddhistComparativeLogic/Experimental.lean",
    "isabelle/Buddhist/HeartSutra/HeartSutra_Text.thy",
)

TEXT_SUFFIXES = {
    ".bib",
    ".cff",
    ".gitignore",
    ".json",
    ".lean",
    ".md",
    ".py",
    ".sha256",
    ".sh",
    ".tex",
    ".thy",
    ".toml",
    ".txt",
    ".yaml",
    ".yml",
}
TEXT_NAMES = {".gitignore", "LICENSE", "LICENSE-CC0", "ROOT", "lean-toolchain"}
SKIP_DIRS = {
    ".git", ".lake", "__pycache__", "output", "outputs", "dist", "tmp", "temp",
    ".cache", ".pytest_cache", ".mypy_cache", ".ruff_cache", ".venv", "venv",
    ".idea", ".vscode", ".direnv",
}

MARKDOWN_LINK = re.compile(r"!?\[[^\]\n]*\]\(([^)\n]+)\)")
INLINE_CODE = re.compile(r"(`+)(.*?)\1")
CONFLICT_MARKER = re.compile(r"^(?:<{7}(?: .*)?|={7}|>{7}(?: .*)?)$")
LOCAL_HOME = re.compile(
    r"(?<![A-Za-z0-9_])/(?:Users|home|root)/[^\s`'\"<>]*"
    r"|(?i:[A-Z]:[\\/]Users[\\/][^\s`'\"<>]*)"
    r"|\bfile:" r"//(?:localhost)?/"
)
SECRET_PATTERNS = (
    ("private key", re.compile(r"-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----")),
    ("GitHub token", re.compile(r"\b(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{40,})\b")),
    ("AWS access key", re.compile(r"\b(?:AKIA|ASIA)[A-Z0-9]{16}\b")),
    ("OpenAI-style secret key", re.compile(r"\bsk-[A-Za-z0-9_-]{32,}\b")),
)
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)

AGGREGATES = {
    "BuddhistComparativeLogic",
    "BuddhistComparativeLogic.Release",
    "BuddhistComparativeLogic.Experimental",
}
EXPECTED_ORDINARY_MODULES = 112
EXPECTED_RELEASE_MODULES = 110
EXPECTED_EXPERIMENTAL_MODULES = 2
EXPECTED_EXPERIMENTAL_SET = {
    "BuddhistComparativeLogic.Comparative.Vedanta.Sriharsa",
    "BuddhistComparativeLogic.Buddhist.KoreanBuddhism.WonhyoHwajaeng",
}


def lean_module_name(path: Path, lean_dir: Path) -> str:
    return ".".join(path.relative_to(lean_dir).with_suffix("").parts)


def relative(path: Path) -> str:
    return path.relative_to(HERE).as_posix()


def check_core_files(errors: list[str]) -> None:
    for name in CORE_FILES:
        if not (HERE / name).is_file():
            errors.append(f"missing standalone file: {name}")
    for name in ("lean", "isabelle", "docs", "catalog", "tools", "sources"):
        if not (HERE / name).is_dir():
            errors.append(f"missing standalone directory: {name}/")
    for name in ("thy", "document"):
        if (HERE / name).exists():
            errors.append(f"obsolete pre-reorganization path remains: {name}/")


def check_software_scope(errors: list[str]) -> None:
    """Keep manuscript artifacts out of the software deposit and Git history."""
    forbidden_names = {"figshare_metadata.md", "licenseref-paper-draft-no-license.txt"}
    for path in HERE.rglob("*"):
        rel = path.relative_to(HERE)
        if any(part in SKIP_DIRS for part in rel.parts):
            continue
        if rel.parts[0].lower() == "paper":
            errors.append("paper/ is outside the software-release scope")
            break
    for path in HERE.rglob("*"):
        rel = path.relative_to(HERE)
        if not path.is_file() or any(part in SKIP_DIRS for part in rel.parts):
            continue
        name = path.name.lower()
        if (name in forbidden_names or name.startswith("manuscript")
                or name.startswith("buddhist_comparative_asian_logic_formalizations")):
            errors.append(f"manuscript artifact is outside software scope: {rel.as_posix()}")


def relevant_text_files() -> list[Path]:
    paths: list[Path] = []
    for path in HERE.rglob("*"):
        if not path.is_file() or any(part in SKIP_DIRS for part in path.relative_to(HERE).parts):
            continue
        if path.name in TEXT_NAMES or path.suffix.lower() in TEXT_SUFFIXES:
            paths.append(path)
    return sorted(paths)


def scan_text_files(errors: list[str]) -> int:
    placeholder = "TODO" + "-at-publication"
    paths = relevant_text_files()
    for path in paths:
        try:
            raw = path.read_bytes()
            text = raw.decode("utf-8")
        except UnicodeDecodeError as error:
            errors.append(f"{relative(path)}: invalid UTF-8: {error}")
            continue
        if raw and not raw.endswith(b"\n"):
            errors.append(f"{relative(path)}: missing final newline")
        for lineno, line in enumerate(text.splitlines(), 1):
            if line.endswith((" ", "\t")):
                errors.append(f"{relative(path)}:{lineno}: trailing whitespace")
            if CONFLICT_MARKER.fullmatch(line):
                errors.append(f"{relative(path)}:{lineno}: merge-conflict marker")
            match = LOCAL_HOME.search(line)
            if match:
                errors.append(
                    f"{relative(path)}:{lineno}: local machine path {match.group(0)!r}"
                )
            if placeholder in line:
                errors.append(f"{relative(path)}:{lineno}: unresolved publication placeholder")
            for label, pattern in SECRET_PATTERNS:
                if pattern.search(line):
                    errors.append(f"{relative(path)}:{lineno}: possible {label}")
    return len(paths)


def markdown_prose(source: str, path: Path, errors: list[str]) -> str:
    output: list[str] = []
    fence: str | None = None
    for line in source.splitlines(keepends=True):
        match = re.match(r"^\s*(`{3,}|~{3,})", line)
        marker = match.group(1) if match else None
        if fence is not None:
            output.append("\n" if line.endswith("\n") else "")
            if marker is not None and marker[0] == fence[0] and len(marker) >= len(fence):
                fence = None
            continue
        if marker is not None:
            fence = marker
            output.append("\n" if line.endswith("\n") else "")
            continue
        output.append(INLINE_CODE.sub("", line))
    if fence is not None:
        errors.append(f"{relative(path)}: unterminated Markdown code fence")
    return "".join(output)


def link_destination(raw: str) -> str:
    target = raw.strip()
    if target.startswith("<"):
        closing = target.find(">")
        return target[1:closing] if closing >= 0 else target
    return target.split(None, 1)[0]


def check_markdown_links(errors: list[str]) -> int:
    checked = 0
    for document in sorted(HERE.rglob("*.md")):
        if any(part in SKIP_DIRS for part in document.relative_to(HERE).parts):
            continue
        prose = markdown_prose(document.read_text(encoding="utf-8"), document, errors)
        for match in MARKDOWN_LINK.finditer(prose):
            target = link_destination(match.group(1))
            if not target or target.startswith("#"):
                continue
            parsed = urlsplit(target)
            if parsed.scheme or parsed.netloc or target.startswith("//"):
                if parsed.scheme == "file":
                    errors.append(f"{relative(document)}: local file URI is not portable: {target}")
                continue
            local = unquote(target.split("#", 1)[0].split("?", 1)[0])
            if not local:
                continue
            checked += 1
            candidate = Path(local)
            if candidate.is_absolute():
                errors.append(f"{relative(document)}: absolute Markdown link: {target}")
                continue
            resolved = (document.parent / candidate).resolve()
            try:
                resolved.relative_to(HERE)
            except ValueError:
                errors.append(f"{relative(document)}: Markdown link leaves project: {target}")
                continue
            if not resolved.exists():
                errors.append(f"{relative(document)}: broken local Markdown link: {target}")
    return checked


def check_versions(errors: list[str]) -> str | None:
    lake_path = HERE / "lakefile.toml"
    cff_path = HERE / "CITATION.cff"
    if not lake_path.is_file() or not cff_path.is_file():
        return None
    lake_text = lake_path.read_text(encoding="utf-8")
    cff_text = cff_path.read_text(encoding="utf-8")
    lake_versions = re.findall(r'^version\s*=\s*["\']([^"\']+)["\']\s*$', lake_text, re.M)
    cff_versions = re.findall(r'^version:\s*["\']?([^\s"\']+)["\']?\s*$', cff_text, re.M)
    if len(lake_versions) != 1:
        errors.append("lakefile.toml: expected exactly one package version")
        return None
    if len(cff_versions) != 1:
        errors.append("CITATION.cff: expected exactly one version")
        return lake_versions[0]
    if lake_versions[0] != cff_versions[0]:
        errors.append(
            "version mismatch: lakefile.toml="
            f"{lake_versions[0]!r}, CITATION.cff={cff_versions[0]!r}"
        )
    return lake_versions[0]


def parse_simple_reuse_toml(text: str) -> dict:
    """Parse the small TOML subset used by REUSE.toml without dependencies."""
    data: dict = {}
    current = data
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        line = lines[index].strip()
        index += 1
        if not line or line.startswith("#"):
            continue
        if line == "[[annotations]]":
            annotations = data.setdefault("annotations", [])
            if not isinstance(annotations, list):
                raise ValueError("annotations is not an array of tables")
            current = {}
            annotations.append(current)
            continue
        if "=" not in line:
            raise ValueError(f"line {index}: expected key = value")
        key, value = (part.strip() for part in line.split("=", 1))
        if not re.fullmatch(r"[A-Za-z0-9_-]+", key) or key in current:
            raise ValueError(f"line {index}: invalid or duplicate key {key!r}")
        if value.startswith("["):
            while not value.rstrip().endswith("]"):
                if index >= len(lines):
                    raise ValueError(f"line {index}: unterminated array")
                value += "\n" + lines[index]
                index += 1
        try:
            parsed = ast.literal_eval(value)
        except (SyntaxError, ValueError) as error:
            raise ValueError(f"line {index}: unsupported or invalid value for {key}") from error
        if not isinstance(parsed, (int, str, list)):
            raise ValueError(f"line {index}: unsupported value type for {key}")
        current[key] = parsed
    return data


def check_reuse_toml(errors: list[str]) -> int:
    path = HERE / "REUSE.toml"
    if not path.is_file():
        return 0
    text = path.read_text(encoding="utf-8")
    try:
        try:
            import tomllib  # type: ignore[import-not-found]
        except ImportError:
            import tomli as tomllib  # type: ignore[import-not-found,no-redef]
    except ImportError:
        parser = parse_simple_reuse_toml
    else:
        parser = tomllib.loads
    try:
        data = parser(text)
    except (OSError, ValueError) as error:
        errors.append(f"REUSE.toml: invalid TOML: {error}")
        return 0
    annotations = data.get("annotations")
    if data.get("version") != 1:
        errors.append("REUSE.toml: version must be 1")
    if not isinstance(annotations, list) or not annotations:
        errors.append("REUSE.toml: annotations must be a non-empty array of tables")
        return 0
    return len(annotations)


def check_workflows(errors: list[str]) -> None:
    active = HERE / ".github" / "workflows" / "verify.yml"
    mirror = HERE / "ci" / "verify.yml"
    if active.is_file() and mirror.is_file() and active.read_bytes() != mirror.read_bytes():
        errors.append(
            ".github/workflows/verify.yml and ci/verify.yml differ; "
            "copy the active workflow to the mirror location"
        )


def aggregate_imports(path: Path) -> list[str]:
    imports: list[str] = []
    code = erase_comments_and_strings(path.read_text(encoding="utf-8"))
    for declaration in IMPORT.findall(code):
        declaration = declaration.split("--", 1)[0]
        imports.extend(declaration.split())
    return imports


def check_release_partition(errors: list[str]) -> tuple[int, int, int]:
    lean_dir = HERE / "lean"
    if not lean_dir.is_dir():
        return 0, 0, 0
    module_paths = {
        lean_module_name(path, lean_dir): path
        for path in lean_dir.rglob("*.lean")
    }
    modules = set(module_paths)
    missing_aggregates = sorted(AGGREGATES - modules)
    if missing_aggregates:
        errors.append("missing Lean aggregates: " + ", ".join(missing_aggregates))
        return 0, 0, 0
    ordinary = modules - AGGREGATES
    release_list = aggregate_imports(
        HERE / "lean" / "BuddhistComparativeLogic" / "Release.lean"
    )
    experimental_list = aggregate_imports(
        HERE / "lean" / "BuddhistComparativeLogic" / "Experimental.lean"
    )
    for label, names in (("release", release_list), ("experimental", experimental_list)):
        duplicates = sorted(name for name, count in Counter(names).items() if count > 1)
        if duplicates:
            errors.append(f"{label} aggregate has duplicate imports: {', '.join(duplicates)}")
        unknown = sorted(set(names) - ordinary)
        if unknown:
            errors.append(f"{label} aggregate has non-subject imports: {', '.join(unknown)}")
    release = set(release_list)
    experimental = set(experimental_list)
    overlap = sorted(release & experimental)
    if overlap:
        errors.append("release/experimental import overlap: " + ", ".join(overlap))
    missing = sorted(ordinary - (release | experimental))
    extra = sorted((release | experimental) - ordinary)
    if missing:
        errors.append("Lean modules absent from release partition: " + ", ".join(missing))
    if extra:
        errors.append("unknown modules in release partition: " + ", ".join(extra))
    if len(ordinary) != EXPECTED_ORDINARY_MODULES:
        errors.append(
            "unexpected ordinary Lean module count: "
            f"expected {EXPECTED_ORDINARY_MODULES}, found {len(ordinary)}"
        )
    if len(release) != EXPECTED_RELEASE_MODULES:
        errors.append(
            "unexpected release Lean module count: "
            f"expected {EXPECTED_RELEASE_MODULES}, found {len(release)}"
        )
    if len(experimental) != EXPECTED_EXPERIMENTAL_MODULES:
        errors.append(
            "unexpected experimental Lean module count: "
            f"expected {EXPECTED_EXPERIMENTAL_MODULES}, found {len(experimental)}"
        )
    if experimental != EXPECTED_EXPERIMENTAL_SET:
        errors.append(
            "unexpected experimental Lean module set: "
            f"expected={sorted(EXPECTED_EXPERIMENTAL_SET)}, "
            f"found={sorted(experimental)}"
        )

    complete_imports = set(aggregate_imports(lean_dir / "BuddhistComparativeLogic.lean"))
    for aggregate in (
        "BuddhistComparativeLogic.Release",
        "BuddhistComparativeLogic.Experimental",
    ):
        if aggregate not in complete_imports:
            errors.append(f"BuddhistComparativeLogic aggregate does not import {aggregate}")

    direct_imports = {
        module: set(aggregate_imports(module_paths[module]))
        for module in ordinary
    }
    for module, imports in sorted(direct_imports.items()):
        aggregate_dependencies = sorted(imports & AGGREGATES)
        if aggregate_dependencies:
            errors.append(
                f"ordinary module {module} imports aggregate module(s): "
                + ", ".join(aggregate_dependencies)
            )
    graph = {
        module: {imported for imported in imports if imported in ordinary}
        for module, imports in direct_imports.items()
    }
    for start in sorted(release):
        pending = [(start, [start])]
        seen: set[str] = set()
        while pending:
            current, chain = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            for imported in graph.get(current, set()):
                next_chain = [*chain, imported]
                if imported in experimental:
                    errors.append(
                        "release dependency reaches experimental module: "
                        + " -> ".join(next_chain)
                    )
                elif imported not in seen:
                    pending.append((imported, next_chain))

    annotations_path = HERE / "catalog" / "catalog_annotations.json"
    if annotations_path.is_file():
        try:
            annotation_data = json.loads(annotations_path.read_text(encoding="utf-8"))
            annotations = annotation_data["modules"]
        except (
            OSError,
            UnicodeDecodeError,
            json.JSONDecodeError,
            KeyError,
            TypeError,
        ) as error:
            errors.append(
                f"catalog_annotations.json: cannot validate release status: {error}"
            )
        else:
            status_by_module = {
                item.get("module"): item.get("release_status")
                for item in annotations
                if isinstance(item, dict)
            }
            expected_aggregate_statuses = {
                "BuddhistComparativeLogic": "full_research_aggregate",
                "BuddhistComparativeLogic.Release": "release_candidate_aggregate",
                "BuddhistComparativeLogic.Experimental": "source_review_aggregate",
            }
            for module, expected_status in expected_aggregate_statuses.items():
                if status_by_module.get(module) != expected_status:
                    errors.append(
                        f"catalog aggregate status mismatch for {module}: "
                        f"expected {expected_status}, "
                        f"found {status_by_module.get(module)!r}"
                    )
            catalog_release = {
                module
                for module in ordinary
                if status_by_module.get(module) == "release_candidate"
            }
            catalog_experimental = {
                module
                for module in ordinary
                if status_by_module.get(module)
                in {"conditional_source_review", "deferred_source_review"}
            }
            if release != catalog_release:
                errors.append(
                    "release aggregate/catalog status mismatch: "
                    f"aggregate-only={sorted(release - catalog_release)}, "
                    f"catalog-only={sorted(catalog_release - release)}"
                )
            if experimental != catalog_experimental:
                errors.append(
                    "experimental aggregate/catalog status mismatch: "
                    f"aggregate-only={sorted(experimental - catalog_experimental)}, "
                    f"catalog-only={sorted(catalog_experimental - experimental)}"
                )
    return len(ordinary), len(release), len(experimental)


def run_generated_checks(errors: list[str]) -> list[str]:
    commands = (
        ("tools/check_text.py",),
        ("tools/check_names.py",),
        ("tools/make_index.py", "--check"),
        ("tools/make_formalization_catalog.py", "--check"),
    )
    summaries: list[str] = []
    for command in commands:
        if not (HERE / command[0]).is_file():
            errors.append(f"missing generated check: {command[0]}")
            continue
        result = subprocess.run(
            [sys.executable, *command],
            cwd=HERE,
            capture_output=True,
            text=True,
            check=False,
        )
        output = "\n".join(
            part.strip() for part in (result.stdout, result.stderr) if part.strip()
        )
        if result.returncode:
            errors.append(f"{' '.join(command)} failed:\n{output}")
        elif output:
            summaries.append(output.splitlines()[-1])
    return summaries


def main() -> int:
    errors: list[str] = []
    check_core_files(errors)
    check_software_scope(errors)
    text_count = scan_text_files(errors)
    link_count = check_markdown_links(errors)
    version = check_versions(errors)
    annotation_count = check_reuse_toml(errors)
    check_workflows(errors)
    ordinary, release, experimental = check_release_partition(errors)
    generated = run_generated_checks(errors)

    if errors:
        print("check_publication.py: FAILED", file=sys.stderr)
        for error in errors:
            indented = error.replace("\n", "\n  ")
            print(f"  {indented}", file=sys.stderr)
        return 1

    for summary in generated:
        print(summary)
    print(
        "check_publication.py: OK; "
        f"{text_count} text files, {link_count} local links, "
        f"REUSE {annotation_count} annotation groups, version {version}, "
        f"Lean partition {ordinary} = {release} release + {experimental} experimental"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
