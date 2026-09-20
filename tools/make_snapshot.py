#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Write a deterministic software-source manifest, also from a Git-free archive."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "audit"
SKIP_DIRS = {
    ".git", ".lake", "audit", "paper", "output", "outputs", "dist", "tmp", "temp",
    "__pycache__", ".cache", ".pytest_cache", ".mypy_cache", ".ruff_cache",
    ".venv", "venv", ".idea", ".vscode", ".direnv",
}
SKIP_NAMES = {".DS_Store", ".env", ".envrc"}
SKIP_SUFFIXES = {".pyc", ".pyo", ".pyd", ".pem", ".key", ".p12", ".pfx", ".swp", ".swo"}


def included(path: Path, root: Path = ROOT) -> bool:
    """Explicit portable exclusions; this is not a general .gitignore parser."""
    relative = path.relative_to(root)
    return (
        path.is_file()
        and not path.is_symlink()
        and not any(part in SKIP_DIRS for part in relative.parts)
        and path.name not in SKIP_NAMES
        and not (path.name.startswith(".env.")
                 and path.name not in {".env.example", ".env.sample"})
        and path.suffix not in SKIP_SUFFIXES
        and not path.name.endswith("~")
    )


def source_paths(root: Path = ROOT) -> list[Path]:
    paths = []
    for directory, names, files in os.walk(root, followlinks=False):
        base = Path(directory)
        names[:] = [name for name in names
                    if name not in SKIP_DIRS and not (base / name).is_symlink()]
        paths.extend(base / name for name in files if included(base / name, root))
    return sorted(paths, key=lambda path: path.relative_to(root).as_posix().encode("utf-8"))


def main() -> None:
    rows = []
    total_bytes = 0
    paths = source_paths()
    for path in paths:
        content = path.read_bytes()
        total_bytes += len(content)
        relative = path.relative_to(ROOT).as_posix()
        if "\n" in relative or "\r" in relative:
            raise ValueError("manifest paths must not contain newline characters")
        rows.append(f"{hashlib.sha256(content).hexdigest()}  {len(content)}  {relative}\n")
    manifest = "".join(rows).encode("utf-8")
    digest = hashlib.sha256(manifest).hexdigest()
    AUDIT.mkdir(parents=True, exist_ok=True)
    (AUDIT / "corpus-manifest.sha256").write_bytes(manifest)
    (AUDIT / "corpus-manifest.digest").write_text(
        f"sha256  {digest}\nfiles  {len(paths)}\nbytes  {total_bytes}\n", encoding="utf-8",
    )
    print(f"files={len(paths)} bytes={total_bytes} manifest_sha256={digest}")


if __name__ == "__main__":
    main()
