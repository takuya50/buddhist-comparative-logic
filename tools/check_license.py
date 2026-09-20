#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check distributable source and audit licences without requiring Git metadata."""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import check_publication
from make_snapshot import source_paths

ROOT = Path(__file__).resolve().parents[1]
REQUIRED_LICENCE_FILES = {
    "LICENSE", "LICENSE-CC0", "REUSE.toml",
    "LICENSES/Apache-2.0.txt", "LICENSES/CC0-1.0.txt",
}


def distributable_paths(root: Path) -> list[Path]:
    """Use the portable source policy, adding the separately published audits."""
    paths = source_paths(root)
    audit = root / "audit"
    if audit.is_dir() and not audit.is_symlink():
        paths.extend(source_paths(audit))
    return sorted(paths, key=lambda path: path.relative_to(root).as_posix().encode("utf-8"))


def software_scope_errors(root: Path) -> list[str]:
    """Apply the publication guard before exclusions can conceal a manuscript."""
    original_root = check_publication.HERE
    errors: list[str] = []
    try:
        check_publication.HERE = root
        check_publication.check_software_scope(errors)
    finally:
        check_publication.HERE = original_root
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="software source root")
    parser.add_argument("--reuse", default=shutil.which("reuse") or "reuse",
                        help="REUSE executable (version 5.1.1)")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        executable = shutil.which(args.reuse)
        if executable is None:
            print("check_license.py: REUSE is required; install reuse==5.1.1",
                  file=sys.stderr)
            return 1
        reuse_bin = str(Path(executable).resolve())
        errors = software_scope_errors(root)
        paths = distributable_paths(root)
        names = {path.relative_to(root).as_posix() for path in paths}
        errors.extend(f"missing distributable licence file: {name}"
                      for name in sorted(REQUIRED_LICENCE_FILES - names))
        if errors:
            for error in errors:
                print(f"check_license.py: {error}", file=sys.stderr)
            return 1
        print(f"check_license.py: validating {len(paths)} distributable files "
              "in an isolated source copy", flush=True)
        with tempfile.TemporaryDirectory(prefix="bcl-license-") as temporary:
            stage = Path(temporary)
            for source in paths:
                destination = stage / source.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
            result = subprocess.run(
                [reuse_bin, "--root", str(stage), "lint"], cwd=stage,
                check=False,
            )
            return result.returncode
    except OSError as error:
        print(f"check_license.py: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
