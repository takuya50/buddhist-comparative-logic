<!-- SPDX-License-Identifier: CC0-1.0 -->

# Reproducing the software audits

These audits cover a named representative selection, not every declaration.
They supplement the full corpus build; they do not replace it or certify the
historical adequacy of a formalization. No paper manuscript, paper inventory,
or bilingual-paper check is needed or included.

## Run after the full proof build

Use the pinned Lean 4.32.0 and Isabelle2025-2 toolchains. After the main Isabelle
session has completed (`sh tools/build.sh`), run from the repository root:

```sh
python3 tools/check_audits.py --isabelle "$ISABELLE_HOME/bin/isabelle"
```

Set `ISABELLE_HOME` to the application/distribution directory already used for
the full build, or pass its executable directly. The driver also recognizes
`ISABELLE_PREFIX` and an `isabelle` executable on `PATH`. For Lean, use Lake on
`PATH`, `LAKE_BIN`, `--lake PATH_TO_LAKE`, or the `lake` sibling of `LEAN_BIN`.
If none is provided, the platform-specific installation under `LEAN_PREFIX`
(by default `$HOME/.local/opt`) used by `tools/check-lean.sh` is also recognized.
No toolchain is installed by this driver.

The driver runs `lake build` before `lake env lean
verification/representative_axioms.lean`, so imported compiled modules resolve
in the project Lake environment. It then runs:

```sh
"$ISABELLE_HOME/bin/isabelle" process_theories \
  -D verification -d isabelle -l Buddhist_Comparative_Logic \
  -O -U Representative_Oracles
```

This uses the main session as its parent and processes the audit theory in an
isolated draft session; no additional `ROOT` is required. Isabelle may rebuild
the parent if its saved heap is absent or stale. Do not run a concurrent build
that writes the same parent heap. The audit sources live outside `lean/` and
`isabelle/` and do not change the corpus module or main-session theory counts.

The expected reports cover 33 Lean declarations and 32 Isabelle theorem names.
The driver checks the exact Lean selection and permits only `propext`,
`Classical.choice`, and `Quot.sound` as global Lean dependencies. It requires
exactly one empty Isabelle `oracles:` report. An empty oracle report does not
mean that Isabelle/HOL has no logical axioms; Lean's dependency report likewise
does not remove record fields or theorem arguments from the premises.

Reports are regenerated in `audit/`, including `lean-axioms.txt`,
`isabelle-oracles.txt`, toolchain/build output, and `representative-receipt.json`.
The receipt records each executed command, its exit status, and its report hash.
The driver does not hide failures behind a shell pipeline: a failed subprocess
produces a nonzero final exit and a `FAIL` receipt. Only reports listed in the
current receipt belong to that run. Local repository/toolchain/home paths are
replaced with relative paths or placeholders in the saved reports.

## Optional pinned CBETA comparison

Acquire the XML separately from the exact commit identified in
`sources/manifest.json`, and keep it outside this repository. The XML is not
redistributed. To include its comparison in the audit run:

```sh
python3 tools/check_audits.py --isabelle "$ISABELLE_HOME/bin/isabelle" \
  --cbeta-xml PATH_TO_PINNED_XML
```

For the comparison alone:

```sh
python3 tools/compare_cbeta_witness.py PATH_TO_PINNED_XML
```

The comparison checks SHA-256
`f5507df86309f861ef2b92e9ba9db985c6db0ad357553599c6e921e15deca761`,
isolates the sutra-body division, removes punctuation and whitespace, and
checks that the declared variants exactly reconstruct the adopted witness.
CBETA's edited running body has 260 codepoints; the adopted body has 262.
The insertion of `一切` supplies the length difference, while the specified
mantra variants preserve length. The report distinguishes CBETA's running
reading from the Taishō and other apparatus witnesses. This is a pinned-byte
comparison, not a critical edition or an identification of all those witnesses.

The driver saves `audit/cbeta-comparison.txt`. Without `--cbeta-xml`, that file
and the receipt explicitly say `NOT RUN`; a successful dependency-only run does
not claim to have repeated the external comparison. A wrong checksum or changed
comparison fails the run.

## Portable content snapshot

After all source and documentation edits are complete, run:

```sh
python3 tools/make_snapshot.py
```

The driver also runs this command at its end. It works in both a Git checkout
and an extracted software archive without Git initialization. Paths are sorted
by their UTF-8 bytes. `audit/corpus-manifest.sha256` contains
`<sha256>  <byte-count>  <relative-path>` rows; `corpus-manifest.digest` records
the manifest hash, file count, and total bytes.

The explicit portable exclusions cover `audit/` itself, `paper/`, Git and Lake
data, generated output/distribution/temporary directories, Python and tool
caches, virtual environments, editor files, conventional local environment and
key files, and symbolic links. Thus regenerating receipts does not change the
source fingerprint. These exclusions are implemented in `make_snapshot.py`;
they are not a general `.gitignore` interpreter or a secret scanner. Review the
release contents separately, and regenerate the snapshot after any source edit.

## Licensing and scope

Validate the distributable files from the repository root with:

```sh
python3 tools/check_license.py
```

The wrapper uses the portable source exclusions and also includes published
files under `audit/`, applying the same exclusions within that directory.
It retains the root licence texts and `REUSE.toml`, checks the software-only
scope, and runs REUSE in a temporary source copy. This works without Git
metadata even when the original directory contains `.lake/` or generated
output. No source, audit, or build file is removed or changed. The temporary
copy is removed after validation, and any REUSE failure produces a nonzero
exit. Install the pinned `reuse==5.1.1` validator before running it.

The audit scripts and Lean/Isabelle audit sources are Apache-2.0;
this documentation and generated audit data are CC0-1.0, as recorded in
`REUSE.toml`. The external CBETA XML remains under its own terms and is absent
from this software distribution. This software distribution does not license or include
the separate paper's prose, TeX sources, or PDFs. The receipts attest only to
their explicitly recorded software checks, not paper publication or licensing.
