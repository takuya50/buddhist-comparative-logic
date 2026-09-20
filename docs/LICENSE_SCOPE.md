<!-- SPDX-License-Identifier: CC0-1.0 -->

# Licence scope

The formalization code and the scripts which verify it are licensed under
Apache License 2.0.  This includes:

- `lean/`, `isabelle/`, `verification/`, `lakefile.toml`, `lean-toolchain`, and
  `lake-manifest.json`;
- `.github/`, `ci/`, shell scripts, and Python scripts;
- `isabelle/document/root.tex` and `isabelle/document/root.bib`, which drive an Isabelle
  document containing Apache-licensed theory listings; and
- machine-readable project configuration not listed below as documentation.

The explanatory writing and release metadata are dedicated to the public
domain under CC0 1.0.  This includes Markdown files, `CITATION.cff`,
`catalog/formalizations.json`, the source manifests under `sources/`, and
generated audit records under `audit/`. The representative proof-audit inputs
under `verification/` and the audit scripts under `tools/` are Apache-2.0 code,
not CC0 records.

The separately maintained paper, its translations, and its paper-specific
evidence package are not part of this software distribution. These software
and documentation licences do not license that separate paper package.
Excluding it from the software release does not alter its existing rights or
publication status.

The Chinese Heart Sutra text represented in
`sources/text/heart-sutra-t251-received-262.txt` is an ancient public-domain
text.  The project's segmentation, whitespace-free transcription, metadata,
and checksum are released under CC0 1.0.  The repository does not redistribute
the CBETA TEI file cited as a comparison witness in `SOURCES.md`; CBETA's own
terms continue to govern that external electronic edition.

The Isabelle-generated technical-reference PDF is a composite: explanatory prose is offered under CC0,
while rendered theory listings remain under Apache-2.0.  The PDF as a whole is
therefore not described as CC0-only.

The complete Apache-2.0 and CC0-1.0 texts are in `LICENSES/`.  The root
`LICENSE` is the Apache-2.0 text for software-hosting services which display a
single repository licence.  `REUSE.toml` records the same split in a
machine-readable form.
