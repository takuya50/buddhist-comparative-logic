<!-- SPDX-License-Identifier: CC0-1.0 -->

# Software release checklist

Role: `record`

Lifecycle: `draft`

Reviewed: 2026-09-20

This repository contains research software, a machine-checked formalization
corpus, technical documentation, and reproducibility audits. It does not
contain the research paper or its publication package. The code repository,
[takuya50/buddhist-comparative-logic](https://github.com/takuya50/buddhist-comparative-logic),
is public. The first GitHub release and tag, `v0.1.0`, are in preparation and
have not yet been created. Zenodo DOI `10.5281/zenodo.22851717` is reserved for
the software, but the draft deposit is not published. No Software Heritage
save has been submitted and no SWHID is recorded. The separately maintained
paper has not been deposited or published and has no DOI.

## 1. Fixed release identity

The software and planned first release use these values:

| Field | Value |
| --- | --- |
| Repository slug | `buddhist-comparative-logic` |
| Display name | Buddhist and Comparative Asian Logic Formalizations |
| GitHub description | Machine-checked formalizations of Buddhist and comparative Asian logic in Lean 4 and Isabelle/HOL. |
| Package version | `0.1.0` |
| First GitHub software release | `v0.1.0` (in preparation) |
| Artifact type | Research software and machine-checked formalization corpus |
| Included case study | The Heart Sutra formalization |
| Generated PDF | Isabelle technical reference and theory listing, not a paper or preprint |

`CITATION.cff` remains the GitHub software-citation record. Its software
version is `0.1.0`; `repository-code` identifies the public repository, and
`doi` records the reserved Zenodo identifier. `date-released` records the
chosen release day, 2026-09-20; the tag is created after this candidate passes CI.
A reserved DOI does not
assert that a deposit is published. This is not paper metadata. The author is
Nimble Ariake, ORCID [0009-0008-2838-6626](https://orcid.org/0009-0008-2838-6626). DOIs in
the source registry identify cited literature, not this software corpus.

The software version `0.1.0` is not a paper version. Paper metadata, its licence
decision, and publication approval are maintained with the separate paper
package, not in this software release.

## 2. Confirm the software release set

Read `RELEASE_SCOPE.md`. `BuddhistComparativeLogic.Release` is the reviewed import boundary;
`BuddhistComparativeLogic.Experimental` is a compiling source-review queue; `BuddhistComparativeLogic`
imports the complete research tree. The software release may contain all
three, but its headline claims and examples must be drawn from the release
set.

For every promotion from the experimental set:

1. identify the primary passage or mark the reconstruction as secondary
   orientation only;
2. register the edition, locator, URL, and access date in
   `sources/registry.json`;
3. state the translation or paraphrase policy and the formal claim boundary;
4. update `catalog/catalog_annotations.json`, the two aggregate imports, and
   `RELEASE_SCOPE.md`;
5. regenerate the catalog and rerun the full checks.

No historical locator should be inferred from a search-result snippet. Do
not redistribute a source text unless its licence or public-domain status has
been checked; a pinned locator and a project-authored paraphrase are enough
for reproducibility.

## 3. Keep the publication channels separate

GitHub, Zenodo, and Software Heritage are for the software corpus and its
technical documentation and audits only. The paper is to be published only on
figshare, through a separate approval and deposit process. A software release
or archive must not include the paper PDF, paper TeX sources, Japanese paper,
figshare metadata, or paper-specific evidence package. A later link to an
actually published paper may identify that separate artifact without bundling
it or assigning its DOI to the software.

Keep the separate paper package outside the software distribution. Excluding
it from this repository does not delete or relicense it. The Apache-2.0 audit
code and CC0 audit records included here are described in [`AUDITS.md`](AUDITS.md); they do not
make the separate paper part of this distribution.

## 4. Run the release checks

From the repository root, run:

```sh
python3 -m pip install reuse==5.1.1 cffconvert==2.0.0
sh tools/check-lean.sh
python3 tools/check_publication.py
python3 tools/check_license.py
cffconvert --validate
sh verify.sh
```

The Lean, standalone-release, REUSE, and CFF commands are the fast checks.
The licence wrapper runs REUSE on a temporary staging copy of the software
distribution files and audit records. It works for a Git-free source archive
and excludes local build output, including `.lake/`, from the licence check.
The final command repeats them after building the Isabelle session and its
technical-reference PDF with the pinned Isabelle 2025-2 distribution. A
release requires the complete sequence to pass on a clean copy. If the host
cannot run Isabelle, retain the last dated Isabelle/technical-reference
receipt and do not
describe the current audit as a fresh full build.

Review the generated files after the checks:

- `catalog/FORMALIZATION_CATALOG.md` and `catalog/formalizations.json` cover every Lean file;
- `STATUS.md` and `catalog/index.json` cover the Isabelle session;
- `sources/text/heart-sutra-t251-received-262.txt` matches its SHA-256 file;
- `STATUS.md`, `README.md`, and `CITATION.cff` agree on identity, scope, and
  counts;
- `python3 tools/check_license.py` and `cffconvert --validate` pass;
- `REUSE.toml` has the software Apache-2.0 and documentation/data CC0-1.0
  scopes only, and REUSE reports no paper-specific licence;
- the reproducibility audits in [`AUDITS.md`](AUDITS.md) pass;
- `.github/workflows/verify.yml` matches the checked-in CI mirror.

## 5. Prepare a software-only release candidate

Prepare the release candidate from a clean checkout of the public repository.
Track the Lean and Isabelle source trees, source registry, catalogue,
technical documentation, verification inputs and audit records, CI, and the
Apache-2.0/CC0-1.0 licensing files. Exclude the entire `paper/` directory and its separate
`LICENSES/LicenseRef-Paper-Draft-No-License.txt` notice. The separate paper
package is not a release payload.

Before committing a release candidate:

1. inspect the complete candidate file list, including untracked files, and
   reject any paper PDF, paper TeX source, Japanese paper, figshare metadata,
   or paper-specific evidence copied to another directory;
2. confirm that neither `paper/` nor its paper-specific licence notice exists
   in the release copy or staged file list; `.gitignore` is a backstop, not a
   substitute for this inspection;
3. exclude `.lake/`, `output/`, temporary distribution directories, build
   intermediates, caches, and local credentials; do not ignore PDF, TeX, JSON,
   TXT, or hand-written C files globally, since the Isabelle manual sources
   and software audit records belong in the software corpus;
4. inspect `git check-ignore` and the staged file list, then run the fast
   checks in the clean copy;
5. commit the software-only candidate and run CI against that exact commit.

Wait for `.github/workflows/verify.yml` to complete successfully before tagging
the candidate. A successful run for an earlier commit does not verify later
changes. The completed CI receipt is recorded in [`STATUS.md`](STATUS.md).

## 6. Publish the GitHub software release

For the first release from the public repository:

1. obtain maintainer approval for the software release and verify
   `repository-code`, package version, and reserved DOI in `CITATION.cff`;
2. on the chosen release day, add the actual `date-released`, validate the
   CFF file, commit the metadata, and wait for CI to pass again;
3. create the `v0.1.0` tag and GitHub software release from that verified commit;
4. confirm that the public README, source archive, citation metadata, release
   and experimental import boundaries, and CI result agree.

Zenodo software archiving and Software Heritage preservation are separate
software-only follow-up actions requiring maintainer approval. Publish the
existing Zenodo draft only with the intended verified software payload; until
then, continue to label its DOI as reserved and its deposit as unpublished.
Inspect archive payloads for the same exclusions before submission, and
record a Software Heritage identifier only after a successful save. Record only
identifiers actually assigned to this software; do not use the paper's figshare DOI as a
software DOI or claim an archive deposit before it exists.

The release notes must distinguish:

- kernel-checked theorem statements and countermodels;
- historical passage mappings and their evidence status;
- bounded modern reconstructions;
- the adopted Heart Sutra witness, which is not a critical edition;
- modules still in the source-review queue;
- the generated Isabelle PDF as technical documentation for the corpus.
