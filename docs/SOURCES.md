<!-- SPDX-License-Identifier: CC0-1.0 -->

# Sources and provenance

This project separates four questions which are easy to conflate:

1. **Did a proof assistant accept the formal statement?** The Lean and
   Isabelle checks answer this.
2. **Which text or argument motivated the statement?** The catalogue and
   source registry record this.
3. **Does the formal predicate faithfully translate that passage?** This is a
   scholarly judgment and is marked as passage-aligned, work-level, or
   unverified rather than inferred from compilation.
4. **Are the premises true?** The project does not claim that they are. It
   derives consequences and constructs countermodels under explicit premises.

[`sources/registry.json`](../sources/registry.json) is the normalized source
registry. [`catalog/FORMALIZATION_CATALOG.md`](../catalog/FORMALIZATION_CATALOG.md) assigns every
Lean module a source status and distinguishes primary, secondary, and formal
sources. Missing evidence is recorded as `unverified`; it is never completed
from a title or from general background knowledge.

## Adopted Heart Sutra witness

The theorem-bearing body witness is
[`sources/text/heart-sutra-t251-received-262.txt`](../sources/text/heart-sutra-t251-received-262.txt).
It has 262 Unicode codepoints, no punctuation or spaces, and one final LF. Its
SHA-256, including that LF, is:

```text
efdccfe767855109acf0c7fa00b82a8851b431114eaa5b25a309aa4fd05a65c7
```

This is a **project-adopted Japanese-style received witness**, not the exact
260-character Taishō T251 body and not a critical edition. It is
assembled from the 31-clause transcription already maintained in `STATUS.md`.
The external comparison is CBETA's TEI transcription of Taishō T08 no. 251,
pp. 848c6–22, pinned to repository commit
`dbdea41071e1e260ad84b72faefd4587333cf76d`. The project does not redistribute
that XML file.

The differences relevant to the character claim are explicit:

- HS22 reads `遠離一切顛倒夢想`; the pinned CBETA running text reads
  `遠離顛倒夢想`. The received `一切` accounts for the project's 262 rather
  than 260 body count.
- The mantra has local `揭諦` / CBETA `揭帝` (four occurrences), local `波羅` /
  CBETA `般羅` (two), and local `薩婆` / CBETA `莎婆` (one). These replacements
  do not change length. At 0848c22 the apparatus records `莎婆` for CBETA,
  `僧莎` for Taishō, and `薩婆` for Song/Yuan/Ming: the edited CBETA running
  text is not identical to the Taishō witness.
- HS00 and HS30 are the title and colophon. They are covered by the formal
  clause enumeration but excluded from the 262-character body checksum.

`tools/check_text.py` checks the actual UTF-8 witness, its checksum, every clause
string and character count in `STATUS.md`, and both the Isabelle and Lean
`char_count` functions.

[`tools/compare_cbeta_witness.py`](../tools/compare_cbeta_witness.py) checks the pinned XML's checksum and
reconstructs the local 262-codepoint body from its 260-codepoint running body
using exactly the variants above. See the checked
[`audit/cbeta-comparison.txt`](../audit/cbeta-comparison.txt) record and
[`AUDITS.md`](AUDITS.md) for rerun instructions. These software audit materials
are included independently of the separate paper publication package.
The local transcription does not establish descent from a specific Japanese
edition. Nattier's 1992 Chinese-composition/back-translation hypothesis
(`nattier-1992-heart`) is textual-critical background, not a result of these
character-count or formal checks.

## Source-status vocabulary

| Status | Meaning |
| --- | --- |
| `passage_aligned` | A passage, clause, or adopted witness is identified. This does not imply that the edition or interpretation is uncontested. |
| `work_level` | A work or argument family is named, but the formal predicates are not mapped line by line to a fixed passage. |
| `unverified` | A historical target is suggested but the required edition or passage mapping has not been registered. |
| `not_applicable` | The module is pure logic, generic proof infrastructure, or an import aggregate and makes no historical passage claim. |

A web page used for orientation is not promoted to a critical edition. A
secondary article can justify why a comparison is worth making, but it does
not by itself turn a modern model into a translation. The `status` field on
each registry entry preserves these distinctions.

## Formal provenance

A manually documented statement-level correspondence links 35 Isabelle theory
units to 34 Lean modules; `BuddhistComparativeLogic.Core.Foundation` links to both
`FiniteLogics` and `Catuskoti`. [`PORTING.md`](PORTING.md) and `catalog/index.json`
record selected definitions, models, countermodels, and headline statements.
This is not a verified translation or a proof of whole-theory semantic or
cross-foundational equivalence.

`BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/Antidote.lean` is
classified as a Lean extension: its stopping and ascent results are not part
of the current 35-theory correspondence map. Its checked definitions and
proofs are self-contained in the current source tree.

## Source-review boundary for 24 release candidates

All 24 compile and contain checked positive results and finite boundaries.
Twenty-two have a fixed passage or an explicit secondary-orientation boundary
and are in the release aggregate. `BuddhistComparativeLogic.Comparative.Vedanta.Sriharsa` and
`BuddhistComparativeLogic.Buddhist.KoreanBuddhism.WonhyoHwajaeng` remain compilable under `BuddhistComparativeLogic.Experimental`
because their exact source-to-formal mappings are incomplete; their presence
must not be cited as
a historical edition claim.

## Bibliography limits

`isabelle/document/root.bib` is the bibliography for the generated Isabelle document.
It is not the normalized source-of-truth for all Lean extensions. Some records
lack stable URLs, DOI data, page ranges, or a theorem-to-passage relation.
The JSON registry and module catalogue make that incompleteness visible while
the bibliography is improved. A source should be added only after its title,
edition, locator, role, and relation to the formal predicate have been checked.
