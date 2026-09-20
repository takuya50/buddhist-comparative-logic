# Buddhist and Comparative Asian Logic Formalizations

Machine-checked formalizations of Buddhist and comparative Asian logic in
Lean 4 and Isabelle/HOL.

Role: `supplement`

Lifecycle: `active`

Full verification receipt: 2026-09-20 (Isabelle2025-2, the
35-theory session, a 153-page technical-reference PDF, all 115 Lean modules,
release guards, REUSE, and CFF validation).

## Planned standalone software release

The code repository is
[takuya50/buddhist-comparative-logic](https://github.com/takuya50/buddhist-comparative-logic).
It is **PRIVATE and access-restricted**; readers cannot view it without
authorization. No public software release or release tag has been issued.
The planned release identity is:

| Field | Planned value |
| --- | --- |
| Repository slug | `buddhist-comparative-logic` |
| Display name | Buddhist and Comparative Asian Logic Formalizations |
| GitHub description | Machine-checked formalizations of Buddhist and comparative Asian logic in Lean 4 and Isabelle/HOL. |
| First GitHub software release | `v0.1.0` |

The artifact is research software and a machine-checked formalization corpus.
The Heart Sutra is one detailed textual case study within the wider library.
The Isabelle-generated PDF is a technical reference and theory listing, not
the research paper. This repository distributes the software corpus, its
technical documentation, and reproducibility audits only. The separate English
paper, Japanese version, and paper-specific evidence package are maintained
outside this repository and are intended for publication only on figshare.
GitHub, Zenodo, and Software Heritage are intended for the software only.
No DOI has been assigned to this software or the separate paper, and no paper
publication or software release date is asserted. The author is Nimble Ariake,
ORCID [0009-0008-2838-6626](https://orcid.org/0009-0008-2838-6626).
[`CITATION.cff`](CITATION.cff) is software citation metadata and does not describe
the paper. See [`docs/PUBLISHING.md`](docs/PUBLISHING.md) for the release
procedure.

The library brings together formalizations of Buddhist and comparative Asian
logic.  Its Isabelle/HOL session includes a Heart Sutra case study that
classifies every clause of a project-adopted 262-character received witness
of the Xuanzang-attributed short text. A manually documented statement-level
correspondence maps 35 Isabelle theory units to 34 Lean modules. The map records
selected definitions, witnesses, and theorem statements; it is not a checked
translation or a proof that the foundations or whole modules are equivalent.
Other Lean modules give
explicit proof interfaces and countermodels for Madhyamaka, Buddhist
epistemology, Yogācāra, and selected Jaina, Nyāya, Mīmāṃsā, Sāṃkhya,
Tibetan, Chinese, Korean, and grammatical comparisons.

The logical layer is parametric over classical logic, Belnap–Dunn
first-degree entailment (FDE), and an extension with an undesignated absorbing
fifth value. The same formula can be evaluated under each semantics, so differences
are checked as theorems or concrete countermodels.

The proof assistants verify that conclusions follow from the displayed
definitions and assumptions.  They do **not** establish that a doctrine is
true, that a premise is historically or empirically correct, or that a
bounded modern reconstruction is the unique interpretation of a text.  The
adopted Chinese witness is not presented as a critical edition.

The central contribution is an auditable, reproducible corpus: a claim can be
traced to its definitions, actually used premises, theorem or countermodel,
source locator, and rerun command. Simple implication-composition lemmas are
useful audit boundaries, not claims of mathematically deep new discoveries.
The corpus distinguishes these from algorithm correctness, executable
countervaluation extraction, relative premise independence, and small-model
preservation for the chosen existential-support semantics.

## Quick start

From the repository root:

```sh
sh tools/check-lean.sh   # Lean-only, bare pinned Lean 4.32.0, no Mathlib
sh verify.sh             # Isabelle + technical PDF + Lean + audits + release guards
```

The full command installs the pinned Isabelle distribution outside the
repository when needed.  For imports, use
`BuddhistComparativeLogic.Release` for the author-reviewed software-release set,
`BuddhistComparativeLogic.Experimental` for the source-review queue, or
`BuddhistComparativeLogic` for the complete research tree.  There are 112
subject and infrastructure modules plus these three aggregate modules: 115 in
total, with 110 release modules and two experimental modules. “Author-reviewed”
means the sole author's self-review of source and scope, not independent or
external peer review.

For historical-source status the ordinary population is 25 passage-aligned,
68 work-level, and 19 not applicable (112 total). All three aggregate import
files are separately classified as not applicable. The catalogue generates
these populations independently.

The repository is organized by purpose: `lean/` contains the Lean library,
`isabelle/` contains the Isabelle session and generated-manual sources,
`docs/` contains explanatory and release documentation, `catalog/` contains
the machine-readable and rendered formalization catalog, `verification/`
contains representative proof-audit inputs, `audit/` contains audit records,
and `tools/` contains the verification and maintenance scripts.

## Project map

| Area | Entry point |
| --- | --- |
| Generic non-classical logic | [`docs/REUSE.md`](docs/REUSE.md) |
| Heart Sutra text and clause coverage | [`docs/STATUS.md`](docs/STATUS.md) |
| Isabelle-to-Lean provenance | [`docs/PORTING.md`](docs/PORTING.md) |
| Madhyamaka and argument composition | [`docs/ARGUMENTS.md`](docs/ARGUMENTS.md) |
| Pramāṇa and Yogācāra | [`docs/PRAMANA_YOGACARA.md`](docs/PRAMANA_YOGACARA.md), [`docs/PRAMANA_TREATISES.md`](docs/PRAMANA_TREATISES.md) |
| Comparative traditions | [`docs/COMPARATIVE_LOGIC.md`](docs/COMPARATIVE_LOGIC.md) |
| Every Lean module, its assumptions and source status | [`catalog/FORMALIZATION_CATALOG.md`](catalog/FORMALIZATION_CATALOG.md) |
| Reproducibility audits and rerun instructions | [`docs/AUDITS.md`](docs/AUDITS.md) |
| Text witness and normalized source registry | [`docs/SOURCES.md`](docs/SOURCES.md) |
| Release versus experimental modules | [`docs/RELEASE_SCOPE.md`](docs/RELEASE_SCOPE.md) |
| Known mathematical and historical limits | [`docs/OPEN_PROBLEMS.md`](docs/OPEN_PROBLEMS.md) |

**Six results, if you read nothing else.**

- Under FDE, the sutra's "form is not different from emptiness" is *not*
  derivable from the sutra's own premises; a glut on own-being defeats it
  (`fde_R_identity_not_notsep`).
- Splitting the claim across the two truths recovers it, and exactly when
  each truth is internally consistent about its own subject matter
  (`hs06_two_truths`). What the two truths buy is not paraconsistency but
  its localisation.
- Priest's fifth value is not a fifth corner of the catuṣkoṭi: at the level
  of designation it lands on the fourth, where the gap already is
  (`fde5_koti_of_E`).
- For the encoded classical and FDE bases, general plurivalence under universal
  designation has a checked variable-inclusion characterization
  (`priest_open_question_classical`, `priest_open_question_fde`).
- Dignāga's three marks of a good reason are not deductively sufficient:
  a model satisfies all three, the wheel returns Valid, and the thesis is
  false (`no_deductive_soundness`).
- The Jaina sevenfold predication is not seven truth values: three of its
  modes are unsatisfiable on any single valuation, and the seventh needs
  three distinct respects (`seventh_mode_needs_three_nayas`).

**Scope, and what would be out of it.**

The thirty-five Isabelle theories comprise twenty-five Buddhist case-study
theories, nine shared core theories, and one Jaina theory.
`isabelle/Comparative/Jaina/Jaina_Saptabhangi.thy` treats sevenfold predication
as a bounded comparison with the four corners and tests its "inexpressible"
mode against Priest's fifth value. The shared core supplies reusable logic
infrastructure; `isabelle/Core/ManyValuedLogicExample.thy`, for example, has no
doctrinal content and shows how to add a logic to the framework.

The comparative Lean-only layer includes selected Jaina, Sāṃkhya, Nyāya,
Mīmāṃsā, Vedānta, Mohist, School of Names, Huayan, Pāṇinian, Tibetan, and
Korean Buddhist arguments.  These are bounded logical interfaces, not added
clauses of the Heart Sutra.  A clause-by-clause edition
of another canon would still need a separate textual development: the
apparatus (`HeartSutra_Text`, `tools/check_text.py`, and the clause table) and
its wording rules concern one text in one language.

**Reproduce everything in one command.**

```sh
sh verify.sh
```

That installs the platform-specific Isabelle 2025-2 distribution, checks the
35 Isabelle theories, builds the technical-reference PDF, type-checks every
Lean module, and runs
the documentation guards. The first Isabelle download is about 1.2 GB on
Linux or 1.7 GB on macOS. The Lean 4.32.0 version is pinned by
`lean-toolchain`; direct Linux and macOS fallback archives are also pinned by
platform-specific SHA-256 digests.
After that a full clean run takes a few minutes.

**What to read next.** [`docs/STATUS.md`](docs/STATUS.md) is the clause-by-clause
table and the wording rules that govern what may be claimed;
[`docs/REUSE.md`](docs/REUSE.md) says which files to take if you only want the
non-classical logic infrastructure; [`docs/PORTING.md`](docs/PORTING.md) is the
Isabelle-to-Lean map; [`docs/OPEN_PROBLEMS.md`](docs/OPEN_PROBLEMS.md)
lists what this sets up but does not settle.

**Lean extensions beyond the Isabelle map.** [Lean progress](docs/LEAN_PROGRESS.md)
records four modules for an audit of dependence and two-truths
assumptions, a quantitative path model with independent observations and
countermodels, attachment-gated Jizang iteration, and an explicit pervasion
adapter for the emptiness inference. These are included in the Lean checker;
they do not add to the 35-theory Isabelle session. The path update laws
remain modeling hypotheses, and the corresponding path theorems remain
definitional.

**Supporting arguments.** [Argument formalization](docs/ARGUMENTS.md) records four
Lean modules: conditional variation derives the dependence-exclusion
bridge, explicit case obligations support fourfold non-arising, a general
countermodel transformation audits the subject omitted by the three marks,
and the path's cessation result refutes fixed suffering. Source passages
and the remaining interpretive premises are recorded separately.

**Logic, argument, and text-alignment modules.** Sixteen modules distinguish
causal, mereological, and conceptual dependence and its coverage; reconstruct
fourfold causation; give evidence-sensitive belief revision, a cognitive
antidote gate, an explicit specification of the selected tier remedy, and an
argument-to-practice pipeline; add sound-and-complete natural deduction and
analytic tableaux for FDE/FDE5; settle the defined K3 and LP
universal-designation cases and characterize an absorbing ineffable extension;
and add naya traces, conditional momentariness results, an apoha feature
hierarchy with stopping and oscillation boundaries, interval motion,
observational comparison of Viṃśatikā models,
and edition-parametric Sanskrit/Tibetan alignment with bounded central token
spans and an explicit source-order reversal.  These theorems hold under the
premises encoded by their records and definitions.  The path updates and
antidote adequacy remain modeling specifications, and lexical validation does
not choose a translation or philosophical construal.

**Premise and selection interfaces.** Five Lean modules distinguish
local from covered dependence and connect it to inference, keep citation
metadata separate from proof-bearing premise certificates, give shipped
internal references compiler-resolved names, transport ordinary
and universal-designation consequence across an explicit matrix isomorphism,
derive momentariness from backward-only rooted causal transport, and prove
at-most-one componential apoha pair under an explicit antisymmetric selection
rule, with existence supplied by an optimal requirement.
Finite countermodels show why local evidence, a citation, or mere
admissibility cannot replace the corresponding premise, and why forward
transport need not be assumed.  The directed declarations reuse the existing
momentariness theory interface, whose separate two-times field is not used by
the directed proof.  External evidence locators remain unchecked annotations,
and the fourfold release certificate requires an occurring event.

**Pramāṇa and Yogācāra synthesis.** Four Lean modules consolidate
subject-level deduction and public comparison in Buddhist inference, the
three natures, seed continuity and transformation, the eight consciousnesses
as functional roles, and the inferential limits of observation-only evidence.
Finite models show that three marks do not supply the missing pervasion, that
causal continuity does not imply an unchanging seed or transformation, that
the eight-role taxonomy does not imply store support or permanence, and that
observational adequacy cannot choose external-object existence or cardinality.
See [the combined audit](docs/PRAMANA_YOGACARA.md).

**Catuṣkoṭi, K3, and FDE synthesis.** One Lean module proves that the
repository's K3 matrix is exactly the non-glut `T`/`N`/`F` submatrix of FDE,
including preservation of connectives, evaluation, designation, satisfaction,
and consequence on the restricted valuation class.  Unrestricted FDE
consequence implies K3 consequence, while explosion supplies a checked failure
of the converse.  The four-corner map is injective on FDE; K3 realizes exactly
the true-only, false-only, and neither corners.  A separate set-valued result
distinguishes universal from existential corner classification.  See
[the logic audit](docs/CATUSKOTI_K3_FDE.md).

**Four pramāṇa treatise architectures.** Four Lean modules reconstruct
selected proof interfaces from the *Pramāṇasamuccaya*, *Pramāṇavārttika*,
the momentariness-proof tradition, and the *Tattvasaṃgraha*.  They separate
perception from conceptual classification, subject warrants from public
proof, causal efficacy from numerical momentariness, and local debate
certificates from encyclopedic coverage.  Finite countermodels expose each
extra pervasion, scope, transport, and composition premise.  See
[the treatise audit](docs/PRAMANA_TREATISES.md).

**Inference and debate interfaces.** Four Lean modules formalize a
five-member Nyāya public proof, the causal-production/image-similarity dilemma
of the *Ālambanaparīkṣā*, a finite Tibetan consequence-debate calculus, and
behaviour-based inference to another stream of cognition.  Each positive
result is paired with a concrete scope countermodel.  See
[the inference and debate audit](docs/INFERENCE_DEBATE.md).

**Comparative logic interfaces.** Six Lean modules formalize
opponent-relative autonomous inference and consequence refutation, Mohist
standards and kind extension, Gaṅgeśa's pervasion and counterconditions,
Mīmāṃsā entitlement and independent knowledge sources, Tibetan definition
theory, and Dharmakīrti's critique of reified relations.  The modules keep
semantic consequence, dialogue commitment, initial entitlement, coextension,
and ontological identity as separate notions, with finite models showing why
the corresponding converse steps fail.  See
[the comparative logic audit](docs/COMPARATIVE_LOGIC.md).

**Debate and cross-tradition interfaces.** Six modules formalize Vādanyāya debate outcomes,
*sahopalambhaniyama*, Śāntarakṣita's one-or-many argument, the paired
extension questions of the Pāli *Yamaka*, the White Horse distinction, and
Jayarāśi's audits of circular grounding and finite extrapolation.  Executable
classifiers and finite models keep procedural victory, observational
nonseparation, numerical identity, intrinsic nature, extensional inclusion,
intensional constraints, and global pervasion distinct.  Their exact proof
boundaries are included in [the comparative logic audit](docs/COMPARATIVE_LOGIC.md).

**Pervasion, person, definition, mereology, and language interfaces.** Six
modules reconstruct Ratnakīrti's determination of pervasion,
Vasubandhu's critique of a separate substantial person, Jaina
`anyathānupapatti`, Śrīharṣa's tests for defective definitions and epistemic
luck, Fazang's rafter-and-house mereology, and a staged reconstruction inspired
by Bhartṛhari's treatment of the unsignifiable.  The corresponding
countermodels separate finite
observation from universal inclusion, causal continuity from numerical
identity, actual co-occurrence from modal connection, truth from a reliable
route, collections from strongly dependent wholes, and base-vocabulary
silence from later-stage designation.

**Absence, sentence meaning, inference, awareness, grammar, and reconciliation.**
Six modules type Navya-Nyāya absence, the two Mīmāṃsā
sentence-meaning architectures, Udayana's effect-to-maker inference,
Dignāga-Dharmakīrti reflexive awareness and memory attribution, a bounded
Pāṇinian priority-rewrite system, and a local-theory gluing reconstruction
inspired by Wŏnhyo's *hwajaeng*.  The positive results require explicit
scope, semantic, causal, trace, determinacy, or overlap premises.  Finite
models show that bare non-cognition does not establish qualified absence,
isolated artifacts do not
establish a universal maker rule, word meanings do not fix argument order,
co-apprehension does not yield self-presentation or identity, termination
does not give a unique normal form, and context erasure can collect opposed
formulas.

**Causation, change, interpretation, negation, and sensory comparison.** Six
modules reconstruct Sāṃkhya latent causation, the Jaina triad
of production, decay, and duration, Vasubandhu's five-part commentary method,
eleven typed non-apprehension deployment shapes from the selected
*Nyāyabindu* 2.31–42 passage, the sensory-access argument of the *Hard and
White* discussion, and a Gelug/Tsongkhapa-inspired calibration of the object
of negation.  Their interfaces and certificates keep causal capacity, change
of mode, exegetical completeness, negative-reason side conditions, sensory
distinguishability, and predicate coextension separate.  Finite models expose
the extra premises needed for latent preexistence, enduring identity,
interpretive uniqueness, sound negation, ontological separation, and a
well-calibrated negandum.

**Predicate, perception, tarka, analysis, acceptance, and priority.** Six
modules give the witness-cell comparisons used in Tibetan
*bsdus grwa*, the boundary between nonconceptual perception and
*pratyakṣābhāsa*, Nyāya *tarka* as counterposition elimination, the
*Abhidharmakośabhāṣya*'s analysis-sensitive two-truths classification,
opponent-relative acceptance in the Xuanzang–Wŏnhyo inference dispute, and
Mīmāṃsā *viniyoga* priority.  Their Lean interfaces distinguish cell
occupancy from coarse predicate relations, nonconceptuality from correctness,
hypothetical elimination from an independent knowledge source, invariance
from an underspecified analysis family, local acceptance from common semantic
ground, and evidential rank from applicability or truth.

The complete Lean tree has 115 modules: 112 subject and infrastructure modules
plus three aggregates.  `BuddhistComparativeLogic.Release` imports the 110
reviewed modules, `BuddhistComparativeLogic.Experimental` imports the two
modules retained for exact source-to-formal mapping review, and
`BuddhistComparativeLogic` imports both aggregates.  Thirty-four subject
modules represent the 35 Isabelle theory units, and 78 modules are Lean-only
extensions.  These counts do not enlarge the 35-theory Isabelle session or its
clause-coverage claim.

**Licence.** Formalization code, verification scripts, and Isabelle document
sources are Apache-2.0. Explanatory Markdown and release/source metadata
are CC0-1.0. The generated PDF is composite: prose is offered under CC0 while
rendered theory listings remain Apache-2.0. The ancient Chinese text is public
domain; the project's transcription metadata is CC0. See
[`docs/LICENSE_SCOPE.md`](docs/LICENSE_SCOPE.md) for the exact boundary and
[`CITATION.cff`](CITATION.cff) for citation metadata.

**How this was made.** AI-assisted drafting was used during development,
including Claude (Anthropic). Proof acceptance is determined by the Lean and
Isabelle kernels. Source selection, historical mapping, interpretation, and
release classification remain human scholarly responsibilities and are not
certified by kernel checking.

## What this is, and is not

The Heart Sutra case study is a **definitional reconstruction**: every clause
of the sutra gets a datatype, function, locale, or theorem, and every theorem's
assumptions are either standard Abhidharma/Madhyamaka structure (the five
skandhas, twelve āyatanas, eighteen dhātus, twelve nidānas) or a direct
restatement of the sutra's own stated implications. It is **not** a proof that
the sutra's claims are true, that any particular philosophical reading is
correct, or that Buddhist metaphysics is consistent. See
[`docs/STATUS.md`](docs/STATUS.md) for the full wording rules and the
clause-by-clause coverage table, and for why: `formal-theorem` (this
repository's Lean-only evidence label) is not used here.

## The Heart Sutra case study and three logics

Classical logic forces "form is emptiness" and "neither arising nor
ceasing" into either triviality or contradiction. The shared Isabelle core
defines a single generic many-valued logic
(`ManyValuedLogic.mv_logic`) and instantiates it three ways — classical,
Belnap–Dunn First Degree Entailment (FDE), and Priest's FDE extended with a
fifth "ineffable" value — so the *same* formulas can be evaluated under
each and compared. This reproduces, as a machine-checked countermodel,
A. J. Cotnoir's published objection that FDE's conditional does not
validate modus ponens (`FiniteLogics.fde_mp_fails`), and shows that Priest's
fifth value is not a fifth *corner* of the catuṣkoṭi but a fifth *value*
landing on an existing corner (`Catuskoti.fde5_koti_of_E`).

## Layers

| File | Layer | Clauses |
| --- | --- | --- |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Text.thy` | 262-character segmentation into 31 IDs | HS00–HS30 |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Dharma.thy` | skandhas, āyatanas, dhātus, nidānas, four truths | structural half of HS03/08/11–17 |
| `isabelle/Core/ManyValuedLogic.thy` | generic many-valued propositional logic | infrastructure |
| `isabelle/Core/FiniteLogics.thy` | classical / FDE / FDE+fifth-value instances | infrastructure |
| `isabelle/Core/Catuskoti.thy` | the four corners and the fifth value | infrastructure |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Emptiness.thy` | svabhāva, dependent origination, three readings of 色即是空 | HS03, HS06–HS19 |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Path.thy` | bodhisattva's and buddhas' reliance on prajñāpāramitā | HS01/02/04/20–24/26 |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Mantra.thy` | epithets and the mantra; explicit non-formalizability | HS25, HS27–HS29 |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Coverage.thy` | every clause has a counterpart; no clause is `Missing` | all |
| `isabelle/Buddhist/Madhyamaka/Madhyamaka_MMK24.thy` | MMK 15:2 + 24:19 derive the emptiness axiom; middle way per logic | extension |
| `isabelle/Buddhist/HeartSutra/HeartSutra_TwoTruths.thy` | 世俗諦 / 勝義諦 as two evaluation points; recovers HS06 under FDE with locally consistent truths | extension |
| `isabelle/Core/PlurivalentSemantics.thy` | functional vs relational plurivalent semantics; `e` as the empty value set (mechanizes Priest 2014 §4/§6) | extension |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Connexive.thy` | connexive (MC) reading of 不生不滅: bivalent, true iff own-being absent | extension |
| `isabelle/Buddhist/Pramana/Dignaga_Hetucakra.thy` | Dignāga's nine reasons, three marks, non-deductive character | independent |
| `isabelle/Core/UniversalDesignation.thy` | classical-base universal designation = K3 + designated infectious value, with a variable-inclusion characterisation | independent |
| `isabelle/Buddhist/DiamondSutra/DiamondSutra_Sokuhi.thy` | Diamond Sutra 即非の論理: glut at one level, bivalent across the two truths | extension |
| `isabelle/Buddhist/Madhyamaka/Madhyamaka_Jizang.thy` | Jizang's 四重二諦: stabilises at tier 2 on every truth-functional semantics | extension |
| `isabelle/Core/UniversalDesignationFDE.thy` | generic variable inclusion + positive plurivalence; θ verified; FDE instance | independent |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Sanskrit.thy` | Sanskrit formulations of HS06-07, *māyopama* as fourth reading, 空即是色 = the samvṛti premise | extension |
| `isabelle/Buddhist/HeartSutra/HeartSutra_PathModel.thy` | grasping model: the HS20–26 chain derived from definitions (sublocale of `bodhisattva_path`) | extension |
| `isabelle/Buddhist/HeartSutra/HeartSutra_Anumana.thy` | 諸法皆空 as a Dignāga inference; the agreed example decides Valid vs Contradictory | extension |
| `isabelle/Buddhist/Madhyamaka/Madhyamaka_MMK1.thy` | MMK 1:1 four-fold non-arising: classical vs FDE, modus tollens | extension |
| `isabelle/Core/FiniteDecisionProcedures.thy` | executable checkers for the three-atom fragment, proved correct; results recomputed `by eval` | infrastructure |
| `isabelle/Buddhist/Pramana/Dharmakirti_Reasons.thy` | Dharmakīrti's three kinds of reason; pervasion as the located inductive premise | independent |
| `isabelle/Buddhist/EarlyBuddhism/Avyakata.thy` | the fourteen unanswered questions: rejection as glut (formula level) or gap (designation level) | extension |
| `isabelle/Buddhist/Madhyamaka/Madhyamaka_StandpointSemantics.thy` | standpoint frames: two truths, Jizang's four tiers separated, Tiantai three truths, Prāsaṅgika as the empty standpoint | extension |
| `isabelle/Buddhist/Madhyamaka/Madhyamaka_Vigrahavyavartani.thy` | Vigrahavyāvartanī: emptiness of the statement of emptiness; "I have no thesis" across two standpoints | extension |
| `isabelle/Core/FDEProofTheory.thy` | relevance, containment, and a sound and complete decision procedure for FDE and FDE5 over arbitrary atoms | independent |
| `isabelle/Buddhist/HeartSutra/HeartSutra_LongerRecension.thy` | the longer recension: the frame adds the speech situation, and the samādhi is the ultimate standpoint | extension |
| `lean/BuddhistComparativeLogic/Core/Foundation.lean` | Lean 4 formulas, classical/FDE/FDE5 semantics and catuṣkoṭi core | cross-check |

The `extension`/`independent`/executable labels identify each theory's role in
the current session; [`docs/PORTING.md`](docs/PORTING.md) maps all 35 Isabelle theory
units to their Lean counterparts. `docs/STATUS.md`, section "Theories beyond
the clause table", states each result and its label, and its section "Related
work and contribution scope"
records selected prior work and the boundary of each corpus contribution.
The plurivalent results restate Priest 2014 in machine-checked form, while
the two-truths and connexive modules test project-defined reconstructions;
Chapman 2026 supplies a related formal modal treatment of Nāgārjuna's
catuṣkoṭi.

## Build

```sh
sh verify.sh                  # everything: Isabelle session, technical PDF,
                              # Lean development and reproducibility audits,
                              # catalogue, links, licences, and whitespace
```

The steps separately:

```sh
sh tools/install-isabelle.sh  # downloads the Linux/macOS Isabelle2025-2
                              # archive, verifies its platform SHA-256, and
                              # extracts outside the repository
sh tools/build.sh             # 'sorry' gate, tools/check_text.py, tools/check_names.py,
                              # then builds the Isabelle session
sh tools/build.sh --pdf       # also renders isabelle/document/root.tex;
                              # implies a clean session build
                              # (needs lualatex, luatexja, IPA fonts: on Debian/Ubuntu
                              #  texlive-luatex texlive-latex-extra texlive-lang-japanese
                              #  fonts-ipafont)
sh tools/check-lean.sh        # finds or downloads Linux/macOS Lean 4.32.0
                              # (no Mathlib), resolves local imports, and
                              # type-checks every lean/*.lean module with
                              # warnings as errors
lake build                    # standard Lean/Lake build of the same aggregate
```

`tools/install-isabelle.sh --check` and `tools/check-lean.sh --check` report
the current install state without downloading. Neither installer writes
inside this repository; Isabelle writes `isabelle/output/` and Lake writes
`.lake/` (both ignored; see `.gitignore`).

`tools/check_names.py` is the guard against documentation drift: it fails the
build if a theorem named in `docs/STATUS.md` or this file does not exist, if
`isabelle/ROOT` and the Isabelle theory hierarchy disagree, if a locale has no
model witness, or if `oops` is used outside a Nitpick regression.
`docs/STATUS.md`, section "What the build enforces", lists the invariants.

## References

Priest, Cotnoir, Attwood, Belnap — full citations in
[`docs/STATUS.md`](docs/STATUS.md#references) and
`isabelle/document/root.bib`.
