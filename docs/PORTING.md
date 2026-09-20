# Isabelle–Lean statement-level correspondence map

Role: `supplement`

Lifecycle: `active`

Lean/static audit: 2026-09-20

Isabelle/PDF receipt: 2026-09-20 (Isabelle2025-2, 35-theory session; full
`sh verify.sh` run)

This manually curated map links 35 Isabelle theory units to 34 Lean modules.
It documents selected definitions, structures, concrete models, countermodels,
and named headline statements used by `README.md` and `STATUS.md`. It does not
assert semantic equivalence of complete modules: there is no verified
translation or cross-foundational equivalence proof. Same-name checks provide
traceability, while corresponding statements require human inspection.
Two infrastructure theories, `FiniteLogics` and `Catuskoti`,
share `BuddhistComparativeLogic/Core/Foundation.lean`; the other theories each have a corresponding
Lean module.  `BuddhistComparativeLogic/Release.lean` contains the author-reviewed release set,
`BuddhistComparativeLogic/Experimental.lean` contains the source-review queue, and
`BuddhistComparativeLogic.lean` imports both sets as the complete research tree.

Four Lean-only interfaces sit outside the map below:
`BuddhistComparativeLogic/Buddhist/HeartSutra/AssumptionAudit.lean`,
`BuddhistComparativeLogic/Buddhist/HeartSutra/PathDynamics.lean`, `BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/Antidote.lean`, and
`BuddhistComparativeLogic/Buddhist/Madhyamaka/EmptinessInference.lean`. They are documented in
[`LEAN_PROGRESS.md`](LEAN_PROGRESS.md).
The antidote module's dynamics are outside the current 35-theory session,
so it is classified as a Lean-only extension together with the remaining
three modules.

Four Lean-only argument modules are `BuddhistComparativeLogic/Buddhist/Madhyamaka/DependentOrigination.lean`,
`BuddhistComparativeLogic/Buddhist/Madhyamaka/Prasanga.lean`, `BuddhistComparativeLogic/Buddhist/Pramana/InferenceScope.lean`, and
`BuddhistComparativeLogic/Buddhist/Madhyamaka/CessationArgument.lean`. These are Lean-only reconstructions and
audits, documented with source passages in [`ARGUMENTS.md`](ARGUMENTS.md).

Sixteen Lean-only modules cover logic, argument, and text-alignment interfaces
without changing the Isabelle map:

- `BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceModes.lean`, `BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceCoverage.lean`, and
  `BuddhistComparativeLogic/Buddhist/Madhyamaka/FourfoldCausation.lean` separate kinds and scopes of dependence
  and state the premises used by the fourfold causal argument.
- `BuddhistComparativeLogic/Buddhist/HeartSutra/BeliefRevision.lean`, `BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/CognitiveAntidote.lean`,
  `BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/AntidoteSelection.lean`, and `BuddhistComparativeLogic/Buddhist/HeartSutra/ArgumentPipeline.lean`
  make the cognitive update and the bridges from formal conclusions to a
  bounded path explicit assumptions.
- `BuddhistComparativeLogic/Core/FDECalculus.lean`, `BuddhistComparativeLogic/Core/UniversalDesignationMore.lean`, and
  `BuddhistComparativeLogic/Core/Ineffable.lean` add sound-and-complete natural deduction and
  analytic tableaux, the K3/LP universal-designation cases,
  and a generic absorbing-ineffable analysis with its stated provisos.
- `BuddhistComparativeLogic/Comparative/Jaina/NayaDynamics.lean`, `BuddhistComparativeLogic/Buddhist/Pramana/Momentariness.lean`,
  `BuddhistComparativeLogic/Buddhist/Pramana/ApohaFeatures.lean`, `BuddhistComparativeLogic/Buddhist/Madhyamaka/GamanaIntervals.lean`,
  `BuddhistComparativeLogic/Buddhist/Yogacara/VimsatikaModels.lean`, and `BuddhistComparativeLogic/Buddhist/HeartSutra/RecensionAlignment.lean`
  add conditional dynamic, temporal, hierarchical, model-comparison, and
  structural-alignment results.  The last checks bounded GRETIL/Silk central
  spans and the source-order reversal while keeping philosophical construal
  independent of lexical validation.

Five Lean-only modules cover premise and selection interfaces without changing
the Isabelle map:

- `BuddhistComparativeLogic/Buddhist/Madhyamaka/SupportingArguments.lean` composes scoped dependence, the
  Dharmakīrti inference interface, fourfold causation, and two-truths
  consistency while retaining countermodels to invalid scope changes.
- `BuddhistComparativeLogic/Buddhist/HeartSutra/PremiseCertificates.lean` separates citation metadata from a
  proof-bearing premise certificate and connects certified inputs to bounded
  release.  Its shipped internal locators resolve as Lean declaration names;
  external locators remain unchecked annotations, and the fourfold certificate
  includes event occurrence.
- `BuddhistComparativeLogic/Core/MatrixTransport.lean` proves invariance of ordinary, positive
  universal, and unrestricted universal consequence under an explicit matrix
  isomorphism, with a truth/falsity-bit FDE presentation as a checked instance.
- `BuddhistComparativeLogic/Buddhist/Pramana/DirectedMomentariness.lean` replaces two-way continuity by
  backward-only rooted effect transport and proves the weakening strict.  It
  reuses the existing theory record, including its unused two-times field.
- `BuddhistComparativeLogic/Buddhist/Pramana/ApohaSelection.lean` makes admissibility, comparison, optimality,
  and antisymmetry explicit and separates unique selection from tied cases.

Four Lean-only modules consolidate pramāṇa and Yogācāra without
changing the Isabelle map:

- `BuddhistComparativeLogic/Buddhist/Pramana/PramanaSynthesis.lean` separates subject-level soundness from the
  comparison example needed for the three marks and wheel classification.
- `BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraSynthesis.lean` formalizes a conditional three-nature
  analysis, seed trajectories, and transformation, with finite boundary
  models.
- `BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraConsciousness.lean` treats the eight consciousnesses as
  functional roles and makes store support and projected duality explicit
  premises.
- `BuddhistComparativeLogic/Buddhist/Yogacara/PramanaYogacara.lean` connects observational adequacy to the
  Dharmakīrti interface and constructs ontology and cardinality defeaters.

See [`PRAMANA_YOGACARA.md`](PRAMANA_YOGACARA.md) for the combined audit.

One Lean-only module consolidates the catuṣkoṭi,
K3, and FDE semantics:

- `BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean` constructs K3 as the exact non-glut FDE
  submatrix, proves the restricted consequence equivalence and strict
  unrestricted direction, computes the corner image, and distinguishes
  universal from existential set classification.

See [`CATUSKOTI_K3_FDE.md`](CATUSKOTI_K3_FDE.md) for that audit.

Four Lean-only modules reconstruct selected proof architectures from
major Buddhist epistemological works and their later proof tradition:

- `BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean` separates perceptual evidence,
  subject-level warrants, public marked arguments, and an optional classical
  extensional apoha selector;
- `BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean` makes operational reliability, causal
  efficacy, intrinsic and effect reasons, and public comparison explicit;
- `BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean` packages the existence-to-efficacy and
  efficacy-to-momentariness steps while isolating the additional temporal
  premises; and
- `BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean` represents selected topic refutations as
  individually scoped debate certificates and audits their composition.

[`PRAMANA_TREATISES.md`](PRAMANA_TREATISES.md) records the theorem boundaries
and source orientation.  These modules do not claim chapter-by-chapter or
verse-by-verse textual coverage.

Four Lean-only modules cover these inference interfaces:

- `BuddhistComparativeLogic/Comparative/Nyaya/Nyaya.lean` separates a five-member public presentation from its
  subject-reason and pervasion proof;
- `BuddhistComparativeLogic/Buddhist/Yogacara/Alambanapariksa.lean` audits causal production and image
  similarity as independent intentional-object conditions;
- `BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Debate.lean` gives a commitment-ledger transition system
  with strategy-relative finite termination; and
- `BuddhistComparativeLogic/Buddhist/Pramana/OtherMinds.lean` uses observationally equivalent behaviour models
  to delimit a behaviour-to-volition inference.

[`INFERENCE_DEBATE.md`](INFERENCE_DEBATE.md) records their theorem and
countermodel boundaries.

Six comparative Lean-only modules cover proof interfaces across Indian,
Tibetan, and early Chinese traditions:

- `BuddhistComparativeLogic/Buddhist/Pramana/SvatantraPrasanga.lean` separates semantic proof, an opponent's
  premise commitments, and consequence refutation;
- `BuddhistComparativeLogic/Comparative/ChineseThought/MohistCanons.lean` models standards, kind extension, and the gap
  between syntactic parallelism and semantic relevance;
- `BuddhistComparativeLogic/Comparative/Nyaya/Tattvacintamani.lean` refines pervasion with reflection,
  countercondition diagnosis, and repaired inference;
- `BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaEpistemology.lean` represents initial entitlement,
  defeaters, postulation, non-cognition, and irreducibility tests;
- `BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Definitions.lean` distinguishes a definition's basis,
  coextension, and intensional constraint; and
- `BuddhistComparativeLogic/Buddhist/Pramana/Sambandhapariksa.lean` separates primitive binary relatedness
  from a reified connector and makes collapse or regress assumptions explicit.

[`COMPARATIVE_LOGIC.md`](COMPARATIVE_LOGIC.md) records the positive theorems,
finite boundaries, and historical scope of these reconstructions.

Six comparative Lean-only modules cover debate and cross-tradition interfaces:

- `BuddhistComparativeLogic/Buddhist/Pramana/Vadanyaya.lean` separates truth, proof adequacy, and the
  procedural outcome of an asymmetric debate;
- `BuddhistComparativeLogic/Buddhist/Yogacara/Sahopalambha.lean` separates co-observation, observational
  nonseparation, and numerical identity;
- `BuddhistComparativeLogic/Buddhist/Madhyamaka/Ekanekaviyoga.lean` makes the one-or-many exhaustiveness and
  composition bridges explicit;
- `BuddhistComparativeLogic/Buddhist/Abhidharma/Yamaka.lean` computes the four possible bilateral extension
  relations and retains failed-inclusion witnesses;
- `BuddhistComparativeLogic/Comparative/ChineseThought/WhiteHorse.lean` separates extension inclusion from identities
  of names, meanings, and feature requests; and
- `BuddhistComparativeLogic/Comparative/Skepticism/Jayarasi.lean` audits circular definitional support and the move
  from finite observations to global pervasion.

Six comparative Lean-only modules cover pervasion, person, definition,
mereology, and language:

- `BuddhistComparativeLogic/Buddhist/Pramana/Vyaptinirnaya.lean`, which distinguishes observed concomitance
  from globally licensed pervasion;
- `BuddhistComparativeLogic/Buddhist/Abhidharma/Pudgala.lean`, which separates conventional personal continuity
  from an immutable additional substance;
- `BuddhistComparativeLogic/Comparative/Jaina/JainaInference.lean`, which gives a modal audit of
  `anyathānupapatti` and two-member inference;
- `BuddhistComparativeLogic/Comparative/Vedanta/Sriharsa.lean`, which checks bounded definition defects and
  separates accidental truth from reliable cognition;
- `BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Fazang/Mereology.lean`, which states explicit conditions for
  rafter-and-house dependence while retaining part distinction; and
- `BuddhistComparativeLogic/Comparative/Grammar/Bhartrhari.lean`, which indexes signification by vocabulary and
  stage so that local unsignifiability is not confused with an absolute one.

Six comparative Lean-only modules cover absence, sentence meaning, inference,
awareness, grammar, and reconciliation:

- `BuddhistComparativeLogic/Comparative/Nyaya/NavyaNyayaAbsence.lean`, which types an absence by its locus,
  counterpositive, delimiter, and relation and separates bare non-cognition
  from a scoped absence certificate;
- `BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaSentenceMeaning.lean`, which compares bounded
  `abhihitānvaya` and `anvitābhidhāna` composition interfaces without
  identifying them;
- `BuddhistComparativeLogic/Comparative/Nyaya/Nyayakusumanjali.lean`, which audits the route from effecthood to
  an intelligent maker while leaving uniqueness, omniscience, and eternity
  as additional claims;
- `BuddhistComparativeLogic/Buddhist/Yogacara/Svasamvedana.lean`, which connects reflexive presentation and
  trace persistence to later memory attribution without deriving a lasting
  self;
- `BuddhistComparativeLogic/Comparative/Grammar/PaniniDerivation.lean`, which separates rank-based termination,
  priority selection, and uniqueness of normal form; and
- `BuddhistComparativeLogic/Buddhist/KoreanBuddhism/WonhyoHwajaeng.lean`, which reconstructs reconciliation as a
  compatibility-and-coverage problem for scoped local theories.

Six comparative Lean-only modules cover causation, change, interpretation,
negation, and sensory comparison:

- `BuddhistComparativeLogic/Comparative/Samkhya/Satkaryavada.lean`, which separates production, causal capacity,
  and latent preexistence;
- `BuddhistComparativeLogic/Comparative/Jaina/JainaChange.lean`, which separates mode origination and decay
  from the duration of a carrier;
- `BuddhistComparativeLogic/Buddhist/Hermeneutics/Vyakhyayukti.lean`, which packages five commentary obligations
  and their compositional use;
- `BuddhistComparativeLogic/Buddhist/Pramana/AnupalabdhiKinds.lean`, which compiles the eleven typed
  non-apprehension deployment shapes in the selected *Nyāyabindu* 2.31–42
  passage under explicit side conditions;
- `BuddhistComparativeLogic/Comparative/ChineseThought/HardWhite.lean`, which distinguishes sensory access profiles
  from numerically distinct bearers or substances; and
- `BuddhistComparativeLogic/Buddhist/Madhyamaka/NegandumCalibration.lean`, which gives a Gelug/Tsongkhapa-inspired
  check of an object of negation for overreach and underreach.

Six comparative Lean-only modules cover predicate comparison, perception,
tarka, analysis, acceptance, and priority:

- `BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/BsdusGrwa.lean`, which classifies two predicates from explicit
  witnesses for the four positive and negative cells;
- `BuddhistComparativeLogic/Buddhist/Pramana/Pratyaksabhasa.lean`, which separates nonconceptuality,
  non-error, and truth in a bounded perception audit;
- `BuddhistComparativeLogic/Comparative/Nyaya/Tarka.lean`, which keeps suppositional elimination distinct from
  the independent evidence needed to settle a claim;
- `BuddhistComparativeLogic/Buddhist/Abhidharma/Analysis.lean`, which indexes conventional and ultimate
  classification by an explicit family of admissible analyses;
- `BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Xuanzang/Inference.lean`, which tracks party-relative acceptance
  and shared semantic scope in a paired-inference audit; and
- `BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaViniyoga.lean`, which separates the traditional ordering
  of application grounds from applicability, tie-breaking, and truth.

These are logical interfaces with finite countermodels rather than textual
editions.  Their theorem statements and interpretive limits are also recorded
in [`COMPARATIVE_LOGIC.md`](COMPARATIVE_LOGIC.md).

The complete Lean tree contains 115 files: 112 subject and infrastructure
modules plus three aggregates.  The 35 Isabelle units are represented
by 34 modules, and the other 78 substantive modules are Lean-only extensions.
`BuddhistComparativeLogic/Release.lean` imports 110 reviewed modules;
`BuddhistComparativeLogic/Experimental.lean` imports two modules retained for exact
source-to-formal mapping review; and
`BuddhistComparativeLogic.lean` imports both. The table below defines the current
35-theory Isabelle-to-Lean alignment.

This is a manually documented statement-level correspondence, not a verified
semantic equivalence or declaration-for-declaration translation.
Small Isabelle helper lemmas may be folded into Lean proofs,
Isabelle locales become explicit structures or namespaces, and Nitpick
regressions become checked concrete witnesses.  The source theories remain
the reference for the complete Isabelle commentary and their proof
decomposition.

| Isabelle/HOL | Lean 4 | Aligned subject |
| --- | --- | --- |
| `HeartSutra_Text.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/Text.lean` | 31 clause identifiers, text, character counts, 262-character body |
| `HeartSutra_Dharma.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/Dharma.lean` | skandhas, ayatanas, dhatus, nidanas, four truths |
| `ManyValuedLogic.thy` | `BuddhistComparativeLogic/Core/MVLogic.lean` | parametric many-valued evaluator and consequence record |
| `FiniteLogics.thy` | `BuddhistComparativeLogic/Core/Foundation.lean` | classical, FDE and FDE5 truth functions and countermodels |
| `Catuskoti.thy` | `BuddhistComparativeLogic/Core/Foundation.lean` | four corners and collapse of the fifth value at designation level |
| `HeartSutra_Emptiness.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/Emptiness.lean` | own-being, dependent origination, readings of form and emptiness |
| `HeartSutra_Path.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/Path.lean` | bodhisattva and buddha path implications |
| `HeartSutra_Mantra.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/Mantra.lean` | epithets, mantra and the formalization boundary |
| `HeartSutra_Coverage.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/Coverage.lean` | clause status and exhaustive coverage proof |
| `Madhyamaka_MMK24.thy` | `BuddhistComparativeLogic/Buddhist/Madhyamaka/MMK.lean` | MMK 15 and 24, designation and middle-way results |
| `HeartSutra_TwoTruths.thy` | `BuddhistComparativeLogic/Buddhist/Madhyamaka/TwoTruths.lean` | conventional/ultimate evaluation and local consistency |
| `HeartSutra_Connexive.thy` | `BuddhistComparativeLogic/Core/Connexive.lean` | connexive implication, Aristotle and Boethius theses |
| `PlurivalentSemantics.thy` | `BuddhistComparativeLogic/Core/Plurivalent.lean` | functional and relational plurivalent liftings |
| `isabelle/Buddhist/Pramana/Dignaga_Hetucakra.thy` | `BuddhistComparativeLogic/Buddhist/Pramana/Hetucakra.lean` | Dignaga's wheel, three marks and non-sufficiency model |
| `UniversalDesignation.thy` | `BuddhistComparativeLogic/Core/UniversalDesignation.lean` | universal designation and variable inclusion |
| `DiamondSutra_Sokuhi.thy` | `BuddhistComparativeLogic/Buddhist/Madhyamaka/Sokuhi.lean` | Diamond Sutra's is/not-is schema across readings |
| `Madhyamaka_Jizang.thy` | `BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang.lean` | fourfold two truths and semantic stabilization |
| `UniversalDesignationFDE.thy` | `BuddhistComparativeLogic/Core/UniversalDesignationFDE.lean` | universal designation over FDE and the theta formula |
| `HeartSutra_Sanskrit.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/Sanskrit.lean` | Sanskrit formulations, illusion simile and reverse identity |
| `HeartSutra_PathModel.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/PathModel.lean` | concrete grasping model for the path chain |
| `HeartSutra_Anumana.thy` | `BuddhistComparativeLogic/Buddhist/Pramana/Anumana.lean` | emptiness as Dignaga-style inference |
| `Madhyamaka_MMK1.thy` | `BuddhistComparativeLogic/Buddhist/Madhyamaka/MMK1.lean` | fourfold non-arising and modus-tollens comparison |
| `FiniteDecisionProcedures.thy` | `BuddhistComparativeLogic/Core/Decide.lean` | executable finite-matrix checkers and correctness proofs |
| `Dharmakirti_Reasons.thy` | `BuddhistComparativeLogic/Buddhist/Pramana/Dharmakirti.lean` | three kinds of reason and pervasion |
| `Avyakata.thy` | `BuddhistComparativeLogic/Buddhist/EarlyBuddhism/Avyakata.lean` | fourteen unanswered questions at formula/designation levels |
| `Madhyamaka_StandpointSemantics.thy` | `BuddhistComparativeLogic/Buddhist/Madhyamaka/Standpoints.lean` | standpoint frames, two/three truths and Prasangika |
| `Madhyamaka_Vigrahavyavartani.thy` | `BuddhistComparativeLogic/Buddhist/Madhyamaka/Vigraha.lean` | self-applicable emptiness and the no-thesis model |
| `FDEProofTheory.thy` | `BuddhistComparativeLogic/Core/FDEProof.lean` | relevance, containment and signed-literal decision procedures |
| `HeartSutra_LongerRecension.thy` | `BuddhistComparativeLogic/Buddhist/HeartSutra/Longer.lean` | longer-recension speech frame and samadhi standpoint |
| `Jaina_Saptabhangi.thy` | `BuddhistComparativeLogic/Comparative/Jaina/Saptabhangi.lean` | Jaina sevenfold predication as the comparative case |
| `Dignaga_Apoha.thy` | `BuddhistComparativeLogic/Buddhist/Pramana/Apoha.lean` | exclusion, revision cycles, and an equivalence-class grounding interface whose causal interpretation is external |
| `Yogacara_Vimsatika.thy` | `BuddhistComparativeLogic/Buddhist/Yogacara/Vimsatika.lean` | consciousness-only models and the atomism dilemma |
| `Sarvastivada_ThreeTimes.thy` | `BuddhistComparativeLogic/Buddhist/Abhidharma/Sarvastivada.lean` | four accounts of temporal presence |
| `Madhyamaka_Gamana.thy` | `BuddhistComparativeLogic/Buddhist/Madhyamaka/Gamana.lean` | MMK 2, path partition and motion over linear orders |
| `ManyValuedLogicExample.thy` | `BuddhistComparativeLogic/Core/MVExample.lean` | strong Kleene K3 extension example |

The translations use a few deliberate representation changes:

- Isabelle locales become Lean structures with explicit arguments.  This
  keeps assumptions visible at theorem sites and gives each structure a
  concrete inhabitant or model.
- Isabelle sets become predicates when only membership matters, and finite
  lists when executable enumeration matters.
- Isabelle/HOL types are inhabited by construction.  A few Lean theorems
  therefore state `[Nonempty α]` explicitly when the empty type would make
  the corresponding claim false.
- Isabelle's `by eval` and Nitpick checks become `decide` proofs or named
  valuations.  Lean checks those witnesses in the same kernel run as the
  universal theorems.

The 2026-09-20 full verification covered all 115 Lean files and built the
Isabelle2025-2 35-theory session and PDF.  Run `sh verify.sh` from the
repository root to reproduce the complete receipt; `sh tools/check-lean.sh`
reproduces the Lean-only stage.  The checker
finds the local import graph, compiles every module with warnings treated as
errors, rejects admitted declarations, and writes all build artefacts to a
temporary directory.  A conventional `lake build` is also available from
this directory through `lakefile.toml` and `lean-toolchain`.
