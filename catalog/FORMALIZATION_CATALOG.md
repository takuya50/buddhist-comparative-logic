<!-- SPDX-License-Identifier: CC0-1.0 -->

# Formalization catalogue

This generated catalogue gives every Lean module a public boundary: its target,
formal scope, explicit-assumption policy, historical-source status, and release
status.  Mechanical facts come from the source files; interpretive judgments
come from `catalog/catalog_annotations.json`.  Regenerate with
`python3 tools/make_formalization_catalog.py`.

The labels are deliberately conservative:

- `passage_aligned` identifies a passage or adopted witness, but does not imply
  that the cited edition or interpretation is uncontested;
- `work_level` names a work or argument family without a theorem-to-passage map;
- `unverified` records missing passage-level evidence and is never filled by guesswork;
- `not_applicable` is used for pure logic and import infrastructure.

Source IDs resolve in [`sources/registry.json`](../sources/registry.json).  The
software-release boundary is explained in
[`RELEASE_SCOPE.md`](../docs/RELEASE_SCOPE.md).  Exact theorem statements remain in the
linked Lean files; the catalogue records their names and counts in
[`formalizations.json`](formalizations.json).

## Inventory populations

Historical-source statuses are counted separately for ordinary modules and
aggregate import files; they are not a common denominator of subject coverage.

| Population | Total | Passage-aligned | Work-level | Not applicable |
| --- | ---: | ---: | ---: | ---: |
| Ordinary modules | 112 | 25 | 68 | 19 |
| Aggregate imports | 3 | 0 | 0 | 3 |

The declaration totals are lexical counts, not measures of mathematical depth.

## Aggregates (3)

### [`BuddhistComparativeLogic.Experimental`](../lean/BuddhistComparativeLogic/Experimental.lean)

- **Target:** Experimental aggregate
- **Formal scope:** These two modules compile and contain checked proofs and countermodels, but their formal predicates still lack a sufficiently exact passage-level mapping. See `docs/RELEASE_SCOPE.md` for the specific remaining evidence gap in each case.
- **Assumption boundary:** No theorem-level assumptions; this file is an import boundary.
- **Checked inventory:** 0 definitions/types, 0 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `aggregate`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** Import convenience only; consult the imported modules for claims.
- **Release:** `source_review_aggregate`. Documentation: [README.md](../README.md), [docs/RELEASE_SCOPE.md](../docs/RELEASE_SCOPE.md).

### [`BuddhistComparativeLogic.Release`](../lean/BuddhistComparativeLogic/Release.lean)

- **Target:** Release-candidate aggregate
- **Formal scope:** This aggregate imports the 110 author-reviewed subject and infrastructure modules. This is the sole author's self-review, not independent or external peer review. The source status, formal mapping, assumption boundary, and claim limit of each module are recorded in `catalog/FORMALIZATION_CATALOG.md`.  Inclusion makes no claim that a historical interpretation is exhaustive or uncontested.
- **Assumption boundary:** No theorem-level assumptions; this file is an import boundary.
- **Checked inventory:** 0 definitions/types, 0 theorems/lemmas, 0 examples; imports 110 direct module(s).
- **Provenance:** `aggregate`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** Import convenience only; consult the imported modules for claims.
- **Release:** `release_candidate_aggregate`. Documentation: [README.md](../README.md), [docs/RELEASE_SCOPE.md](../docs/RELEASE_SCOPE.md).

### [`BuddhistComparativeLogic`](../lean/BuddhistComparativeLogic.lean)

- **Target:** Buddhist and comparative Asian logic
- **Formal scope:** This is the aggregate import for the Lean 4 port and its extensions.  Its transitive import closure contains the counterpart of every theory in the Isabelle `Buddhist_Comparative_Logic` session together with 78 Lean-only modules; see `docs/PORTING.md` for the theory-by-theory map and `docs/LEAN_PROGRESS.md` for the additional argument interfaces.
- **Assumption boundary:** No theorem-level assumptions; this file is an import boundary.
- **Checked inventory:** 0 definitions/types, 0 theorems/lemmas, 0 examples; imports 100 direct module(s).
- **Provenance:** `aggregate`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** Import convenience only; consult the imported modules for claims.
- **Release:** `full_research_aggregate`. Documentation: [README.md](../README.md), [docs/RELEASE_SCOPE.md](../docs/RELEASE_SCOPE.md).

## Logic/Core (14)

### [`BuddhistComparativeLogic.Core.CatuskotiK3FDE`](../lean/BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean)

- **Target:** Catuṣkoṭi, K3, and FDE
- **Formal scope:** This module makes precise a limited algebraic comparison.  Strong Kleene K3 is the `T/N/F` (non-glut) submatrix of FDE.  The embedding preserves the connectives, formula evaluation, designation, and the catuṣkoṭi classifier. Consequently, K3 consequence is exactly FDE consequence restricted to valuations with no `B` values.  Unrestricted FDE consequence is strictly weaker, as the familiar contradiction countermodel shows.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 3 definitions/types, 27 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `priest-2010`, `priest-2018`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/CATUSKOTI_K3_FDE.md](../docs/CATUSKOTI_K3_FDE.md).

### [`BuddhistComparativeLogic.Core.Connexive`](../lean/BuddhistComparativeLogic/Core/Connexive.lean)

- **Target:** A connexive reading of 「不生不滅」
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Connexive.thy`.  Truth and falsity are tracked independently.  The connexive conditional is compared with FDE's material conditional, including the bivalent result that turns the pair of negated conditionals into absence of own-being.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 12 definitions/types, 9 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Connexive`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.Decide`](../lean/BuddhistComparativeLogic/Core/Decide.lean)

- **Target:** Executable decision procedures for the three-atom fragment
- **Formal scope:** Lean counterpart of `isabelle/Core/FiniteDecisionProcedures.thy`.  The checkers enumerate 8 classical, 64 FDE, and 125 FDE5 valuations.  Their correctness theorems connect finite Boolean computation back to quantification over all three-atom valuations.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 8 definitions/types, 18 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `FiniteDecisionProcedures`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.FDECalculus`](../lean/BuddhistComparativeLogic/Core/FDECalculus.lean)

- **Target:** Sound and complete proof calculi for FDE and FDE5
- **Formal scope:** There are two layers. `Deriv` is the familiar lattice/De Morgan natural deduction presentation and is proved sound and complete through a finite disjunctive normal form. `Tableau` is an analytic signed tableau whose proof objects close every counterexample branch produced by the connective rules. It is also proved sound and complete. `Tableau5` adds the atom-containment obligation exactly required by the absorbing fifth value.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 20 definitions/types, 60 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `belnap-1977`, `dunn-1976`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Core.FDEProof`](../lean/BuddhistComparativeLogic/Core/FDEProof.lean)

- **Target:** Proof theory for FDE and FDE5
- **Formal scope:** This is the Lean counterpart of `isabelle/Core/FDEProofTheory.thy`.  It proves the variable-sharing theorem for FDE, characterizes Priest's absorbing five-valued logic as FDE plus atom containment, and gives an executable signed-literal decision procedure for formulas over any decidable atom type.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 31 definitions/types, 47 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `FDEProofTheory`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`, `belnap-1977`, `dunn-1976`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.Foundation`](../lean/BuddhistComparativeLogic/Core/Foundation.lean)

- **Target:** Core finite logic layer
- **Formal scope:** A self-contained Lean 4 port of the parts of the Isabelle session `Buddhist_Comparative_Logic` that carry the logical content: the formula type, the Belnap-Dunn four-valued semantics, Priest's absorbing fifth value, and the results the rest of the session leans on.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 36 definitions/types, 41 theorems/lemmas, 0 examples; imports 0 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `FiniteLogics`, `Catuskoti`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`, `priest-2010`, `priest-2018`, `belnap-1977`, `dunn-1976`, `anderson-belnap-1962`, `ferguson-2016-faulty`, `ciuni-szmuc-ferguson-2018`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.Ineffable`](../lean/BuddhistComparativeLogic/Core/Ineffable.lean)

- **Target:** An absorbing ineffable value over an arbitrary many-valued base
- **Formal scope:** This module adjoins one undesignated, operation-absorbing value to any `MVLogic`.  It proves two exact boundary theorems.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 13 definitions/types, 34 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Core.MVExample`](../lean/BuddhistComparativeLogic/Core/MVExample.lean)

- **Target:** Worked example: adding strong Kleene K3
- **Formal scope:** Lean counterpart of `isabelle/Core/ManyValuedLogicExample.thy`.  This has no doctrinal content; it demonstrates the reusable many-valued interface and isolates the glut that separates K3 from FDE.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 9 definitions/types, 5 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `ManyValuedLogicExample`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.MVLogic`](../lean/BuddhistComparativeLogic/Core/MVLogic.lean)

- **Target:** Generic many-valued propositional logic
- **Formal scope:** Lean counterpart of `isabelle/Core/ManyValuedLogic.thy`.  The carrier and its designated values are explicit data, mirroring an Isabelle locale without committing the rest of the development to a global type-class instance.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 13 definitions/types, 5 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `ManyValuedLogic`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`, `belnap-1977`, `dunn-1976`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.MatrixTransport`](../lean/BuddhistComparativeLogic/Core/MatrixTransport.lean)

- **Target:** Transporting universal designation across explicit finite matrices
- **Formal scope:** The remaining instance-classification problem should not depend on the names chosen for truth values.  This module records the exact data required for two many-valued matrices to be isomorphic and proves that ordinary consequence, positive universal designation, and unrestricted universal designation are all invariant under that data.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 9 definitions/types, 22 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Core.Plurivalent`](../lean/BuddhistComparativeLogic/Core/Plurivalent.lean)

- **Target:** Plurivalent semantics
- **Formal scope:** Lean counterpart of `isabelle/Core/PlurivalentSemantics.thy`.  Sets are represented by their membership predicates (`PSet α = α → Prop`), which keeps the image semantics literal while requiring no set library.  The functional and relational liftings are compared explicitly, and Priest's absorbing value is recovered as the empty-set case.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 17 definitions/types, 55 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `PlurivalentSemantics`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.UniversalDesignation`](../lean/BuddhistComparativeLogic/Core/UniversalDesignation.lean)

- **Target:** Universal designation over the classical base
- **Formal scope:** Lean counterpart of `isabelle/Core/UniversalDesignation.thy`.  General plurivalent designation is universal: a formula is designated when every value it has is designated, including the empty value set vacuously.  The resulting classical logic is represented by the `T/E`-designated FDE5 matrix and characterized by K3 consequence after discarding premises with variables absent from the conclusion.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 17 definitions/types, 24 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `UniversalDesignation`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.UniversalDesignationFDE`](../lean/BuddhistComparativeLogic/Core/UniversalDesignationFDE.lean)

- **Target:** Universal designation over FDE
- **Formal scope:** Lean counterpart of `isabelle/Core/UniversalDesignationFDE.thy`.  The first half is uniform in the chosen many-valued base: unrestricted universal designation reduces to positive plurivalence after retaining only premises whose atoms occur in the conclusion.  The second half verifies Priest's `theta` map for FDE and thereby reduces positive plurivalent FDE back to ordinary FDE.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 2 definitions/types, 34 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `UniversalDesignationFDE`.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: `internal-isabelle-port`. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Core.UniversalDesignationMore`](../lean/BuddhistComparativeLogic/Core/UniversalDesignationMore.lean)

- **Target:** Universal designation over K3 and LP
- **Formal scope:** This module completes the two three-valued cases of universal plurivalent designation.  Positive universal K3 consequence collapses to ordinary K3. Positive universal LP consequence instead collapses to FDE: a nonempty LP value set containing both classical values behaves as an FDE gap.  The generic variable-inclusion theorem then gives the unrestricted consequence relations.
- **Assumption boundary:** Carriers, operations, designated values, valuations, and finite enumerations are explicit parameters or data.
- **Checked inventory:** 8 definitions/types, 37 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** A mathematical semantics or proof tool; it does not select a historical interpretation by itself.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

## Heart Sutra (15)

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.ArgumentPipeline`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/ArgumentPipeline.lean)

- **Target:** Composing the philosophical and practical arguments
- **Formal scope:** The earlier modules prove the stages separately.  This file states the two bridges required to compose them: recognition turns a proved absence of own-being into an initial cognitive insight, and a revision policy turns that insight into a bounded change of grasping, fear and suffering.  Keeping both bridges as fields prevents an ontological conclusion from silently becoming a psychological law.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 2 definitions/types, 9 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.AssumptionAudit`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/AssumptionAudit.lean)

- **Target:** What the emptiness and two-truths conclusions depend on
- **Formal scope:** Lean-only audit, not an additional translation of a sutra clause. Independent predicates expose the bridge from dependence to absence of own-being. The FDE results isolate the local consistency conditions from the number of evaluation points. None of these results selects a philological reading.
- **Assumption boundary:** Named interfaces and certificates carry every premise consumed by the composition or transport theorem.
- **Checked inventory:** 11 definitions/types, 15 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** The interface checks composition; it does not independently justify historical, causal, or empirical inputs.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.BeliefRevision`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/BeliefRevision.lean)

- **Target:** Evidence-sensitive belief revision
- **Formal scope:** This Lean-only model separates support for own-being from counterevidence for emptiness.  Grasping is the positive balance of the former over the latter. Consequently, contraction is derived from three explicit update conditions: support does not increase, admitted counterevidence is retained, and one new unit is assimilated while the own-being belief is still accepted.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 18 definitions/types, 13 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.Coverage`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/Coverage.lean)

- **Target:** Coverage theorem
- **Formal scope:** The Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Coverage.thy`.  Every clause is classified as defined, proved, or explicitly noted; `Missing` is never assigned.
- **Assumption boundary:** The adopted witness, segmentation, alignment, or speech-act classification is explicit data.
- **Checked inventory:** 3 definitions/types, 21 theorems/lemmas, 0 examples; imports 4 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Coverage`.
- **Historical status:** `passage_aligned`; primary: `t251-project-received-262`, `t251-cbeta-pinned`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** The project witness is not a critical edition, and textual alignment does not establish doctrinal truth.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.Dharma`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/Dharma.lean)

- **Target:** Dharma-structure layer
- **Formal scope:** This module ports `isabelle/Buddhist/HeartSutra/HeartSutra_Dharma.thy`: the five skandhas, twelve ayatanas, eighteen dhatus, twelve nidanas, and four truths.  Each finite type has an explicit exhaustive, duplicate-free list.  In bare Lean these lists are also the constructive witnesses for the standard cardinalities.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 21 definitions/types, 15 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Dharma`.
- **Historical status:** `work_level`; primary: `t251-project-received-262`, `t251-cbeta-pinned`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.Emptiness`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/Emptiness.lean)

- **Target:** Emptiness, dependent origination, and readings of HS06--HS10
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Emptiness.thy`.  As in the Isabelle development, all doctrinal results are conditional on the fields of `Emptiness`; the structure is a reconstruction of the sutra's claims, not evidence for those claims.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 25 definitions/types, 29 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Emptiness`.
- **Historical status:** `work_level`; primary: `t251-project-received-262`, `t251-cbeta-pinned`; secondary/formal: `internal-isabelle-port`, `attwood-2017`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.Longer`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/Longer.lean)

- **Target:** The longer Heart Sutra recension
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_LongerRecension.thy`.  It records the six-part narrative frame, separates speech acts from assertoric content, and realizes the silent samādhi and the speaking scene as two standpoints.
- **Assumption boundary:** The adopted witness, segmentation, alignment, or speech-act classification is explicit data.
- **Checked inventory:** 14 definitions/types, 14 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_LongerRecension`.
- **Historical status:** `work_level`; primary: `t251-cbeta-pinned`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** The project witness is not a critical edition, and textual alignment does not establish doctrinal truth.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.Mantra`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/Mantra.lean)

- **Target:** The mantra and its epithets
- **Formal scope:** This is the Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Mantra.thy`.  Invocation is represented as a distinct kind of utterance, so the model records explicitly that the heart mantra is not a truth-apt formula.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 6 definitions/types, 4 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Mantra`.
- **Historical status:** `work_level`; primary: `t251-project-received-262`, `t251-cbeta-pinned`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.Path`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/Path.lean)

- **Target:** The path clauses HS20--HS26
- **Formal scope:** This is the explicit-record counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Path.thy`.  Its implication fields are the sutra's own claims.  The theorems below establish only that those implications compose.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 3 definitions/types, 4 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Path`.
- **Historical status:** `work_level`; primary: `t251-project-received-262`, `t251-cbeta-pinned`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.PathDynamics`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/PathDynamics.lean)

- **Target:** A conditional, quantitative path model
- **Formal scope:** Lean-only extension. Insight, grasping, fear and suffering are independent observations on a state. The natural numbers are abstract ranks, not measured psychological quantities. Update laws are explicit modeling hypotheses; they are not consequences of the sutra or empirical evidence for it.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 14 definitions/types, 15 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.PathModel`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/PathModel.lean)

- **Target:** A grasping model for the path layer
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_PathModel.thy`.  The model derives the eight path conditions from predicates for grasping, seeing emptiness, and impermanence.  The only substantive bridge field is that a dharma seen as empty is not grasped.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 10 definitions/types, 8 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_PathModel`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.PremiseCertificates`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/PremiseCertificates.lean)

- **Target:** Premise certificates for the argument-to-practice pipeline
- **Formal scope:** The end-to-end arguments deliberately leave historical, philosophical, and empirical premises exposed.  This module adds a provenance-bearing interface without pretending that a citation establishes its claim.  `CitedClaim P` stores only metadata and is inhabited even when `P` is false.  `Certified P` also contains a Lean proof of `P`; only certified premises enter the soundness theorems below.
- **Assumption boundary:** Named interfaces and certificates carry every premise consumed by the composition or transport theorem.
- **Checked inventory:** 14 definitions/types, 18 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** The interface checks composition; it does not independently justify historical, causal, or empirical inputs.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.RecensionAlignment`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/RecensionAlignment.lean)

- **Target:** Edition-parametric recension alignment
- **Formal scope:** This module separates structural alignment from philological identity.  An `Alignment` can certify that source-unit identifiers cover target units, behave as a function, and preserve order without asserting any source string, translation, token count, or preferred reading.  Lexical evidence is a separate, explicitly partial layer: absent Sanskrit or Tibetan witnesses produce proof obligations rather than axioms.
- **Assumption boundary:** The adopted witness, segmentation, alignment, or speech-act classification is explicit data.
- **Checked inventory:** 66 definitions/types, 45 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `gretil-heart-sanskrit`, `silk-1994-heart-sutra`; secondary/formal: none registered. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** The project witness is not a critical edition, and textual alignment does not establish doctrinal truth.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.Sanskrit`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/Sanskrit.lean)

- **Target:** Sanskrit HS06--HS07 and the illusion reading
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Sanskrit.thy`.  It adds Attwood's `mayopama` reading and isolates the conventional-appearance premise needed for the converse "emptiness is form".
- **Assumption boundary:** The adopted witness, segmentation, alignment, or speech-act classification is explicit data.
- **Checked inventory:** 6 definitions/types, 12 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Sanskrit`.
- **Historical status:** `passage_aligned`; primary: `gretil-heart-sanskrit`; secondary/formal: `internal-isabelle-port`, `attwood-2017`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** The project witness is not a critical edition, and textual alignment does not establish doctrinal truth.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.HeartSutra.Text`](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/Text.lean)

- **Target:** Text layer: the 262-character recension segmented into clauses
- **Formal scope:** This is the Lean 4 counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Text.thy`.  The Chinese source text remains in the prose documentation; this module records its clause structure, the transmitted-form character counts, its two explicit elisions, and the interlocutor annotations.
- **Assumption boundary:** The adopted witness, segmentation, alignment, or speech-act classification is explicit data.
- **Checked inventory:** 7 definitions/types, 6 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Text`.
- **Historical status:** `passage_aligned`; primary: `t251-project-received-262`, `t251-cbeta-pinned`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** The project witness is not a critical edition, and textual alignment does not establish doctrinal truth.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md), [docs/PORTING.md](../docs/PORTING.md).

## Madhyamaka (23)

### [`BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang.Antidote`](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/Antidote.lean)

- **Target:** Attachment-gated iteration of Jizang's tiers
- **Formal scope:** The central antidote dynamics, with an exact stopping criterion and an infinite-ascent counterexample added in Lean. The operation on formulas remains stipulated. Neither reduction of attachment nor silence follows merely from gating.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 4 definitions/types, 11 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang.AntidoteSelection`](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/AntidoteSelection.lean)

- **Target:** Deriving the form of Jizang's tier antidote
- **Formal scope:** The cognitive model explains when a remedy is applied.  This module first models the two members of a tier as the current attachment focus.  The conventional part of an adequate response must be a least common consequence of that focus, while the ultimate part must be interderivable with its negation.  The FDE derivation rules then select `Antidote.tstep` up to derivability, rather than assuming its two syntax-tree fields outright.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 11 definitions/types, 12 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang.CognitiveAntidote`](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/CognitiveAntidote.lean)

- **Target:** A cognitive semantics for the Jizang antidote gate
- **Formal scope:** The earlier attachment-gated iteration left its Boolean gate uninterpreted. Here a tier is grasped exactly when support for treating it as intrinsically true exceeds the admitted counterevidence.  This gives an exact cognitive stopping criterion, while leaving the Jizang formula operation unchanged.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 6 definitions/types, 14 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang`](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang.lean)

- **Target:** Jizang's fourfold two truths
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_Jizang.thy`.  The formulas grow at every tier, while their values stabilize after the first application of excluded middle in classical, FDE, and FDE5 semantics.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 9 definitions/types, 29 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Madhyamaka_Jizang`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.EarlyBuddhism.Avyakata`](../lean/BuddhistComparativeLogic/Buddhist/EarlyBuddhism/Avyakata.lean)

- **Target:** The fourteen unanswered questions
- **Formal scope:** Lean counterpart of the formula- and designation-level results in `isabelle/Buddhist/EarlyBuddhism/Avyakata.thy`.  Negating all four corners is a glut at formula level; leaving every corner undesignated is a gap (or the fifth, ineffable value).
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 10 definitions/types, 13 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Avyakata`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.CessationArgument`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/CessationArgument.lean)

- **Target:** The argument from possible cessation against fixed suffering
- **Formal scope:** Reconstruction of one argument discussed in MMK 24: suffering with a fixed unchanging nature cannot cease. Connect that reasoning to the previously checked dynamic path, without equating emptiness with a successful path. The interpretation of intrinsic suffering as unchanging along this process is an explicit criterion; no psychological law is claimed as a fact.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 2 definitions/types, 7 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/ARGUMENTS.md](../docs/ARGUMENTS.md), [docs/LEAN_PROGRESS.md](../docs/LEAN_PROGRESS.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceCoverage`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceCoverage.lean)

- **Target:** Coverage, universalization, and countermodels for dependence modes
- **Formal scope:** The local inference from a witnessed variation to absence of own-being does not by itself yield `all dharmas are empty`.  This module states the missing coverage premise for any selected collection of modes, proves the scoped and universal conclusions, and supplies finite countermodels for the converses and for cross-mode identification.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 9 definitions/types, 26 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceModes`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceModes.lean)

- **Target:** Three modes of dependence and independent criteria for own-being
- **Formal scope:** This module separates causal, mereological and conceptual dependence.  They form one indexed family, but each mode has its own contexts, support changes and manifestations.  Thus an edge in one mode is not definitionally an edge in either of the others.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 14 definitions/types, 12 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.DependentOrigination`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/DependentOrigination.lean)

- **Target:** An argument from conditional variation to absence of own-being
- **Formal scope:** Reconstruction motivated by MMK 15.1-2 and 24.18-19, not a textual identity claim. Own-being is a primitive predicate. The interpretive premise says that it entails invariance of presence across the admitted contexts. A dependency is witnessed by two contexts differing in exactly one other condition, with different presence of the subject. This derives the previous audit's exclusion law rather than assuming that law directly.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 7 definitions/types, 12 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: `siderits-katsura-2013`; secondary/formal: none registered. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/ARGUMENTS.md](../docs/ARGUMENTS.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.Ekanekaviyoga`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Ekanekaviyoga.lean)

- **Target:** A scoped reconstruction of the neither-one-nor-many reason
- **Formal scope:** This module formalizes the proof shape associated with Śāntarakṣita's `ekānekaviyogahetu`.  `Intrinsic`, `TrulyOne` and `TrulyMany` are primitive predicates on analyzed subjects.  In particular, the last two are not Lean claims about the cardinality of the carrier type.  The central conclusion requires an explicit premise that anything intrinsic falls under one of the two horns and explicit rejections of both horns.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 17 definitions/types, 16 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.EmptinessInference`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/EmptinessInference.lean)

- **Target:** Explicit pervasion in the emptiness inference
- **Formal scope:** Connect the existing Madhyamaka inference to Dharmakirti.Model, keeping exactly its subject, reason and thesis. A second adapter starts from the weaker independent-predicate model: its pervasion is precisely the exclusion law, so the bridge is visible rather than hidden in universal emptiness.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 2 definitions/types, 5 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.FourfoldCausation`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/FourfoldCausation.lean)

- **Target:** Event-level reconstruction of fourfold non-arising
- **Formal scope:** This file separates an event token from its kind and time.  In particular, a prior event of the same kind is not the very event that it produces.  The distinction prevents the rejection of self-arising from accidentally ruling out ordinary recurrence or conditional production.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 22 definitions/types, 25 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: `siderits-katsura-2013`; secondary/formal: none registered. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.Gamana`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Gamana.lean)

- **Target:** MMK II: the gone, the not-gone, and the being-gone-over
- **Formal scope:** This semantic port partitions a strict linear order around a current place, proves that the present locus is a singleton and therefore is not itself a traversed region, and keeps density as an explicit premise.  It models one formal boundary in MMK II; it is not a complete translation of the chapter.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 6 definitions/types, 9 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Madhyamaka_Gamana`.
- **Historical status:** `passage_aligned`; primary: `siderits-katsura-2013`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.GamanaIntervals`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/GamanaIntervals.lean)

- **Target:** Motion as a relation over a temporal interval
- **Formal scope:** `BuddhistComparativeLogic.Buddhist.Madhyamaka.Gamana` proves that the presently occupied place is a singleton and therefore cannot itself be traversed.  Here motion is represented positively by a trajectory relating distinct times and positions.  The trace of a nonconstant trajectory over a closed interval contains its two endpoints and is consequently traversable.  This makes the static-point result compatible with motion rather than treating a place as the bearer of motion.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 9 definitions/types, 16 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: `siderits-katsura-2013`; secondary/formal: none registered. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.MMK`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/MMK.lean)

- **Target:** MMK 15:2 and 24:18--19
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_MMK24.thy`.  Own-being is defined as the negation of dependent arising; universal dependent arising and involutive negation then derive the emptiness premise used by `Emptiness`.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 10 definitions/types, 15 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Madhyamaka_MMK24`.
- **Historical status:** `passage_aligned`; primary: `siderits-katsura-2013`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.MMK1`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/MMK1.lean)

- **Target:** MMK 1:1: fourfold non-arising
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_MMK1.thy`.  The four refutations yield formula-level non-arising in classical and FDE semantics.  FDE still admits a valuation on which arising itself is designated, and it does not in general validate the modus-tollens step used by each reductio.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 7 definitions/types, 6 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Madhyamaka_MMK1`.
- **Historical status:** `passage_aligned`; primary: `siderits-katsura-2013`; secondary/formal: `internal-isabelle-port`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.NegandumCalibration`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/NegandumCalibration.lean)

- **Target:** Calibrating an object of negation
- **Formal scope:** This module gives a restrained predicate reconstruction of the Gelug concern, especially associated with Tsongkhapa, that an object of negation must be neither too broad nor too narrow.  It does not treat this calibration as the single Tibetan interpretation of Madhyamaka.  Here `candidate x` says that the proposed content to be negated applies at `x`; it does not say that the conventional object `x` is erased.
- **Assumption boundary:** The candidate and intrinsic predicates are supplied. Extensional recovery uses classical double-negation elimination; conventional-appearance and many-valued bridges require the separately named premises.
- **Checked inventory:** 16 definitions/types, 18 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `sep-tsongkhapa-object-negation`, `garfield-thakchoe-2011-object-negation`. Secondary orientation only (sources accessed 2026-09-19): SEP section 3 and Garfield–Thakchöe identify the paired danger of over-negation/under-negation. No primary Tibetan passage or translation is claimed; TooBroad, TooNarrow, and Calibrated are project-authored extensional paraphrases.
- **Limit:** A secondary-oriented modern calibration model, not a Tibetan edition, translation, passage-aligned exegesis, or uniquely correct Gelug reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.Prasanga`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Prasanga.lean)

- **Target:** Explicit reductio obligations behind fourfold non-arising
- **Formal scope:** MMK 1.1 motivates the four cases. We expose exhaustiveness and each case's consequence as premises, not four negations presented as already proved. The target is intrinsic production; ordinary conditional occurrence is a different predicate and is not refuted by these rules.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 12 definitions/types, 18 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: `siderits-katsura-2013`; secondary/formal: none registered. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/ARGUMENTS.md](../docs/ARGUMENTS.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.Sokuhi`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Sokuhi.lean)

- **Target:** The Diamond Sutra's logic of sokuhi
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/DiamondSutra/DiamondSutra_Sokuhi.thy`: single-level classical, FDE, FDE5, and connexive readings are compared with a locally consistent two-truths reading.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 8 definitions/types, 13 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `DiamondSutra_Sokuhi`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.Standpoints`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Standpoints.lean)

- **Target:** Standpoint semantics for Buddhist two-truths readings
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_StandpointSemantics.thy`.  An assertion belongs to a standpoint rather than receiving a global truth value.  This is the small piece of structure used by the two-truths, Jizang, Vigrahavyāvartanī, and long-recension modules.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 22 definitions/types, 23 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Madhyamaka_StandpointSemantics`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.SupportingArguments`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/SupportingArguments.lean)

- **Target:** Reusable schemas for the arguments supporting emptiness
- **Formal scope:** This module composes results that were previously available only one stage at a time.  The statements keep four scopes separate:
- **Assumption boundary:** Named interfaces and certificates carry every premise consumed by the composition or transport theorem.
- **Checked inventory:** 7 definitions/types, 22 theorems/lemmas, 0 examples; imports 5 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `not_applicable`; primary: none registered; secondary/formal: none registered. No historical passage claim is made.
- **Limit:** The interface checks composition; it does not independently justify historical, causal, or empirical inputs.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.TwoTruths`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/TwoTruths.lean)

- **Target:** The two truths as two evaluation points
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_TwoTruths.thy`.  `Satya2` is shared with the standpoint semantics so later modules can combine the truth-value and assertion-level accounts without duplicate types.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 11 definitions/types, 11 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_TwoTruths`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Madhyamaka.Vigraha`](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Vigraha.lean)

- **Target:** Vigrahavyāvartanī: empty statements and “I have no thesis”
- **Formal scope:** Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_Vigrahavyavartani.thy`.  The results remain conditional on an explicit model.  Emptiness is applied to the statement itself without turning it into a truth predicate, and the no-thesis claim is located at a silent standpoint.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 13 definitions/types, 9 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Madhyamaka_Vigrahavyavartani`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

## Pramana (22)

### [`BuddhistComparativeLogic.Buddhist.Pramana.Anumana`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Anumana.lean)

- **Target:** Emptiness as an inference
- **Formal scope:** `isabelle/Buddhist/HeartSutra/HeartSutra_Anumana.thy` combines the Madhyamaka assumptions with Dignāga's wheel. This module retains an explicit reusable interface, then supplies an adapter from the actual `Madhyamaka` development.  In that adapter universal emptiness and arising are derived from the model, while a distinct comparison dharma is constructed from the concrete `Dharma` datatype.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 6 definitions/types, 9 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `HeartSutra_Anumana`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`, `chi-1969`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.AnupalabdhiKinds`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/AnupalabdhiKinds.lean)

- **Target:** Eleven deployment forms of non-apprehension
- **Formal scope:** *Nyāyabindu* 2.31–42 presents eleven applications of non-apprehension and then gathers the ten indirect applications under non-apprehension of an own nature.  This module reconstructs those *deployment shapes*: it is not a critical edition, and it does not claim that the same eleven-item taxonomy is used in Dharmakīrti's other works or by every commentator.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 24 definitions/types, 14 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `nyayabindu-2.31-42-gretil`; secondary/formal: none registered. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Apoha`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Apoha.lean)

- **Target:** Apoha and revision
- **Formal scope:** Sets are represented extensionally as predicates.  Unlike Isabelle/HOL, Lean permits empty types, so `apoha_no_fixpoint` explicitly assumes that the underlying type is inhabited; without it the statement is false.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 13 definitions/types, 18 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Dignaga_Apoha`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.ApohaFeatures`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/ApohaFeatures.lean)

- **Target:** Feature-grounded apoha
- **Formal scope:** Bare mutual complementation determines the negative extension only after a positive extension has already been chosen.  This module adds a component semantics: a concept is fixed by the features it requires, and its positive extension contains exactly the objects having every required feature.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 15 definitions/types, 13 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.ApohaSelection`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/ApohaSelection.lean)

- **Target:** Selection principles for feature-grounded apoha
- **Formal scope:** Feature grounding fixes an apoha pair only after its required features have been fixed.  This module makes the remaining selection step explicit.  A rule states which requirements are admissible and when one admissible requirement is no worse than another.  Antisymmetry on admissible candidates makes an optimal requirement unique, after which the existing component theorem fixes both the positive and negative extensions.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 7 definitions/types, 13 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Dharmakirti`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Dharmakirti.lean)

- **Target:** Dharmakīrti's three kinds of reason
- **Formal scope:** This ports the semantic content of `isabelle/Buddhist/Pramana/Dharmakirti_Reasons.thy`: pervasion supplies the premise missing from the three marks, while identity, effect and non-perception reasons expose different sources for that premise.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 8 definitions/types, 12 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Dharmakirti_Reasons`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`, `chi-1969`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.DirectedMomentariness`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/DirectedMomentariness.lean)

- **Target:** Directed causal transport and momentariness
- **Formal scope:** `BuddhistComparativeLogic.Buddhist.Pramana.Momentariness` derives punctual production from a rooted chain whose links preserve every causal power in both directions.  Literal momentariness does not need that much.  For a production observed at the end of a rooted chain, it is enough to transport that same effect backwards, one link at a time, to the root.  Uniqueness of an effect's production time then identifies the observed time with the root.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 5 definitions/types, 8 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Hetucakra`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Hetucakra.lean)

- **Target:** Dignāga's wheel of reasons
- **Formal scope:** A bare Lean port of `isabelle/Buddhist/Pramana/Dignaga_Hetucakra.thy`.  The object-language predicates are `Prop`-valued; this makes explicit a distinction that Isabelle/HOL's `bool` type leaves implicit.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 17 definitions/types, 15 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Dignaga_Hetucakra`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`, `chi-1969`, `iwata-2002-hetucakra`, `tillemans-2004-inductiveness`, `katsura-2004-example`, `oetke-2004-example`. Iwata documents the wheel classification. Tillemans 2004 pp. 252-258 and Katsura 2004 p. 149 discuss subject exclusion and the known inferential gap. The finite predicates and subject-erasure implementation are modern diagnostics of that established issue, not a new objection to Dignaga.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.InferenceScope`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/InferenceScope.lean)

- **Target:** The subject excluded from the comparison classes
- **Formal scope:** Audit of the existing Hetucakra encoding, not a historical refutation of Dignaga. Its similar and dissimilar classes exclude the subject. This file shows exactly why their three marks do not by themselves decide that subject: deleting its thesis preserves the marks. Under the marks, the additional global pervasion premise is equivalent to the subject's thesis.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 2 definitions/types, 6 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/ARGUMENTS.md](../docs/ARGUMENTS.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Ksanabhangasiddhi`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean)

- **Target:** Premise audit for momentariness inference
- **Formal scope:** This module formalizes a restrained `sattvānumāna`-style argument: an existent is causally efficacious, and the proposed thesis is numerical momentariness.  The first equivalence follows from the explicit `efficacy` field of `Momentariness.Theory`.  The second step is represented by an explicit global pervasion premise; a rooted directed transport certificate is one sufficient way to prove it.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 13 definitions/types, 16 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/PRAMANA_TREATISES.md](../docs/PRAMANA_TREATISES.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Momentariness`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Momentariness.lean)

- **Target:** Causal efficacy and the limit of the argument for momentariness
- **Formal scope:** The argument usually summarized as `whatever exists is momentary` first establishes a weaker conclusion under efficacy, uniqueness of an effect's production time, and the existence of two distinct times: an existent cannot have exactly the same causal powers at every time.  This module keeps that conclusion separate from the further continuity and punctuality bridge needed for literal momentariness.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 14 definitions/types, 23 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.OtherMinds`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/OtherMinds.lean)

- **Target:** Behaviour and the inference to another stream of cognition
- **Formal scope:** This module gives a deliberately small reconstruction of one issue connecting Dharmakīrti's argument for other streams of cognition with Ratnakīrti's criticism.  An agent's behaviour is observable and its volition is the target of inference.  The deductive argument therefore needs a pervasion from the selected behaviour to volition; a calibrated first-person case does not by itself supply that pervasion.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 18 definitions/types, 14 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/INFERENCE_DEBATE.md](../docs/INFERENCE_DEBATE.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/PramanaSynthesis.lean)

- **Target:** A common certificate interface for Buddhist inference
- **Formal scope:** This module synthesizes the existing Dignaga, Dharmakirti and emptiness developments without identifying their distinct proof obligations.  A `DeductiveCertificate` contains exactly what derives the thesis at the subject: possession of the reason and an explicit pervasion.  A `DialecticalCertificate` additionally contains a positive comparison example; that extra field completes the three marks and gives a valid cell in the wheel of reasons.
- **Assumption boundary:** Named interfaces and certificates carry every premise consumed by the composition or transport theorem.
- **Checked inventory:** 6 definitions/types, 24 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** The interface checks composition; it does not independently justify historical, causal, or empirical inputs.
- **Release:** `release_candidate`. Documentation: [docs/PRAMANA_YOGACARA.md](../docs/PRAMANA_YOGACARA.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Pramanasamuccaya`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean)

- **Target:** A restrained Pramanasamuccaya synthesis
- **Formal scope:** This module formalizes a small proof architecture associated with Dignaga's *Pramanasamuccaya*.  It does not encode the Sanskrit text or claim that one modern semantics is its uniquely correct interpretation.  Instead it keeps four interfaces separate:
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 18 definitions/types, 24 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/PRAMANA_TREATISES.md](../docs/PRAMANA_TREATISES.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Pramanavarttika`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean)

- **Target:** A restrained Pramāṇavārttika synthesis
- **Formal scope:** This module packages several proof obligations associated with Dharmakīrti's epistemology without claiming to formalize a historical edition of the `Pramāṇavārttika`.  A pramāṇa is represented here by an occurring, novel, content-bearing and reliable cognition.  Reliability is operational: every object presented by the cognition participates in a successful realization. Causal efficacy is therefore obtained only through an occurring cognition that both presents and realizes the object.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 17 definitions/types, 26 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/PRAMANA_TREATISES.md](../docs/PRAMANA_TREATISES.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Pratyaksabhasa`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pratyaksabhasa.lean)

- **Target:** A finite audit of perception and perceptual semblance
- **Formal scope:** This module compares two deliberately narrow formal criteria associated with Dignāga and Dharmakīrti: freedom from conceptual construction, and freedom from error in addition to nonconceptuality.  It is not an edition or complete interpretation of either author's account of perception or *pratyakṣābhāsa*.  In particular, the predicates `erroneous` and `true` are independent inputs rather than a claimed reconstruction of a single Sanskrit term.
- **Assumption boundary:** Conceptuality, error, and truth are independent inputs. Dharmakīrti-side refinement is definitional, while reliability needs an explicit bridge from nonerror to true cognition.
- **Checked inventory:** 13 definitions/types, 13 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `dignaga-ps1-steinkellner-2014`, `dharmakirti-nyayabindu-1.4-1.6-gretil`; secondary/formal: none registered. Passage aligned (sources accessed 2026-09-19) to Dignāga PS(V) 1.3c and 1.7c–8b in Steinkellner’s revised reconstruction and Dharmakīrti Nyāyabindu 1.4–1.6 in the Shastri-based GRETIL text. The predicates and two-moons model are project paraphrases, not translations.
- **Limit:** A finite comparison of two narrow criteria, not an edition, complete theory of perception, or claim that one Boolean predicate exhausts pratyakṣābhāsa.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Sambandhapariksa`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Sambandhapariksa.lean)

- **Target:** Relations and reified connectors
- **Formal scope:** This module provides a bounded formal audit motivated by arguments about relations in Dharmakirti's *Sambandhapariksa*.  An ordinary binary relation is a `Prop`-valued predicate.  A reified connector instead belongs to a separate type and has endpoints.  The two kinds of data are independent until an explicit representation bridge is supplied.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 18 definitions/types, 19 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.SvatantraPrasanga`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/SvatantraPrasanga.lean)

- **Target:** Autonomous inference and consequence refutation
- **Formal scope:** This module supplies two small interfaces for comparing an autonomous inference with a consequence-style refutation.  It is not a definition of the historically contested labels *Svatantrika* and *Prasangika*, nor does it attribute one fixed proof theory to Bhaviveka, Candrakirti, or later Tibetan authors.  The interfaces isolate claims that can be checked in the present repository: a deductively sound argument may also require the opponent's commitment to its subject reason and pervasion, whereas a covered refutation of an opponent's claim does not by itself prove an independent thesis.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 14 definitions/types, 9 theorems/lemmas, 0 examples; imports 4 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Tattvasamgraha`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean)

- **Target:** Scoped debate certificates motivated by the Tattvasaṃgraha
- **Formal scope:** Śāntarakṣita's *Tattvasaṃgraha* is a large, internally varied collection of arguments against rival positions.  This module does not claim to translate every verse or to turn the whole work into one axiomatic theory.  It instead registers a selected group of arguments that can be connected carefully to the existing developments: inference, dependence, fourfold causation, momentariness, theories of the three times, apoha, and the observational underdetermination exposed by the *Viṃśatikā* models.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 28 definitions/types, 20 theorems/lemmas, 0 examples; imports 5 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/PRAMANA_TREATISES.md](../docs/PRAMANA_TREATISES.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.Debate`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Debate.lean)

- **Target:** A small consequence-debate calculus
- **Formal scope:** This module gives a deliberately small calculus inspired by Tibetan `bsdus grwa` consequence debate.  It is not a transcription of any one monastic manual, and its three replies are not claimed to exhaust the historical vocabulary.  They isolate one proof-theoretic core: a challenger presents a consequence, while a defender may accept it, report no commitment to its subject-reason, or report no commitment to its pervasion.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 39 definitions/types, 27 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/INFERENCE_DEBATE.md](../docs/INFERENCE_DEBATE.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Vadanyaya`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Vadanyaya.lean)

- **Target:** Semantic proof and procedural result in a small debate audit
- **Formal scope:** This module gives a deliberately small formal interface inspired by Dharmakirti's *Vadanyaya*.  It is not a complete transcription of that work, its historical list of defeat conditions, or any later debate manual.  The model isolates a few auditable distinctions: proponent and opponent have asymmetric procedural obligations; an allegation may identify a real fault or merely a pseudo-fault; and thesis truth, semantic proof, public acceptance, and procedural result remain separate layers.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 22 definitions/types, 17 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Vyaptinirnaya`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Vyaptinirnaya.lean)

- **Target:** A causal and scope-bounded audit of pervasion determination
- **Formal scope:** This module gives a deliberately small reconstruction inspired by Ratnakirti's *Vyaptinirnaya*.  It separates finite observed concomitance from global reason-to-thesis pervasion.  A global conclusion is licensed here only when a causal-production rule is joined to an explicit scope, proof that every reason case is covered by that scope, and proof that the scope contains no defeating condition.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 21 definitions/types, 14 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: `ratnakirti-vyaptinirnaya-gretil`; secondary/formal: `oeaw-vyaptinirnaya`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

## Yogacara (8)

### [`BuddhistComparativeLogic.Buddhist.Yogacara.Alambanapariksa`](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Alambanapariksa.lean)

- **Target:** A two-condition reconstruction of the Alambanapariksa
- **Formal scope:** This module isolates a small argument form associated with Dignaga's *Alambanapariksa*.  It is a text-bounded reconstruction, not a claim that the Lean predicates exhaust the historical notions.  An intentional object (`alambana`) for one cognition must satisfy two separately supplied conditions: it causally produces that cognition, and it resembles the image presented in that cognition.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 21 definitions/types, 20 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/INFERENCE_DEBATE.md](../docs/INFERENCE_DEBATE.md).

### [`BuddhistComparativeLogic.Buddhist.Yogacara.PramanaYogacara`](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/PramanaYogacara.lean)

- **Target:** Inferential scope for Yogacara observation models
- **Formal scope:** The Viṃśatikā models record appearances and efficacy, while Dharmakīrti's inference interface makes pervasion an explicit premise.  This module joins those interfaces without treating observational adequacy as an ontological conclusion.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 24 definitions/types, 25 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/PRAMANA_YOGACARA.md](../docs/PRAMANA_YOGACARA.md).

### [`BuddhistComparativeLogic.Buddhist.Yogacara.Sahopalambha`](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Sahopalambha.lean)

- **Target:** Constant co-apprehension and the scope of non-difference
- **Formal scope:** This module gives a restrained reconstruction of the argument commonly called `sahopalambhaniyama`.  Objects, cognitions, observation tokens and times have different types.  Tokenwise co-apprehension first yields only equality of observable traces and of their time profiles.  Numerical identity is a separate primitive relation on a tagged sum and follows only from an explicit identity-from-extension bridge.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 26 definitions/types, 18 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Yogacara.Svasamvedana`](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Svasamvedana.lean)

- **Target:** Reflexive presentation, traces, and later memory
- **Formal scope:** This module gives a bounded interface inspired by Dignaga-Dharmakirti discussions of `svasamvedana`.  Episodes, presented objects, traces, and memory tokens have different types.  Object presentation does not contain self-presentation by definition: an explicit reflexivity certificate supplies that step.  Trace formation, later retention, matching recall content, and unique source attribution are further independent proof obligations.
- **Assumption boundary:** Self-presentation, trace formation, retention, laterness, content matching, and source uniqueness remain independent certificate fields; none follows from co-apprehension alone.
- **Checked inventory:** 23 definitions/types, 12 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `dignaga-ps1-steinkellner-2014`; secondary/formal: `mascarello-2025-svasamvedana`. Passage aligned (sources accessed 2026-09-19) to Dignāga PS(V) 1.6ab and 1.9–12, especially 1.11c–d on later recollection. Technical labels are retained, but traces, laterness, and unique source attribution are project-authored typed decompositions, not translations.
- **Limit:** A bounded reflexive-awareness and memory test bench, not an edition, exhaustive history of svasaṃvedana, or proof that recollection is the only historical argument.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Yogacara.Vimsatika`](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Vimsatika.lean)

- **Target:** Vasubandhu's Viṃśatikā
- **Formal scope:** The first part supplies appearance-only models for the four adequacy conditions.  The second states the partless-atom dilemma using predicate sets, so it needs no external set library.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 18 definitions/types, 9 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Yogacara_Vimsatika`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Yogacara.VimsatikaModels`](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/VimsatikaModels.lean)

- **Target:** Appearance models and object-indexed factorizations
- **Formal scope:** The four adequacy conditions in `BuddhistComparativeLogic.Buddhist.Yogacara.Vimsatika` mention only appearance and efficacy.  This module factors those two predicates through an indexed carrier and compares the resulting accounts through their observable fields. The type `ObjectIndexedAccount` denotes only this relational interface: it does not encode mind-independence, persistence, individuation, or even nonemptiness of the carrier.  Consequently the generic construction below is a factorization through observation tokens, not a proof that external objects exist.  Concrete `Unit`- and `Bool`-indexed accounts show only that the same observations leave the carrier cardinality underdetermined at this interface.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 9 definitions/types, 13 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [README.md](../README.md).

### [`BuddhistComparativeLogic.Buddhist.Yogacara.YogacaraConsciousness`](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraConsciousness.lean)

- **Target:** Eight consciousnesses as functional roles
- **Formal scope:** This module represents the eight-consciousness taxonomy by eight role labels: five sensory roles, mental cognition, afflicted mind, and store consciousness. The labels do not introduce eight substances.  Activity, presentation, and support are separate predicates on the labels, and distinct roles may be realized by the same bearer.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 14 definitions/types, 8 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/PRAMANA_YOGACARA.md](../docs/PRAMANA_YOGACARA.md).

### [`BuddhistComparativeLogic.Buddhist.Yogacara.YogacaraSynthesis`](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraSynthesis.lean)

- **Target:** A conditional Yogācāra synthesis
- **Formal scope:** This module connects four claims often grouped under a Yogācāra reading: appearance-level adequacy, the three natures, continuity by seeds, and transformation of the basis.  The interfaces are deliberately weaker than a historical or metaphysical identification of those claims.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 17 definitions/types, 21 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/PRAMANA_YOGACARA.md](../docs/PRAMANA_YOGACARA.md).

## Comparative (30)

### [`BuddhistComparativeLogic.Buddhist.Abhidharma.Analysis`](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Analysis.lean)

- **Target:** Analysis-relative existence in the Abhidharmakośabhāṣya
- **Formal scope:** This module reconstructs the analytical contrast discussed around *Abhidharmakośabhāṣya* VI.4.  Physical destruction and mental analysis are tagged separately.  A framework also keeps transformation, admissibility, and continued recognition separate.  An object is `ParamarthaSat` here when its recognition survives every admitted analysis; it is `SamvrtiSat` when an admitted analysis supplies a recognition-loss witness.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 18 definitions/types, 13 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `abhidharmakosabhasya-6.4-gretil`; secondary/formal: none registered. Abhidharmakośabhāṣya VI.4 and its bhāṣya are fixed at GRETIL source-page markers 333.23–334.13: breaking a pot and mentally separating water are conventional-existence examples, contrasted with form and feeling as ultimately existent. `Framework` and `RecognitionSurvives` are the module’s modern encoding.
- **Limit:** Passage-aligned only for the destruction/analysis examples and persistence of the relevant cognition. The finite-inventory complement theorem, certificate APIs, and ranked-rewrite adapter are modern results and are not attributed to Vasubandhu.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Buddhist.Abhidharma.Pudgala`](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Pudgala.lean)

- **Target:** Aggregate streams and the person
- **Formal scope:** This module gives a deliberately scoped reconstruction inspired by the discussion of the person in chapter IX of Vasubandhu's *Abhidharmakosabhasya*.  The mathematical target is narrow: it distinguishes a conventional designation over a time-indexed stream of the five aggregates from a putative separate substantial person, and it records exactly which dependence and change premises exclude an immutable, causally active extra person.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 28 definitions/types, 15 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: `abhidharmakosabhasya-gretil`; secondary/formal: `sep-vasubandhu`, `iep-pudgalavada`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Buddhist.Abhidharma.Sarvastivada`](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Sarvastivada.lean)

- **Target:** Sarvāstivāda accounts of the three times
- **Formal scope:** The formal comparison is kept separate from any particular clock.  A `TriTemporal` model supplies its own `before` relation; the concrete Buddhadeva countermodel uses natural-number time.
- **Assumption boundary:** Locale/record fields expose the doctrinal and semantic premises mirrored from the Isabelle theory.
- **Checked inventory:** 11 definitions/types, 15 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Sarvastivada_ThreeTimes`.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `internal-isabelle-port`. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A semantic headline-result port, not a declaration-for-declaration translation or proof of the premises.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Buddhist.Abhidharma.Yamaka`](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Yamaka.lean)

- **Target:** Paired extension questions in the Yamaka style
- **Formal scope:** This module formalizes a small, computational audit inspired by the paired questions of the Pali *Yamaka*.  It checks the two directions `A ⊆ B` and `B ⊆ A` separately on an explicitly enumerated finite domain, and classifies their extensions as equal, left proper, right proper, or incomparable.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 18 definitions/types, 15 theorems/lemmas, 0 examples; imports 0 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Fazang.Mereology`](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Fazang/Mereology.lean)

- **Target:** A scoped rafter-house mereology
- **Formal scope:** This module develops a typed whole-part and functional-intervention model inspired by Fazang's rafter-and-house discussions and the six characteristics. The primary passage is *Huayan yisheng jiaoyi fenqi zhang* 華嚴一乘教義分齊章, Taishō T45 no. 1866, 507c3–508a22, in pinned CBETA XML P5 <https://github.com/cbeta-org/xml-p5/blob/dbdea41071e1e260ad84b72faefd4587333cf76d/T/T45/T45n1866.xml#L2797-L2841>; Jones's study supplies secondary orientation: <https://doi.org/10.1080/09608788.2018.1563768> (accessed 2026-09-19).
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 33 definitions/types, 25 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `fazang-t1866-507c03-508a22-cbeta`; secondary/formal: `jones-2019-fazang-six-characteristics`. CBETA T45 no. 1866, 507c3–508a22 fixes the six-characteristics list and the rafter-house dialogue, including the one-rafter removal example; Jones (2019) supplies standard secondary orientation. `CommonIdentity`, `StrongInterpenetration`, and the functional intervention fields are modern operational definitions.
- **Limit:** Passage-aligned for the six labels, the rafter-house case, and the stated removal dependence. It does not identify the Lean predicates with every Huayan use of identity or interpenetration, supply a literal translation, or claim a uniquely correct interpretation.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Xuanzang.Inference`](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Xuanzang/Inference.lean)

- **Target:** Acceptance scopes in paired Buddhist inferences
- **Formal scope:** This module gives a small typed model for the acceptance conditions at issue in discussions of Xuanzang's so-called "consciousness-only inference" and a counter-inference associated with Wonhyo.  An argument records its subject, reason, conclusion, pervasion, comparison witness, and the terms which both parties accept for the exchange.  Soundness uses the semantic reason and pervasion; shared terminology by itself does not establish the conclusion.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 24 definitions/types, 11 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: none registered; secondary/formal: `tang-2018-xuanzang-inference`. Passage aligned through Tang’s source study (accessed 2026-09-19), especially pp. 143–150 and edited materials Texts 1.1, 1.9, and 5.2, for the three qualifications and Wŏnhyo counter-inference. The module records the dispute and paraphrases argumentative roles.
- **Limit:** A modern acceptance-scope audit of a contested inference. It does not settle authenticity, establish a uniquely correct interpretation, reproduce a source translation, or infer historical acceptance from formal validity.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Buddhist.Hermeneutics.Vyakhyayukti`](../lean/BuddhistComparativeLogic/Buddhist/Hermeneutics/Vyakhyayukti.lean)

- **Target:** Five-part commentary certificates inspired by the Vyākhyāyukti
- **Formal scope:** This module gives a typed audit of five tasks associated with Vasubandhu's *Vyākhyāyukti*: stating a purpose (`prayojana`), giving a synopsis (`piṇḍārtha`), explaining words (`padārtha`), locating a passage in its discourse (`anusandhi`), and answering objections (`codyaparihāra`).  The formal certificate is a checklist whose witnesses remain visible.  It is not an edition or translation of the treatise, and it does not claim that every historical commentator formulates the five tasks in exactly this way.
- **Assumption boundary:** Coverage is relative to a supplied framework and explicit witnesses; it does not prove truth, completeness beyond that framework, or uniqueness of an interpretation.
- **Checked inventory:** 45 definitions/types, 31 theorems/lemmas, 0 examples; imports 4 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `lee-2001-vyakhyayukti-tibetan`; secondary/formal: `ueno-2021-vyakhyayukti`, `uva-vyakhyayukti-30b`. Passage aligned (sources accessed 2026-09-19) to Vyākhyāyukti saṃgrahaśloka 1 and the five tasks, with Lee’s four-recension Tibetan critical edition, Ueno’s pp. 95–96 Sanskrit witness and translation, and Mandala’s 30b locator. Lean task predicates are project paraphrases and a modern checklist.
- **Limit:** A finite certificate system for the five identified tasks, not an edition, full translation, or formalization of the entire Vyākhyāyukti.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Buddhist.KoreanBuddhism.WonhyoHwajaeng`](../lean/BuddhistComparativeLogic/Buddhist/KoreanBuddhism/WonhyoHwajaeng.lean)

- **Target:** Local theories and a bounded hwajaeng gluing interface
- **Formal scope:** This module gives a modern, bounded reconstruction inspired by Wŏnhyo's *hwajaeng* (harmonization of disputes).  Claims are evaluated in typed local contexts.  A global valuation can be glued from them only when every claim is covered and overlapping contexts agree.  The resulting theorem preserves a local derivation; it does not store the desired conclusion in the gluing certificate.
- **Assumption boundary:** The finite contexts, `inScope` predicate, coverage condition, overlap agreement, and gluing function are project-authored interfaces. The extant fragment does not establish a sheaf-like construction.
- **Checked inventory:** 24 definitions/types, 18 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: `wonhyo-simmun-muller-2016`; secondary/formal: `muller-2015-hwajaeng`. Muller’s translation records that only fragments of the beginning of Simmun hwajaeng non survive (HBJ/HPC 1.838–841). The fragment and Muller’s study support attention to positions’ backgrounds, aims, assumptions, and precise divergence, but do not supply coverage, overlap-agreement, or gluing operations.
- **Limit:** The module is a bounded modern analogy for local-to-global consistency, not a translation, reconstruction of the lost work, or claim that Wŏnhyo used sheaf semantics.
- **Release:** `deferred_source_review`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.BsdusGrwa`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/BsdusGrwa.lean)

- **Target:** Four-cell predicate comparison from *bsdus grwa*
- **Formal scope:** This module isolates one extensional exercise found in Tibetan collected-topic (*bsdus grwa*) pedagogy: compare two predicates by asking which of the four joint truth cells have witnesses.  It is not an edition of a particular manual, and it does not claim that this finite predicate semantics exhausts the intensional or dialectical uses of the historical relation vocabulary.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 33 definitions/types, 33 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `ngagwangtashi-collected-topics-uma`; secondary/formal: `magee-2019-open-source-geshe`. Ngag-wang-tra-shi’s bilingual Collected Topics, ch. 1, pp. 31–32 explicitly enumerates and witnesses all four possibilities between color and shape. Magee (2019) maps the broader four-relation taxonomy and warns that the compared phenomena are not concepts or sets. The Boolean implementation is therefore an explicit modern extensionalization.
- **Limit:** Passage-aligned to the four color/shape witness cells and secondarily oriented to the relation taxonomy. It does not claim that Tibetan phenomena are sets, that Boolean predicates capture intensional or dialectical practice, or that one manual exhausts the bsdus grwa genre.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.Definitions`](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Definitions.lean)

- **Target:** Definition, definiendum, and definitional basis
- **Formal scope:** This module gives a restrained predicate model of the three items commonly distinguished in Tibetan discussions of definition: a defining condition, a definiendum, and a basis on which the condition is instantiated.  It is not an edition of a Tibetan *bsdus grwa* text and does not claim that extensional predicates capture every intensional, linguistic, or pedagogical constraint used by a particular author or monastery.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 18 definitions/types, 12 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.ChineseThought.HardWhite`](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/HardWhite.lean)

- **Target:** Sensory access and co-inherence in a Hard/White audit
- **Formal scope:** This module gives a small typed reconstruction motivated by the received "Hard and White" discussion in the *Gongsun Longzi*.  Sight and touch are modeled as different access channels, while whiteness and hardness are modeled as qualities which can inhere in one stone.  Distinct sensory access profiles are provable without identifying sensory distinction with separate substances.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 18 definitions/types, 17 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `gongsunlongzi-jianbai-ctext`; secondary/formal: `graham-1967-hard-white`, `uzh-2015-gongsunlongzi-philology`. The received Chinese Jianbai lun is fixed at Chinese Text Project; Graham (1967) analyzes the seen-white/touched-hard contrast and early evidence, while the University of Zurich overview records the disputed textual history. No user/AI English rendering from the primary-text site is adopted.
- **Limit:** Passage-aligned only to the received hard/white and sight/touch problem. The one-stone sensory countermodel does not establish the dialogue’s intended metaphysics, historical authorship, date, or a uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.ChineseThought.MohistCanons`](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/MohistCanons.lean)

- **Target:** Kind, standard, naming, and analogical extension in the Mohist Canons
- **Formal scope:** This module gives a small semantic audit inspired by the Later Mohist discussions of `lei` (kind), `fa` (standard), names and objects, and `tui` (extension by analogy).  It is not a transcription of the damaged received text, and it does not identify Mohist reasoning with modern propositional logic.  In particular, surface parallelism is represented as data about a public expression and is kept separate from semantic relevance.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 24 definitions/types, 8 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.ChineseThought.WhiteHorse`](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/WhiteHorse.lean)

- **Target:** Extension, name, and selection in a White Horse audit
- **Formal scope:** This module gives a bounded semantic audit motivated by Gongsun Long's *White Horse Discourse*.  It does not select one historical interpretation of that text.  Instead it separates four claims that are easy to conflate: extension inclusion, identity of public names, identity of meanings, and identity of the feature requirements used to select an object.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 20 definitions/types, 14 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Grammar.Bhartrhari`](../lean/BuddhistComparativeLogic/Comparative/Grammar/Bhartrhari.lean)

- **Target:** Staged signification and avacya
- **Formal scope:** This module gives a small formal reconstruction inspired by Bhartṛhari's discussion of expressions for what is called inexpressible (`avācya`).  A vocabulary is indexed by a stage, so failure of every expression in a base vocabulary remains distinct from failure at every possible stage.  A later extended vocabulary can therefore denote the target without contradiction.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 24 definitions/types, 17 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `vakyapadiya-3.3.26-web`; secondary/formal: `sep-literal-nonliteral-india`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Grammar.PaniniDerivation`](../lean/BuddhistComparativeLogic/Comparative/Grammar/PaniniDerivation.lean)

- **Target:** Ranked priority rewriting
- **Formal scope:** This module gives a small, executable rewrite interface inspired by the rule ordering and conflict-resolution questions associated with Pāṇini.  A finite rule inventory is separated from an explicit resolver.  Every applicable rewrite must lower a natural-number rank, while the resolver must choose an applicable rule of maximal declared priority.  These premises give a terminating chosen derivation.  Uniqueness of normal forms is proved only for a step relation supplied with an explicit determinism premise.
- **Assumption boundary:** Termination depends on a natural-number rank decrease for every applicable rule; unique normal forms require a separately supplied deterministic step relation. The Bhartrhari import supplies only a generic rewrite adapter.
- **Checked inventory:** 19 definitions/types, 12 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `ashtadhyayi-1.4.2-sanskrit-library`; secondary/formal: `rajpopat-2023-conflict-resolution`. Passage aligned (sources accessed 2026-09-19) to Aṣṭādhyāyī 1.4.2, vipratiṣedhe paraṃ kāryam. Priority can encode the standard serial-order reading; ranks, lists, choice, termination, and determinism are modern infrastructure and not translations of the sūtra.
- **Limit:** A configurable modern priority-rewrite system motivated by one metarule, not a full Aṣṭādhyāyī implementation or a unique historical account of conflict resolution.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Jaina.JainaChange`](../lean/BuddhistComparativeLogic/Comparative/Jaina/JainaChange.lean)

- **Target:** Origination, decay, and duration in Jaina change
- **Formal scope:** This module gives a typed transition semantics for the Jaina triad *utpāda*, *vyaya*, and *dhrauvya*: a carrier is present at two successive times, an old mode is lost, and a new mode is acquired.  A certificate keeps these facts independent.  Finite countermodels then distinguish replacement without a persisting carrier from duration without change of mode.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 17 definitions/types, 15 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `tattvarthasutra-5.29-5.30`; secondary/formal: `sep-jaina`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Jaina.JainaInference`](../lean/BuddhistComparativeLogic/Comparative/Jaina/JainaInference.lean)

- **Target:** Anyathanupapatti and a two-member inference
- **Formal scope:** This module gives a bounded modal reconstruction of the Jaina criterion `anyathanupapatti`, the reason's inability to occur otherwise than with the thesis.  Actual-world inclusion and absence of an accessible countercase are different predicates.  A two-member certificate carries the reason at the subject and the modal link at that subject; a global bridge is explicitly required before the certificate is exported to the existing Nyaya semantic interface.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 17 definitions/types, 14 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: `nyayavatara-commentary-gretil`; secondary/formal: `sep-jaina`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Jaina.NayaDynamics`](../lean/BuddhistComparativeLogic/Comparative/Jaina/NayaDynamics.lean)

- **Target:** Ordered observation traces for the seven naya
- **Formal scope:** `BuddhistComparativeLogic.Comparative.Jaina.Saptabhangi` separates the seven modes by quantifying over three respects.  This module adds an ordered observation layer.  A trace records the respects actually entered; observation is accumulated monotonically, and a mode is exactly licensed when the trace has acquired its primitive profile.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 11 definitions/types, 20 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Jaina.Saptabhangi`](../lean/BuddhistComparativeLogic/Comparative/Jaina/Saptabhangi.lean)

- **Target:** The Jaina sevenfold predication
- **Formal scope:** This follows `isabelle/Comparative/Jaina/Jaina_Saptabhangi.thy` through its three readings: truth functional, classificatory, and indexical over respects (`naya`).
- **Assumption boundary:** Three existential primitive supports determine all seven predicates. An arbitrary family has a noncomputably selected representative subfamily of at most three viewpoints, including the empty case.
- **Checked inventory:** 13 definitions/types, 33 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `isabelle_port`; Isabelle theory units: `Jaina_Saptabhangi`.
- **Historical status:** `work_level`; primary: `samantabhadra-aptamimamsa-14-23-gretil`; secondary/formal: `internal-isabelle-port`, `sep-jaina`, `rahlwes-2023-saptabhangi`, `nahata-2024-syadvada`, `matilal-1981-central`, `ganeri-2020-jaina-reprint`. Āptamīmāṃsā 14–23 anchors conditioned modes and naya. Matilal's successive/simultaneous distinction and Ganeri's alternative neutrality interpretation are recorded separately. E is independent existential support; the model does not implement simultaneous predication as a cause of inexpressibility.
- **Limit:** Small-model preservation concerns only these support predicates, not order, frequency, relations or general Jaina semantics. Relation information loss has a modern counterexample; the wrapper is not a historical theory of simultaneity.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md), [docs/PORTING.md](../docs/PORTING.md).

### [`BuddhistComparativeLogic.Comparative.Mimamsa.MimamsaEpistemology`](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaEpistemology.lean)

- **Target:** Defeasible qualification and distinct pramanas in a Bhāṭṭa Mīmāṃsā audit
- **Formal scope:** This module isolates four proof-theoretic ideas in a Bhāṭṭa Mīmāṃsā, Kumārila-oriented audit: a cognition's initial qualification before defeat, later defeaters, postulation (`arthapatti`), and non-cognition (`anupalabdhi`).  It is not an edition or a claim that every Mīmāṃsā school accepts the same sources or gives the same account.  Initial qualification below is an entitlement status, not truth by definition.  A separate bridge is therefore required to derive truth from undefeated qualification.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 24 definitions/types, 24 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Mimamsa.MimamsaSentenceMeaning`](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaSentenceMeaning.lean)

- **Target:** Two Mīmāṃsā sentence-meaning architectures
- **Formal scope:** This module gives a bounded typed comparison inspired by the classical contrast between `abhihitanvaya` and `anvitabhidhana`.  In the first architecture, words independently supply lexical meanings which are then composed with argument roles.  In the second, a context supplies connected word occurrences before a sentence result is synthesized.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 30 definitions/types, 7 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `salikanatha-vakyarthamatrka-i-textgrid`; secondary/formal: `saxena-2018-mimamsa-verbal-cognition`. Śālikanātha’s Vākyārthamātṛkā I e-text contains the explicit anvitābhidhāna/abhihitānvaya debate; Saxena (2018) identifies it as the locus classicus and supplies a translation/paraphrase together with Sucarita’s Bhāṭṭa response. The two Lean structures are modern typed architectures, not translations.
- **Limit:** Passage-aligned to the named contrast in sentence-meaning theory. The computation APIs, `CompositionBridge`, agreement theorem, and Bhartṛhari staged-language adapter are not claims found in the cited texts, and the module does not endorse either school as uniquely correct.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Mimamsa.MimamsaViniyoga`](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaViniyoga.lean)

- **Target:** Ranked grounds for Mīmāṃsā viniyoga
- **Formal scope:** This module formalizes a finite resolver for the six interpretive grounds often ordered as `śruti`, `liṅga`, `vākya`, `prakaraṇa`, `sthāna`, and `samākhyā`.  Evidence records both whether it applies in the present case and which decision it supports.  The resolver first finds the strongest rank among applicable items and returns a decision only when every item at that rank supports the same result.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 23 definitions/types, 16 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `mimamsasutra-3.3.14-textgrid`; secondary/formal: none registered. Passage aligned (source accessed 2026-09-19) to Mīmāṃsāsūtra 3.3.14, which enumerates the six interpretive grounds and their relative weakening. The Lean ranks and resolver are project-authored formal paraphrases.
- **Limit:** Passage-aligned for the six grounds and their relative ordering only. Numeric ranks, tie behavior, executable resolution, and example applications are modern infrastructure, not a translation of Jaimini or Śabara.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Nyaya.NavyaNyayaAbsence`](../lean/BuddhistComparativeLogic/Comparative/Nyaya/NavyaNyayaAbsence.lean)

- **Target:** Qualified absence in a Navya-Nyaya-inspired audit
- **Formal scope:** This module gives a bounded modern reconstruction inspired by Navya-Nyaya analyses of absence.  A putative absence is indexed separately by a locus, a counterpositive, a delimiter, and a relation.  The formal result is therefore only a qualified absence at the supplied indices; it is not an unqualified claim that an object does not exist.
- **Assumption boundary:** The `relates` and `delimits` fields and the perceptibility, finite-search, cognition, and detection conditions are supplied interfaces. The historical sources do not prove the module’s detection law.
- **Checked inventory:** 23 definitions/types, 6 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: `sen-chatterjee-2010-navya-nyaya`, `ganeri-2008-navya-regimentation`, `sep-early-modern-india-abhava`. Secondary orientation only. Sen and Chatterjee pp. 83–85 and Ganeri, SEP §§11.2–11.3, substantiate the distinct locus, counterpositive, delimiter, and relation vocabulary. No primary passage or historical four-place formula is claimed.
- **Limit:** The four typed indices and certificate are a bounded modern reconstruction of source-oriented distinctions, not an edition, translation, or exhaustive Navya-Nyāya analysis.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Nyaya.Nyaya`](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Nyaya.lean)

- **Target:** A five-member public inference protocol
- **Formal scope:** This module gives a deliberately small, text-bounded model of the five members conventionally named `pratijna`, `hetu`, `udaharana`, `upanaya`, and `nigamana` in discussions of classical Nyaya inference.  It formalizes one inferential reading of those members; it is not an edition of the *Nyayasutra* or *Nyayabhasya*, and it does not claim that every historical Nyaya author assigned them exactly these proof-theoretic roles.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 29 definitions/types, 15 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md), [docs/INFERENCE_DEBATE.md](../docs/INFERENCE_DEBATE.md).

### [`BuddhistComparativeLogic.Comparative.Nyaya.Nyayakusumanjali`](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Nyayakusumanjali.lean)

- **Target:** A bounded maker-inference audit inspired by the Nyayakusumanjali
- **Formal scope:** This module reconstructs one narrow proof pattern associated with Udayana's `karyat` inference: effecthood is the reason, and the existence of an agent who knows the relevant materials, wills the product, and makes it is the thesis.  The reason reaches that thesis only through an explicit universal maker-pervasion premise.  A single manufactured example is kept separate from that premise.
- **Assumption boundary:** The conclusion requires an explicit universal MakerPervasion premise; one manufactured example does not establish it. Uniqueness, omniscience, eternity, and unrestricted domain claims are independent obligations.
- **Checked inventory:** 24 definitions/types, 15 theorems/lemmas, 0 examples; imports 2 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `nyayakusumanjali-5-gretil`; secondary/formal: `ruzsa-2022-kusumanjali`. Passage aligned (sources accessed 2026-09-19) to the received fifth section, verse 5.1 and the prose beginning kṣityādi kartṛpūrvakaṃ kāryatvāt. GRETIL is explicitly unproofread; Ruzsa 2022 motivates leaving verse authorship open. All English descriptions are project paraphrases.
- **Limit:** A bounded maker-inference audit of one kāryāt route, not a critical edition, full translation, complete Nyāyakusumāñjali, or proof of God.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Nyaya.Tarka`](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Tarka.lean)

- **Target:** Tarka as auxiliary counterfactual reasoning
- **Formal scope:** This module gives a deliberately small reconstruction of `tarka`.  The opposite of a target `F` is provisionally admitted and is shown to undermine an independently established proposition `G`.  The counterfactual step and the evidence for `G` are separate proof objects.  Together they establish `¬¬F` constructively; recovering `F` requires an explicit stability principle such as `Decidable F`.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 4 definitions/types, 15 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `nyayasutra-1.1.40-gretil`; secondary/formal: `kang-2010-tarka`. Nyāyasūtra 1.1.40 is fixed in the GRETIL Sanskrit text; Kang (2010) analyzes it with the Nyāyabhāṣya and cautions against an unqualified reductio reading. `CounterfactualStep` plus `SupportingPramana` is the module’s modern constructive reconstruction.
- **Limit:** The sūtra supports the target topic and doubt-removing orientation, but it does not state the exact rule `¬target → ¬supported`, the derivation of `¬¬target`, the later pramāṇa taxonomy, or the FDE comparison.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Nyaya.Tattvacintamani`](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Tattvacintamani.lean)

- **Target:** A scoped inference audit motivated by the Tattvacintamani
- **Formal scope:** This module isolates four proof-theoretic notions useful when reading the inference discussions associated with Gangesa's *Tattvacintamani*: universal reason-to-thesis inclusion (`Vyapti`), its reflective application to the subject (`Paramarsa`), a condition exposing a counterinstance to an unqualified inclusion (`Upadhi`), and three corresponding defects of a reason.  These are deliberately extensional interfaces over the existing `Anumana` model, not a translation of the Sanskrit text or a claim that the historical notions have only these components.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 14 definitions/types, 21 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Samkhya.Satkaryavada`](../lean/BuddhistComparativeLogic/Comparative/Samkhya/Satkaryavada.lean)

- **Target:** Capacity and latent effects in satkāryavāda
- **Formal scope:** This module gives a deliberately bounded reconstruction of one argument for the Sāṃkhya doctrine commonly called *satkāryavāda*: an effect is produced only where the cause has the corresponding capacity, and a further grounding principle locates that capacity in the effect's latent presence in the cause. Production, capacity, and latent presence remain three separate predicates. Consequently the positive theorem exposes both bridges, while finite models show that selective production or bare capacity does not supply latent preexistence by itself.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 14 definitions/types, 15 theorems/lemmas, 0 examples; imports 1 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `samkhyakarika-9`; secondary/formal: `sep-naturalism-india`, `iep-sankhya`. Registered sources identify the stated witness, work, or passage; consult source status before treating it as a critical edition.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Skepticism.Jayarasi`](../lean/BuddhistComparativeLogic/Comparative/Skepticism/Jayarasi.lean)

- **Target:** Grounding definitions and extending observations
- **Formal scope:** This module gives two bounded audits motivated by Jayarasi Bhatta's *Tattvopaplavasiṃha*.  First, it distinguishes a definition's local adequacy from the noncircular support used to qualify an epistemic method.  Support is either an independently certified base or a finite rank that strictly falls along every definitional dependency together with certified dependency-free bases.  A two-node mutual dependency has neither kind of support.
- **Assumption boundary:** Positive results require the module’s named model or certificate fields; finite boundaries expose omitted bridges.
- **Checked inventory:** 21 definitions/types, 17 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `work_level`; primary: none registered; secondary/formal: none registered. Work- or topic-level orientation only; passage-to-predicate mapping remains open.
- **Limit:** A bounded modern reconstruction, not an edition, translation, exhaustive doctrine, or uniquely correct reading.
- **Release:** `release_candidate`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).

### [`BuddhistComparativeLogic.Comparative.Vedanta.Sriharsa`](../lean/BuddhistComparativeLogic/Comparative/Vedanta/Sriharsa.lean)

- **Target:** A finite definition audit motivated by Sriharsa
- **Formal scope:** This module isolates four checkable defects often useful when reconstructing the definition criticism in Sriharsa's *Khandanakhandakhadya*: a definition may omit a target case, include a non-target case, depend directly and mutually on another definition, or classify relevantly alike cases non-uniformly.  The model is a modern finite audit, not an edition of the Sanskrit work and not a claim that these four tests exhaust Sriharsa's dialectic.  In particular, the dependency check detects reciprocal edges, not longer directed cycles.
- **Assumption boundary:** The finite relevant-alternatives model, the changed jewel/empty-shell example, direct reciprocal-dependency test, and Boolean `sameProfile` relation are supplied by the project. Jha’s translation is a historical witness with an explicit translator caveat.
- **Checked inventory:** 39 definitions/types, 20 theorems/lemmas, 0 examples; imports 3 direct module(s).
- **Provenance:** `lean_extension`; Isabelle theory units: none.
- **Historical status:** `passage_aligned`; primary: `sriharsa-jha-1913-sweets-refutation`; secondary/formal: `sep-sriharsa-das-2022`. Jha, chapter I §14, paras. 257–259, and Das §§1.2, 2.1–2.3 map chance-correct awareness, overextension, circularity, and uniformity to named KKh passages. No precise primary passage is yet mapped for the module’s underextension test; its direct mutual dependency and Boolean `sameProfile` test are narrower modern surrogates.
- **Limit:** The module audits four finite modern defect predicates; it does not formalize all direct or indirect circularity, provide an edition of KKh, or identify its uniformity relation with Śrīharṣa’s own formulation.
- **Release:** `deferred_source_review`. Documentation: [docs/COMPARATIVE_LOGIC.md](../docs/COMPARATIVE_LOGIC.md).
