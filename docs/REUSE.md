# Reusing parts of this development

Role: `supplement`

Lifecycle: `active`

Verified: 2026-09-19

Most of this repository is about Buddhist material, but the logical
infrastructure underneath it is ordinary non-classical logic and can be
lifted out on its own. Everything below is Apache-2.0 and depends on
nothing outside Isabelle's `HOL` session: no AFP, no `HOL-Library`.

Every row also has a bare-toolchain Lean 4 counterpart.  The full mapping is
in [`PORTING.md`](PORTING.md); import `lean/BuddhistComparativeLogic.lean` for everything,
or take the named modules and their transitive imports.  The Lean sources
use no Mathlib dependency.

| If you want | Take | Depends on |
| --- | --- | --- |
| A generic many-valued propositional logic: one formula type, one executable evaluator, and a locale parametric in carrier, negation, meet, join and designated set | `isabelle/Core/ManyValuedLogic.thy` | nothing |
| Classical, Belnap–Dunn FDE, and Priest's FDE-plus-fifth-value as three instances of that locale, with their truth tables, the classical embedding, and the standard failures (explosion, modus ponens, excluded middle) each with a constructive countermodel and a Nitpick regression | `isabelle/Core/FiniteLogics.thy` | `ManyValuedLogic` |
| The four corners of the catuṣkoṭi as a function of designation, and the theorem that Priest's fifth value is not a fifth corner | `isabelle/Core/Catuskoti.thy` | `ManyValuedLogic`, `FiniteLogics` |
| A sound and complete decision procedure for FDE and FDE5 consequence over **arbitrary** formulas and atom types, plus the variable-sharing (relevance) property and the theorem that FDE5 is FDE plus atom containment | `isabelle/Core/FDEProofTheory.thy` | the three above, `PlurivalentSemantics`, `UniversalDesignation`, `FiniteDecisionProcedures` |
| Priest's plurivalent construction, both liftings of the connectives, and the answer to his open question about general plurivalence under universal designation | `isabelle/Core/PlurivalentSemantics.thy`, `isabelle/Core/UniversalDesignation.thy`, `isabelle/Core/UniversalDesignationFDE.thy` | `Catuskoti` |
| Brute-force checkers for the three-atom fragment, proved equal to the semantics, for recomputing results by `eval` | `isabelle/Core/FiniteDecisionProcedures.thy` | `Madhyamaka_Jizang`, `HeartSutra_Connexive`, `HeartSutra_Emptiness` |
| Dignāga's wheel of reasons and Dharmakīrti's three kinds of reason as a locale semantics, with the theorem that the three marks are not deductively sufficient | `isabelle/Buddhist/Pramana/Dignaga_Hetucakra.thy`, `isabelle/Buddhist/Pramana/Dharmakirti_Reasons.thy` | `Main` only — these two are independent of everything else here |
| Circular definitions of the shape "X is the exclusion of non-X": the antitone operator has no fixed point, the two-term system is underdetermined, the Gupta–Belnap revision sequence has period two, and an equivalence relation restores uniqueness | `isabelle/Buddhist/Pramana/Dignaga_Apoha.thy` | `Dignaga_Hetucakra` only (and only for its last section) |
| A mereological dilemma about partless parts in contact: whole-to-whole contact collapses a cluster to a point, extension forces sides | `isabelle/Buddhist/Yogacara/Yogacara_Vimsatika.thy` | `Main` only |
| Four candidate definitions of "present" over a linear order of times, tested against uniqueness and change | `isabelle/Buddhist/Abhidharma/Sarvastivada_ThreeTimes.thy` | `Main` only |
| The threefold division of a linear order at a point, and the fact that traversal needs two positions — density stated as a hypothesis, not assumed | `isabelle/Buddhist/Madhyamaka/Madhyamaka_Gamana.thy` | `Main` only |
| Seven-mode predication over the five values, and the general point that a mode needing two "respects" cannot be a property of a single valuation | `isabelle/Comparative/Jaina/Jaina_Saptabhangi.thy` | `Catuskoti` |

## Adding your own logic

`isabelle/Core/ManyValuedLogicExample.thy` is a forty-line worked example: strong Kleene `K3` as
a datatype, three operations, a designated set and one
`global_interpretation`. Everything the locale proves is then available
under the new prefix, including the four corners, and the new logic can be
compared with the three already there against the same formulas. The
example ends by showing what separates `K3` from FDE — both lose excluded
middle; only FDE stops a contradiction from proving everything. It is part
of the session, so it is checked on every build.

For the stronger Lean comparison, take
`lean/BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean`.  It constructs K3 as the exact non-glut
FDE submatrix, proves formula and designation preservation, identifies K3
consequence with FDE consequence restricted to non-glut valuations, and
computes the exact four-corner image.  It also distinguishes existential from
universal corner classification for sets of possible values.

## Reusing the pramāṇa treatise interfaces

The four Lean-only treatise modules can be imported independently through
their transitive dependencies:

- `lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean` for perceptual evidence, neutral
  subject warrants, public marked arguments, and the classical extensional
  apoha boundary;
- `lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean` for content-bearing reliable cognition,
  causal efficacy, and intrinsic/effect reason certificates;
- `lean/BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean` for the existence-to-efficacy and
  efficacy-to-numerical-momentariness premise audit; and
- `lean/BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean` for scoped debate rules, explicit
  cross-topic connectors, and registry countermodels.

Their names indicate the historical argument families that motivated the
interfaces.  The reusable code does not contain textual editions or
chapter-completeness claims; see [`PRAMANA_TREATISES.md`](PRAMANA_TREATISES.md).

## Conventions worth copying

Three habits in this development are transferable to any Isabelle project
that formalizes contested texts or several logics at once.

- **One evaluator, many logics.** `mv_eval` is defined outside the locale,
  so it stays executable and Nitpick-friendly; the locale fixes only the
  operations. Instantiating is then a one-line `global_interpretation`.
- **Every locale carries a model.** A locale with contradictory assumptions
  proves everything, so each one here is accompanied by an interpretation
  or a `..._nonvacuous` lemma exhibiting a concrete model. `tools/check_names.py`
  fails the build if one is missing.
- **The prose is checked against the sources.** `tools/check_names.py` also fails
  the build if a theorem named in the documentation does not exist. For a
  development whose value is partly in its commentary, this is what keeps
  the commentary honest.
