/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.PremiseCertificates
import BuddhistComparativeLogic.Buddhist.Madhyamaka.Standpoints

/-!
# Local theories and a bounded hwajaeng gluing interface

This module gives a modern, bounded reconstruction inspired by Wŏnhyo's
*hwajaeng* (harmonization of disputes).  Claims are evaluated in typed local
contexts.  A global valuation can be glued from them only when every claim is
covered and overlapping contexts agree.  The resulting theorem preserves a
local derivation; it does not store the desired conclusion in the gluing
certificate.

The construction does not claim that all disputes are jointly consistent,
that adding a context label settles truth, or that this sheaf-like interface
is Wŏnhyo's own proof theory.  The countermodels below make both limitations
explicit: forgetting context can collect an assertion and its negation, and
an actual disagreement on an overlap prevents any common global extension.

Historical orientation and formal mapping (sources accessed 2026-09-19):

* Wŏnhyo, *Ten Approaches to the Harmonization of Doctrinal Disputes*
  (`Simmun hwajaeng non`), trans. A. Charles Muller (2016), introduction,
  preface, and extant translated fragments:
  https://www.acmuller.net/kor-bud/simmun_hwajaeng_non.html.
  Muller's introduction reports that only fragments of the beginning survive,
  with gaps even there, and that the translation uses the reconstructed text
  from the preface inscription and five Haeinsa printing blocks.
* A. Charles Muller, "Wŏnhyo's Approach to Harmonization of the Mahayana
  Doctrines (Hwajaeng)," *Acta Koreana* 18.1 (2015), 9-44, especially 10-13,
  22-29, and 34, DOI 10.18399/acta.2015.18.1.001:
  https://doi.org/10.18399/acta.2015.18.1.001.  Muller describes comparison
  of divergent positions by uncovering their background, assumptions, aims,
  and precise point of divergence, while warning that "harmonization" can
  mislead if detached from that inquiry.

`LocalTheory.inScope` is a modern proxy for such differences of background,
aim, and domain; it is not a translation of a Wŏnhyo predicate.  The extant
text and the checked study do not supply counterparts for `Covers`,
`OverlapAgreement`, `GluedValue`, or `GluingCertificate`.  Those definitions
are explicitly a sheaf-like mathematical analogy, and no claim of historical
gluing or a complete reconstruction is made.  Transliterated titles and terms
follow Muller; the English descriptions are bounded paraphrases, not a new
translation of the fragmentary source.
-/

namespace BuddhistComparativeLogic.WonhyoHwajaeng

universe u v

/-! ## Local scope, valuation, and gluing -/

/-- A family of local theories.  `inScope` records which statements a context
addresses; `holds` is its local valuation/theory predicate. -/
structure LocalTheory (Context : Type u) (Statement : Type v) where
  inScope : Context -> Statement -> Prop
  holds : Context -> Statement -> Prop

namespace LocalTheory

variable {Context : Type u} {Statement : Type v}
    (theory : LocalTheory Context Statement)

/-- Two local theories agree wherever both are defined. -/
def OverlapAgreement : Prop :=
  forall {left right statement},
    theory.inScope left statement -> theory.inScope right statement ->
      (theory.holds left statement <-> theory.holds right statement)

/-- Every statement has at least one local context in which it can be
evaluated. -/
def Covers : Prop :=
  forall statement, exists context, theory.inScope context statement

/-- The candidate global valuation says that every local theory whose scope
contains the statement accepts it. -/
def GluedValue (statement : Statement) : Prop :=
  forall context, theory.inScope context statement ->
    theory.holds context statement

/-- `global` is a genuine common extension when restriction to every local
scope recovers that context's valuation in both directions. -/
def ExtendsAll (global : Statement -> Prop) : Prop :=
  forall context statement, theory.inScope context statement ->
    (global statement <-> theory.holds context statement)

/-- The certificate contains structural compatibility and coverage only.  It
contains no preferred statement and no proof of a local conclusion. -/
structure GluingCertificate : Prop where
  agreement : theory.OverlapAgreement
  coverage : theory.Covers

theorem global_extension_implies_overlap_agreement
    {global : Statement -> Prop} (extensionProof : theory.ExtendsAll global) :
    theory.OverlapAgreement := by
  intro left right statement leftScope rightScope
  exact (extensionProof left statement leftScope).symm.trans
    (extensionProof right statement rightScope)

/-- Agreement makes the explicit `GluedValue` restrict to every local theory.
This is the operative gluing theorem. -/
theorem glued_value_extends_all (certificate : theory.GluingCertificate) :
    theory.ExtendsAll theory.GluedValue := by
  intro context statement scope
  constructor
  · intro global
    exact global context scope
  · intro localProof otherContext otherScope
    exact (certificate.agreement scope otherScope).mp localProof

/-- Coverage chooses a real local site for every statement, and overlap
agreement identifies the glued value with that site's local value.  This
exposes the separate contribution of both certificate fields. -/
theorem glued_value_has_covered_restriction
    (certificate : theory.GluingCertificate) (statement : Statement) :
    exists context,
      theory.inScope context statement /\
        (theory.GluedValue statement <-> theory.holds context statement) := by
  rcases certificate.coverage statement with ⟨context, scope⟩
  exact ⟨context, scope,
    theory.glued_value_extends_all certificate context statement scope⟩

/-- A separately certified local conclusion survives gluing.  Coverage also
supplies a visible witness that the global statement is not outside every
local domain. -/
theorem preserves_local_conclusion
    (certificate : theory.GluingCertificate)
    {context : Context} {statement : Statement}
    (withinScope : theory.inScope context statement)
    (localProof : theory.holds context statement) :
    theory.GluedValue statement /\
      exists witness, theory.inScope witness statement := by
  constructor
  · exact (theory.glued_value_extends_all certificate
      context statement withinScope).mpr localProof
  · exact certificate.coverage statement

end LocalTheory

/-! ## Connection to the existing standpoint semantics -/

/-- Any formula-valued local family induces the repository's existing
`StandpointFrame`; accessibility remains separate from local truth. -/
def LocalTheory.toStandpointFrame
    {Context FormulaAtom : Type}
    (theory : LocalTheory Context (Fm FormulaAtom))
    (accessible : Context -> Context -> Prop) :
    StandpointFrame Context FormulaAtom where
  accessible := accessible
  asserted := theory.holds

theorem local_holds_iff_standpoint_convTrue
    {Context FormulaAtom : Type}
    (theory : LocalTheory Context (Fm FormulaAtom))
    (accessible : Context -> Context -> Prop)
    (context : Context) (statement : Fm FormulaAtom) :
    theory.holds context statement <->
      (theory.toStandpointFrame accessible).convTrue context statement := by
  rfl

/-! ## A three-context nonvacuous model -/

inductive HarmonyContext where
  | conventional
  | analytic
  | reconciled
  deriving DecidableEq, Repr

inductive HarmonyAtom where
  | appearance
  | dependent
  | ownBeing
  deriving DecidableEq, Repr

open HarmonyContext HarmonyAtom

def appearanceClaim : Fm HarmonyAtom := .atom .appearance
def dependenceClaim : Fm HarmonyAtom := .atom .dependent
def noOwnBeingClaim : Fm HarmonyAtom := .neg (.atom .ownBeing)

/-- The first two contexts have different domains.  The reconciled context
covers all formulas.  Truth is intentionally specified independently from
scope, making agreement an auditable fact rather than a field of the model. -/
def harmonyTheory : LocalTheory HarmonyContext (Fm HarmonyAtom) where
  inScope
    | .conventional, statement =>
        statement = appearanceClaim ∨ statement = dependenceClaim
    | .analytic, statement =>
        statement = dependenceClaim ∨ statement = noOwnBeingClaim
    | .reconciled, _ => True
  holds := fun _ statement =>
    statement = appearanceClaim ∨ statement = dependenceClaim ∨
      statement = noOwnBeingClaim

theorem harmony_overlap_agreement : harmonyTheory.OverlapAgreement := by
  intro left right statement leftScope rightScope
  simp [harmonyTheory]

theorem harmony_coverage : harmonyTheory.Covers := by
  intro statement
  exact ⟨.reconciled, trivial⟩

theorem harmonyCertificate : harmonyTheory.GluingCertificate where
  agreement := harmony_overlap_agreement
  coverage := harmony_coverage

theorem harmony_appearance_local :
    harmonyTheory.holds .conventional appearanceClaim := by
  exact Or.inl rfl

theorem harmony_appearance_scoped :
    harmonyTheory.inScope .conventional appearanceClaim :=
  Or.inl rfl

theorem harmony_model_is_nonvacuous :
    Nonempty (LocalTheory HarmonyContext (Fm HarmonyAtom)) /\
      harmonyTheory.inScope .conventional appearanceClaim /\
      ¬ harmonyTheory.inScope .conventional noOwnBeingClaim /\
      harmonyTheory.inScope .analytic noOwnBeingClaim /\
      harmonyTheory.GluedValue appearanceClaim /\
      HarmonyContext.conventional ≠ HarmonyContext.analytic := by
  refine ⟨⟨harmonyTheory⟩, Or.inl rfl, ?_, Or.inr rfl,
    (harmonyTheory.preserves_local_conclusion harmonyCertificate
      harmony_appearance_scoped harmony_appearance_local).1, by decide⟩
  simp [harmonyTheory, noOwnBeingClaim, appearanceClaim, dependenceClaim]

/-! ## Provenance-bearing local input -/

/-- The existing premise-certificate API records provenance for the local
proof; the gluing certificate itself still contains no conclusion. -/
def harmonyAppearanceEvidence :
    PremiseCertificates.Certified
      (harmonyTheory.holds .conventional appearanceClaim) :=
  PremiseCertificates.certifyInternal
    ``BuddhistComparativeLogic.WonhyoHwajaeng.harmony_appearance_local
    harmony_appearance_local

theorem provenance_bearing_local_conclusion_glues :
    harmonyTheory.holds .conventional appearanceClaim /\
      harmonyTheory.GluedValue appearanceClaim := by
  exact ⟨harmonyAppearanceEvidence.fact,
    (harmonyTheory.preserves_local_conclusion harmonyCertificate
      harmony_appearance_scoped harmonyAppearanceEvidence.fact).1⟩

/-- The same positive model is an actual `StandpointFrame`, not merely a
prose analogy. -/
def harmonyStandpoint : StandpointFrame HarmonyContext HarmonyAtom :=
  LocalTheory.toStandpointFrame
    (Context := HarmonyContext) (FormulaAtom := HarmonyAtom)
    harmonyTheory (fun _ _ => True)

theorem glued_appearance_is_conventionally_asserted :
    harmonyTheory.GluedValue appearanceClaim /\
      harmonyStandpoint.convTrue .conventional appearanceClaim := by
  exact ⟨(harmonyTheory.preserves_local_conclusion harmonyCertificate
      harmony_appearance_scoped harmony_appearance_local).1,
    (local_holds_iff_standpoint_convTrue harmonyTheory
      (fun _ _ => True) HarmonyContext.conventional appearanceClaim).mp
      harmony_appearance_local⟩

/-! ## Boundary model: context erasure globalizes opposed formulas -/

inductive BoundaryContext where
  | conventional
  | ultimate
  deriving DecidableEq, Repr

inductive BoundaryAtom where
  | conditioned
  deriving DecidableEq, Repr

def boundaryPositive : Fm BoundaryAtom := .atom .conditioned
def boundaryNegative : Fm BoundaryAtom := .neg boundaryPositive

/-- Each context asserts exactly one of the opposed formulas. -/
def boundaryTheory : LocalTheory BoundaryContext (Fm BoundaryAtom) where
  inScope
    | .conventional, statement => statement = boundaryPositive
    | .ultimate, statement => statement = boundaryNegative
  holds
    | .conventional, statement => statement = boundaryPositive
    | .ultimate, statement => statement = boundaryNegative

/-- Context erasure takes the union of the local theories. -/
def erasedBoundaryTheory (statement : Fm BoundaryAtom) : Prop :=
  exists context, boundaryTheory.holds context statement

theorem each_boundary_context_avoids_the_opposed_pair :
    forall context,
      ¬ (boundaryTheory.holds context boundaryPositive /\
        boundaryTheory.holds context boundaryNegative) := by
  intro context
  cases context <;>
    simp [boundaryTheory, boundaryPositive, boundaryNegative]

/-- Dropping the context coordinate puts `P` and the formula `¬P` into one
erased theory even though neither local context contains both. -/
theorem erasing_context_collects_P_and_not_P :
    erasedBoundaryTheory boundaryPositive /\
      erasedBoundaryTheory boundaryNegative /\
      boundaryPositive ≠ boundaryNegative := by
  refine ⟨⟨.conventional, rfl⟩, ⟨.ultimate, rfl⟩, ?_⟩
  decide

/-! ## Failed overlap blocks a global extension -/

inductive ConflictContext where
  | left
  | right
  deriving DecidableEq, Repr

inductive ConflictStatement where
  | disputed
  deriving DecidableEq, Repr

/-- Both contexts cover the same statement, but only the left accepts it. -/
def conflictTheory : LocalTheory ConflictContext ConflictStatement where
  inScope := fun _ _ => True
  holds
    | .left, _ => True
    | .right, _ => False

theorem conflict_has_coverage : conflictTheory.Covers := by
  intro statement
  exact ⟨.left, trivial⟩

theorem conflict_fails_overlap_agreement :
    ¬ conflictTheory.OverlapAgreement := by
  intro agreement
  have clash := agreement
    (left := ConflictContext.left)
    (right := ConflictContext.right)
    (statement := ConflictStatement.disputed)
    trivial trivial
  exact clash.mp trivial

/-- Coverage is present, so the obstruction is specifically the failed
agreement on the nonempty overlap.  Consequently there is neither a gluing
certificate nor any proposition-valued common extension. -/
theorem failed_overlap_blocks_gluing :
    conflictTheory.Covers /\
      ¬ Nonempty conflictTheory.GluingCertificate /\
      ¬ exists global : ConflictStatement -> Prop,
        conflictTheory.ExtendsAll global := by
  refine ⟨conflict_has_coverage, ?_, ?_⟩
  · rintro ⟨certificate⟩
    exact conflict_fails_overlap_agreement certificate.agreement
  · rintro ⟨global, extensionProof⟩
    exact conflict_fails_overlap_agreement
      (conflictTheory.global_extension_implies_overlap_agreement extensionProof)

end BuddhistComparativeLogic.WonhyoHwajaeng
