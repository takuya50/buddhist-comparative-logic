/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Nyaya.Nyaya
import BuddhistComparativeLogic.Buddhist.Pramana.Hetucakra
import BuddhistComparativeLogic.Buddhist.Pramana.Dharmakirti

/-!
# A scoped inference audit motivated by the Tattvacintamani

This module isolates four proof-theoretic notions useful when reading the
inference discussions associated with Gangesa's *Tattvacintamani*: universal
reason-to-thesis inclusion (`Vyapti`), its reflective application to the
subject (`Paramarsa`), a condition exposing a counterinstance to an
unqualified inclusion (`Upadhi`), and three corresponding defects of a
reason.  These are deliberately extensional interfaces over the existing
`Anumana` model, not a translation of the Sanskrit text or a claim that the
historical notions have only these components.

An `UpadhiDiagnostic` below follows the standard extensional pattern: the
condition covers the thesis but fails to cover a reason-bearing case.  That
diagnoses a counterinstance to the unqualified inclusion.  A separate
`RestrictionRepair` records the stronger rule needed to recover an inference
after adding the condition.  Soundness at the disputed subject additionally
requires that both the original reason and the condition hold there.
-/

namespace BuddhistComparativeLogic.Tattvacintamani

open BuddhistComparativeLogic.Hetucakra

/-- Reuse the global scope audited by `InferenceScope` and exposed by the
Nyaya public-inference module. -/
abbrev Vyapti {L : Type u} (argument : Anumana L) : Prop :=
  BuddhistComparativeLogic.Nyaya.Pervasion argument

/-- Restrict possession of a reason by one stated condition.  The subject and
thesis predicates are unchanged. -/
def restrictReason {L : Type u} (argument : Anumana L)
    (condition : L -> Prop) : Anumana L where
  paksa := argument.paksa
  sadhya := argument.sadhya
  reason := fun x => argument.reason x ∧ condition x

/-- The explicitly conditional reason-to-thesis rule. -/
def ConditionalVyapti {L : Type u} (argument : Anumana L)
    (condition : L -> Prop) : Prop :=
  forall x, argument.reason x -> condition x -> argument.sadhya x

theorem restricted_vyapti_iff_conditional {L : Type u}
    (argument : Anumana L) (condition : L -> Prop) :
    Vyapti (restrictReason argument condition) <->
      ConditionalVyapti argument condition := by
  constructor
  · intro restricted x reason hasCondition
    exact restricted x ⟨reason, hasCondition⟩
  · intro conditional x reason
    exact conditional x reason.1 reason.2

/-- The standard extensional diagnostic pattern: the condition covers every
thesis case but not every reason case.  No claim is made that this record
exhausts Gaṅgeśa's analyses of `upadhi`. -/
structure UpadhiDiagnostic {L : Type u} (argument : Anumana L) where
  condition : L -> Prop
  sadhyaVyapaka : ∀ x, argument.sadhya x -> condition x
  witness : L
  witnessReason : argument.reason witness
  witnessLacksCondition : ¬ condition witness

namespace UpadhiDiagnostic

variable {L : Type u} {argument : Anumana L}

/-- Failure of the thesis at the reason-bearing witness is derived from the
coverage condition; it is not stored as an independent premise. -/
theorem witness_lacks_thesis (audit : UpadhiDiagnostic argument) :
    ¬ argument.sadhya audit.witness :=
  fun thesis => audit.witnessLacksCondition
    (audit.sadhyaVyapaka audit.witness thesis)

/-- The derived counterinstance defeats the unqualified universal rule. -/
theorem defeats_unrestricted_vyapti (audit : UpadhiDiagnostic argument) :
    ¬ Vyapti argument := by
  intro unrestricted
  exact audit.witness_lacks_thesis
    (unrestricted audit.witness audit.witnessReason)

end UpadhiDiagnostic

/-- Repair is stronger than diagnosis: it explicitly states that the
conditioned reason entails the thesis. -/
structure RestrictionRepair {L : Type u} {argument : Anumana L}
    (diagnostic : UpadhiDiagnostic argument) : Prop where
  conditionalVyapti : ConditionalVyapti argument diagnostic.condition

namespace RestrictionRepair

variable {L : Type u} {argument : Anumana L}
  {diagnostic : UpadhiDiagnostic argument}

/-- Adding a separately certified repair condition yields a genuine universal
rule for the restricted reason predicate. -/
theorem repairs_restricted_vyapti
    (repair : RestrictionRepair diagnostic) :
    Vyapti (restrictReason argument diagnostic.condition) :=
  (restricted_vyapti_iff_conditional argument diagnostic.condition).mpr
    repair.conditionalVyapti

end RestrictionRepair

/-- A Dharmakirti-style model whose explicit `vyapti` proposition is exactly
the conditional rule and whose reason is the restricted reason. -/
def conditionedModel {L : Type u} (argument : Anumana L)
    (condition : L -> Prop) : BuddhistComparativeLogic.Dharmakirti.Model L where
  paksa := argument.paksa
  sadhya := argument.sadhya
  reason := fun x => argument.reason x ∧ condition x
  vyapti := ConditionalVyapti argument condition
  vyapti_iff := by
    constructor
    · intro conditional x reason
      exact conditional x reason.1 reason.2
    · intro unrestricted x reason hasCondition
      exact unrestricted x ⟨reason, hasCondition⟩

/-- A small proof certificate for reflective application: the reason occurs
at the disputed subject and its unrestricted inclusion has been supplied.
This record formalizes only the inferential payload used below. -/
structure Paramarsa {L : Type u} (argument : Anumana L) : Prop where
  subjectReason : argument.reason argument.paksa
  vyapti : Vyapti argument

namespace Paramarsa

variable {L : Type u} {argument : Anumana L}

/-- The certificate is also a semantic proof for the existing five-member
Nyaya interface. -/
theorem toNyayaSemanticProof (reflection : Paramarsa argument) :
    BuddhistComparativeLogic.Nyaya.SemanticProof argument where
  subjectReason := reflection.subjectReason
  pervasion := reflection.vyapti

theorem sound (reflection : Paramarsa argument) :
    argument.sadhya argument.paksa :=
  reflection.toNyayaSemanticProof.sound

theorem rules_out_unestablished_subject_reason
    (reflection : Paramarsa argument) :
    ¬ (¬ argument.reason argument.paksa) :=
  fun failure => failure reflection.subjectReason

theorem rules_out_counterexample (reflection : Paramarsa argument) :
    ¬ (exists x, argument.reason x ∧ ¬ argument.sadhya x) := by
  rintro ⟨x, reason, failure⟩
  exact failure (reflection.vyapti x reason)

theorem rules_out_contrary_pervasion (reflection : Paramarsa argument) :
    ¬ (forall x, argument.reason x -> ¬ argument.sadhya x) := by
  intro contrary
  exact contrary argument.paksa reflection.subjectReason reflection.sound

end Paramarsa

/-! ## Three explicitly represented defects -/

/-- Three failures tracked by this reconstruction.  The constructors are
diagnostic proof objects and do not claim to enumerate every historical
classification of pseudo-reasons. -/
inductive Hetvabhasa {L : Type u} (argument : Anumana L) : Type u where
  | unestablished (failure : ¬ argument.reason argument.paksa)
  | counterexample (witness : L) (hasReason : argument.reason witness)
      (lacksThesis : ¬ argument.sadhya witness)
  | contrary (opposition : forall x,
      argument.reason x -> ¬ argument.sadhya x)

namespace Paramarsa

/-- A complete reflective-application certificate is incompatible with each
of the three registered defect witnesses. -/
theorem excludes_registered_hetvabhasa {L : Type u}
    {argument : Anumana L} (reflection : Paramarsa argument) :
    ¬ Nonempty (Hetvabhasa argument) := by
  rintro ⟨defect⟩
  cases defect with
  | unestablished failure =>
      exact failure reflection.subjectReason
  | counterexample witness hasReason lacksThesis =>
      exact lacksThesis (reflection.vyapti witness hasReason)
  | contrary opposition =>
      exact opposition argument.paksa reflection.subjectReason
        reflection.sound

end Paramarsa

/-- A conditional certificate recovers reflective application only when the
condition is also established at the subject. -/
theorem RestrictionRepair.toConditionedParamarsa
    {L : Type u} {argument : Anumana L}
    {diagnostic : UpadhiDiagnostic argument}
    (repair : RestrictionRepair diagnostic)
    (subjectReason : argument.reason argument.paksa)
    (subjectCondition : diagnostic.condition argument.paksa) :
    Paramarsa (restrictReason argument diagnostic.condition) where
  subjectReason := And.intro subjectReason subjectCondition
  vyapti := repair.repairs_restricted_vyapti

/-- Condition addition restores subject-level soundness through the existing
Dharmakirti `vyapti_sound` theorem. -/
theorem sound_after_adding_condition {L : Type u}
    {argument : Anumana L} {diagnostic : UpadhiDiagnostic argument}
    (repair : RestrictionRepair diagnostic)
    (subjectReason : argument.reason argument.paksa)
    (subjectCondition : diagnostic.condition argument.paksa) :
    argument.sadhya argument.paksa := by
  exact (conditionedModel argument diagnostic.condition).vyapti_sound
    repair.conditionalVyapti (And.intro subjectReason subjectCondition)

/-! ## Finite condition audit -/

inductive Site where
  | wetHearth
  | wetKitchen
  | dryLamp
  | pond
  deriving DecidableEq, Repr

open Site

/-- Fire is the reason at two wet sites and at a dry lamp; smoke is asserted
only at the wet sites. -/
def fireSmoke : Anumana Site where
  paksa := .wetHearth
  reason := fun x =>
    x = .wetHearth ∨ x = .wetKitchen ∨ x = .dryLamp
  sadhya := fun x => x = .wetHearth ∨ x = .wetKitchen

def wetFuel : Site -> Prop := fun x =>
  x = .wetHearth ∨ x = .wetKitchen ∨ x = .pond

def wetFuelDiagnostic : UpadhiDiagnostic fireSmoke where
  condition := wetFuel
  sadhyaVyapaka := by
    intro x thesis
    rcases thesis with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  witness := .dryLamp
  witnessReason := Or.inr (Or.inr rfl)
  witnessLacksCondition := by simp [wetFuel]

theorem wetFuelRepair : RestrictionRepair wetFuelDiagnostic where
  conditionalVyapti := by
    intro x reason wet
    change wetFuel x at wet
    cases x <;> simp_all [fireSmoke, wetFuel]

theorem fire_does_not_unconditionally_pervade_smoke :
    ¬ Vyapti fireSmoke :=
  wetFuelDiagnostic.defeats_unrestricted_vyapti

theorem wet_condition_recovers_subject_thesis :
    fireSmoke.sadhya fireSmoke.paksa :=
  sound_after_adding_condition wetFuelRepair (Or.inl rfl) (Or.inl rfl)

theorem conditioned_fire_marks :
    (restrictReason fireSmoke wetFuel).trairupya := by
  have subjectReason :
      (restrictReason fireSmoke wetFuel).paksadharmata :=
    And.intro (Or.inl rfl) (Or.inl rfl)
  have similarReason :
      (restrictReason fireSmoke wetFuel).anvaya := by
    refine ⟨.wetKitchen, ?_, ?_⟩
    · exact ⟨by decide, Or.inr rfl⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
  have dissimilarExclusion :
      (restrictReason fireSmoke wetFuel).vyatireka :=
    (conditionedModel fireSmoke wetFuel).vyapti_gives_vyatireka
      wetFuelRepair.conditionalVyapti
  exact ⟨subjectReason, similarReason, dissimilarExclusion⟩

/-- The repaired reason also passes the existing Hetucakra verdict, with a
distinct positive comparison site. -/
theorem conditioned_fire_wheel_valid :
    (restrictReason fireSmoke wetFuel).wheelVerdict = .valid := by
  exact (restrictReason fireSmoke wetFuel).wheel_valid_iff.mpr
    ⟨conditioned_fire_marks.2.1, conditioned_fire_marks.2.2⟩

/-- The finite model contains the disputed subject, a distinct positive
comparison, a reason-bearing counterinstance to the unrestricted rule, and a
wet site with neither reason nor thesis.  The latter keeps the repair
condition extension distinct from the conclusion. -/
theorem condition_audit_nonvacuous :
    (fireSmoke.reason .wetHearth ∧ wetFuel .wetHearth ∧
      fireSmoke.sadhya .wetHearth) ∧
    (fireSmoke.reason .wetKitchen ∧ wetFuel .wetKitchen ∧
      fireSmoke.sadhya .wetKitchen) ∧
    (fireSmoke.reason .dryLamp ∧ ¬ wetFuel .dryLamp ∧
      ¬ fireSmoke.sadhya .dryLamp) ∧
    (wetFuel .pond ∧ ¬ fireSmoke.reason .pond ∧
      ¬ fireSmoke.sadhya .pond) := by
  simp [fireSmoke, wetFuel]

/-! ## Missing-premise and converse audits -/

/-- Changing only the disputed subject to the dry lamp leaves the conditional
rule and subject reason intact.  The subject condition and conclusion both
fail, so a conditional inclusion cannot silently supply its own antecedent. -/
def dryLampSubject : Anumana Site where
  paksa := .dryLamp
  reason := fireSmoke.reason
  sadhya := fireSmoke.sadhya

theorem conditional_vyapti_needs_subject_condition :
    ConditionalVyapti dryLampSubject wetFuel ∧
      dryLampSubject.reason dryLampSubject.paksa ∧
      ¬ wetFuel dryLampSubject.paksa ∧
      ¬ dryLampSubject.sadhya dryLampSubject.paksa := by
  refine ⟨?_, Or.inr (Or.inr rfl), ?_, ?_⟩
  · intro x reason wet
    exact wetFuelRepair.conditionalVyapti x reason wet
  · simp [dryLampSubject, wetFuel]
  · simp [dryLampSubject, fireSmoke]

/-- Reuse Nyaya's finite model: universal inclusion and a positive example
do not prove the subject thesis when subject application is absent. -/
theorem vyapti_without_subject_application_is_insufficient :
    Vyapti BuddhistComparativeLogic.Nyaya.missingApplication ∧
      (exists x,
        BuddhistComparativeLogic.Nyaya.missingApplication.reason x ∧
        BuddhistComparativeLogic.Nyaya.missingApplication.sadhya x) ∧
      ¬ BuddhistComparativeLogic.Nyaya.missingApplication.reason
        BuddhistComparativeLogic.Nyaya.missingApplication.paksa ∧
      ¬ BuddhistComparativeLogic.Nyaya.missingApplication.sadhya
        BuddhistComparativeLogic.Nyaya.missingApplication.paksa := by
  refine ⟨BuddhistComparativeLogic.Nyaya.missingApplicationUdaharana.pervasion,
    ?_, ?_, ?_⟩
  · exact ⟨.kitchen, rfl, rfl⟩
  · simp [BuddhistComparativeLogic.Nyaya.missingApplication]
  · simp [BuddhistComparativeLogic.Nyaya.missingApplication]

/-- A true subject thesis can be accidental relative to the proposed reason:
the dry lamp blocks the converse from a true conclusion to universal
`vyapti`, and hence to a `Paramarsa` certificate. -/
def accidentalConclusion : Anumana Site where
  paksa := .wetHearth
  reason := fun x => x = .wetHearth ∨ x = .dryLamp
  sadhya := fun x => x = .wetHearth

theorem subject_thesis_does_not_entail_vyapti_or_paramarsa :
    accidentalConclusion.sadhya accidentalConclusion.paksa ∧
      ¬ Vyapti accidentalConclusion ∧
      ¬ Nonempty (Paramarsa accidentalConclusion) := by
  have noVyapti : ¬ Vyapti accidentalConclusion := by
    intro universal
    have falseAtLamp : accidentalConclusion.sadhya .dryLamp :=
      universal .dryLamp (Or.inr rfl)
    cases falseAtLamp
  refine ⟨rfl, noVyapti, ?_⟩
  rintro ⟨reflection⟩
  exact noVyapti reflection.vyapti

end BuddhistComparativeLogic.Tattvacintamani
