/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Nyaya.Nyaya

/-!
# Anyathanupapatti and a two-member inference

This module gives a bounded modal reconstruction of the Jaina criterion
`anyathanupapatti`, the reason's inability to occur otherwise than with the
thesis.  Actual-world inclusion and absence of an accessible countercase are
different predicates.  A two-member certificate carries the reason at the
subject and the modal link at that subject; a global bridge is explicitly
required before the certificate is exported to the existing Nyaya semantic
interface.

This is a proof-theoretic model of one use of the criterion, not a translation
of every Jaina theory of inference or a claim that all Jaina authors used one
fixed modal semantics.  The two public members represented here are the
thesis and reason; historical discussions may embed them in richer dialectical
settings.

Sources and orientation:

* https://plato.stanford.edu/entries/jaina-philosophy/
* https://gretil.sub.uni-goettingen.de/gretil/corpustei/transformations/html/sa_siddhasenamahAmati-nyAyAvatAra-comm.htm
-/

namespace BuddhistComparativeLogic.JainaInference

open BuddhistComparativeLogic.Hetucakra

universe u v

/-! ## Actual and modal entailment -/

/-- A distinguished actual world and its accessible alternatives.  The only
frame condition needed for subject-level soundness is accessibility of the
actual world to itself.  Because `AnyathanupapattiAt` is stored as the
negation of a counterexample, the elimination theorem below uses Lean's
ambient classical reasoning. -/
structure ModalModel (World : Type u) (Locus : Type v) where
  actual : World
  accessible : World -> World -> Prop
  actualAccessible : accessible actual actual
  paksa : Locus
  reason : World -> Locus -> Prop
  thesis : World -> Locus -> Prop

namespace ModalModel

variable {World : Type u} {Locus : Type v}

/-- Forget alternative worlds and expose the ordinary actual-world inference
shape used elsewhere in the repository. -/
def actualArgument (model : ModalModel World Locus) : Anumana Locus where
  paksa := model.paksa
  reason := model.reason model.actual
  sadhya := model.thesis model.actual

/-- Extensional inclusion at the distinguished actual world. -/
def ActualInclusion (model : ModalModel World Locus) : Prop :=
  BuddhistComparativeLogic.InferenceScope.Pervasion model.actualArgument

/-- An accessible world in which this locus has the reason without the
thesis. -/
def OtherwisePossibleAt (model : ModalModel World Locus)
    (object : Locus) : Prop :=
  exists world, model.accessible model.actual world /\
    model.reason world object /\ ¬ model.thesis world object

/-- `AnyathanupapattiAt` literally records inability to find an accessible
reason-without-thesis case at one locus. -/
def AnyathanupapattiAt (model : ModalModel World Locus)
    (object : Locus) : Prop :=
  ¬ model.OtherwisePossibleAt object

/-- The stronger, globally quantified modal link needed to recover ordinary
pervasion over every actual-world locus. -/
def GlobalAnyathanupapatti (model : ModalModel World Locus) : Prop :=
  forall object, model.AnyathanupapattiAt object

/-- Classically eliminate a possible actual counterexample using reflexive
accessibility. -/
theorem thesis_of_reason_and_anyathanupapatti
    (model : ModalModel World Locus) {object : Locus}
    (reason : model.reason model.actual object)
    (link : model.AnyathanupapattiAt object) :
    model.thesis model.actual object := by
  apply Classical.byContradiction
  intro lacksThesis
  exact link ⟨model.actual, model.actualAccessible, reason, lacksThesis⟩

/-- A global modal link implies actual inclusion by reflexive accessibility.
The converse will fail in the finite two-world model below. -/
theorem actualInclusion_of_globalAnyathanupapatti
    (model : ModalModel World Locus)
    (link : model.GlobalAnyathanupapatti) : model.ActualInclusion := by
  intro object reason
  exact model.thesis_of_reason_and_anyathanupapatti reason (link object)

end ModalModel

/-! ## Two public members and their semantic certificate -/

inductive Member where
  | thesis
  | reason
  deriving DecidableEq, Repr

def twoMemberOrder : List Member := [.thesis, .reason]

/-- The public order is retained separately from its proof payload.  No
positive comparison example is a field of this certificate. -/
structure TwoMemberInference {World : Type u} {Locus : Type v}
    (model : ModalModel World Locus) where
  members : List Member
  ordered : members = twoMemberOrder
  subjectReason : model.reason model.actual model.paksa
  modalLink : model.AnyathanupapattiAt model.paksa

namespace TwoMemberInference

variable {World : Type u} {Locus : Type v}
  {model : ModalModel World Locus}

/-- Subject possession and inability-to-be-otherwise at that subject suffice
for the stated thesis. -/
theorem sound (inference : TwoMemberInference model) :
    model.thesis model.actual model.paksa :=
  model.thesis_of_reason_and_anyathanupapatti
    inference.subjectReason inference.modalLink

end TwoMemberInference

/-- An independent certificate of the modal link at every locus.  It is
supplied alongside a subject-specific two-member argument when exporting that
argument to an interface whose pervasion field is global. -/
structure GlobalBridge {World : Type u} {Locus : Type v}
    (model : ModalModel World Locus) : Prop where
  modalLink : model.GlobalAnyathanupapatti

namespace GlobalBridge

variable {World : Type u} {Locus : Type v}
  {model : ModalModel World Locus}

theorem toActualInclusion (bridge : GlobalBridge model) :
    model.ActualInclusion :=
  model.actualInclusion_of_globalAnyathanupapatti bridge.modalLink

end GlobalBridge

/-- Once the global bridge is supplied, the two-member certificate converts
to the repository's ordinary Nyaya semantic proof.  The positive-example
field used by a public `Udaharana` is not needed by `SemanticProof`. -/
theorem TwoMemberInference.toNyayaSemanticProof
    {World : Type u} {Locus : Type v}
    {model : ModalModel World Locus}
    (inference : TwoMemberInference model) (bridge : GlobalBridge model) :
    BuddhistComparativeLogic.Nyaya.SemanticProof model.actualArgument where
  subjectReason := inference.subjectReason
  pervasion := bridge.toActualInclusion

/-! ## Actual agreement is weaker than modal pervasion -/

inductive CounterWorld where
  | actual
  | alternative
  deriving DecidableEq, Repr

inductive CounterLocus where
  | subject
  deriving DecidableEq, Repr

open CounterWorld CounterLocus

/-- The sole locus has both reason and thesis in the actual world.  In the
accessible alternative it retains the reason and loses the thesis. -/
def actualAgreementModel : ModalModel CounterWorld CounterLocus where
  actual := .actual
  accessible := fun source _target => source = .actual
  actualAccessible := rfl
  paksa := .subject
  reason := fun _world _object => True
  thesis
    | .actual, _ => True
    | .alternative, _ => False

theorem actual_agreement_is_inclusion :
    actualAgreementModel.ActualInclusion := by
  intro object _reason
  cases object
  trivial

theorem alternative_is_countercase :
    actualAgreementModel.OtherwisePossibleAt .subject := by
  exact ⟨.alternative, rfl, trivial, by simp [actualAgreementModel]⟩

theorem actual_inclusion_does_not_entail_modal_pervasion :
    actualAgreementModel.reason .actual .subject /\
      actualAgreementModel.thesis .actual .subject /\
      actualAgreementModel.ActualInclusion /\
      ¬ actualAgreementModel.AnyathanupapattiAt .subject /\
      ¬ actualAgreementModel.GlobalAnyathanupapatti := by
  refine ⟨trivial, trivial, actual_agreement_is_inclusion, ?_, ?_⟩
  · intro modalLink
    exact modalLink alternative_is_countercase
  · intro globalLink
    exact globalLink .subject alternative_is_countercase

/-- The same finite model states the failed implication directly. -/
theorem actual_inclusion_is_not_sufficient_for_modal_link :
    ¬ (actualAgreementModel.ActualInclusion ->
      actualAgreementModel.AnyathanupapattiAt .subject) := by
  intro implication
  exact (implication actual_agreement_is_inclusion)
    alternative_is_countercase

/-! ## A sound inference without a distinct positive example -/

inductive SoleWorld where
  | actual
  deriving DecidableEq, Repr

inductive SoleLocus where
  | subject
  deriving DecidableEq, Repr

/-- Both predicates hold at the only world and locus.  The singleton locus
makes a positive comparison distinct from the subject impossible. -/
def solitaryModel : ModalModel SoleWorld SoleLocus where
  actual := .actual
  accessible := fun _ _ => True
  actualAccessible := trivial
  paksa := .subject
  reason := fun _ _ => True
  thesis := fun _ _ => True

theorem solitaryLink : solitaryModel.AnyathanupapattiAt .subject := by
  rintro ⟨world, _accessible, _reason, lacksThesis⟩
  exact lacksThesis trivial

def solitaryTwoMember : TwoMemberInference solitaryModel where
  members := twoMemberOrder
  ordered := rfl
  subjectReason := trivial
  modalLink := solitaryLink

theorem solitaryGlobalBridge : GlobalBridge solitaryModel where
  modalLink := by
    intro object
    cases object
    exact solitaryLink

theorem solitarySemanticProof :
    BuddhistComparativeLogic.Nyaya.SemanticProof solitaryModel.actualArgument :=
  solitaryTwoMember.toNyayaSemanticProof solitaryGlobalBridge

theorem solitary_has_no_distinct_positive_example :
    ¬ Nonempty
      (BuddhistComparativeLogic.Nyaya.PositiveExample solitaryModel.actualArgument) := by
  rintro ⟨positive⟩
  cases positive.witness
  exact positive.distinct rfl

/-- The two-member argument derives its thesis and exports a semantic proof
even though the singleton domain cannot contain a distinct positive example.
This establishes only that such an example is not a premise of this formal
certificate, not that examples lack historical or pedagogical roles. -/
theorem two_member_inference_needs_no_positive_example :
    solitaryModel.thesis solitaryModel.actual solitaryModel.paksa /\
      BuddhistComparativeLogic.Nyaya.SemanticProof solitaryModel.actualArgument /\
      ¬ Nonempty
        (BuddhistComparativeLogic.Nyaya.PositiveExample solitaryModel.actualArgument) := by
  exact ⟨solitaryTwoMember.sound, solitarySemanticProof,
    solitary_has_no_distinct_positive_example⟩

end BuddhistComparativeLogic.JainaInference
