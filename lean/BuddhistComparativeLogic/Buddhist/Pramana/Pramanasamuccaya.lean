/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis
import BuddhistComparativeLogic.Buddhist.Pramana.Apoha

/-!
# A restrained Pramanasamuccaya synthesis

This module formalizes a small proof architecture associated with Dignaga's
*Pramanasamuccaya*.  It does not encode the Sanskrit text or claim that one
modern semantics is its uniquely correct interpretation.  Instead it keeps
four interfaces separate:

* perception presents a datum under an explicitly assumed nonconceptuality
  predicate;
* a project-level subject warrant carries subject possession and pervasion;
* a certified public argument adds a positive comparison example;
* concept extension can be selected by an explicitly supplied apoha
  grounding.

The final finite models audit three tempting shortcuts.  An undifferentiated
appearance does not determine a conceptual classification.  The three marks
and a valid wheel cell do not establish the thesis at the subject without
pervasion.  Finally, a marked public presentation and a subject-level
deductive warrant are distinct project interfaces: either can exist when the
other does not.  These interfaces are not asserted to be exact definitions of
Dignaga's historical `svarthanumana` and `pararthanumana` categories.
-/

namespace BuddhistComparativeLogic.Pramanasamuccaya

open BuddhistComparativeLogic.Hetucakra

/-! ## Two explicit evidence interfaces -/

/-- A minimal semantic interface for perception.  `nonconceptual` is a
premise of this model, not a theorem extracted from raw data. -/
structure PerceptionModel (Object : Type u) (Datum : Type v) where
  appearance : Object -> Datum
  nonconceptual : Datum -> Prop

/-- Evidence supplied by the perceptual interface at one object. -/
structure PerceptualEvidence {Object : Type u} {Datum : Type v}
    (model : PerceptionModel Object Datum) (object : Object) where
  datum : Datum
  presented : model.appearance object = datum
  nonconceptual : model.nonconceptual datum

namespace PerceptualEvidence

variable {Object : Type u} {Datum : Type v}
  {model : PerceptionModel Object Datum} {object : Object}

theorem appearance_is_nonconceptual
    (evidence : PerceptualEvidence model object) :
    model.nonconceptual (model.appearance object) := by
  rw [evidence.presented]
  exact evidence.nonconceptual

end PerceptualEvidence

/-- An optional reflexive-awareness layer.  Its law is an explicit extra
field, so the following result cannot be read as deriving self-awareness from
the bare perception interface. -/
structure SelfAwarenessModel (Object : Type u) (Datum : Type v)
    extends PerceptionModel Object Datum where
  aware : Datum -> Prop
  reflexive : forall object,
    toPerceptionModel.nonconceptual (toPerceptionModel.appearance object) ->
      aware (toPerceptionModel.appearance object)

theorem self_awareness_of_explicit_model
    {Object : Type u} {Datum : Type v}
    (model : SelfAwarenessModel Object Datum) (object : Object)
    (evidence : PerceptualEvidence model.toPerceptionModel object) :
    model.aware evidence.datum := by
  rw [← evidence.presented]
  exact model.reflexive object evidence.appearance_is_nonconceptual

/-- The inference interface is the already audited subject reason plus
pervasion certificate. -/
abbrev InferentialEvidence {L : Type u}
    (model : BuddhistComparativeLogic.Dharmakirti.Model L) :=
  PramanaSynthesis.DeductiveCertificate model

inductive PramanaKind where
  | perception
  | inference
  deriving DecidableEq, Repr

/-- A tagged evidence space prevents perceptual data and inferential
certificates from being silently identified. -/
inductive Evidence {Object : Type u} {Datum : Type v} {L : Type w}
    (perception : PerceptionModel Object Datum)
    (inference : BuddhistComparativeLogic.Dharmakirti.Model L) where
  | perceptual (object : Object) (proof : PerceptualEvidence perception object)
  | inferential (proof : InferentialEvidence inference)

namespace Evidence

variable {Object : Type u} {Datum : Type v} {L : Type w}
  {perception : PerceptionModel Object Datum}
  {inference : BuddhistComparativeLogic.Dharmakirti.Model L}

def kind : Evidence perception inference -> PramanaKind
  | .perceptual _ _ => .perception
  | .inferential _ => .inference

@[simp] theorem kind_perceptual (object : Object)
    (proof : PerceptualEvidence perception object) :
    kind (.perceptual object proof : Evidence perception inference) =
      .perception :=
  rfl

@[simp] theorem kind_inferential (proof : InferentialEvidence inference) :
    kind (.inferential proof : Evidence perception inference) = .inference :=
  rfl

theorem perceptual_ne_inferential (object : Object)
    (perceptualProof : PerceptualEvidence perception object)
    (inferentialProof : InferentialEvidence inference) :
    (.perceptual object perceptualProof : Evidence perception inference) ≠
      .inferential inferentialProof := by
  intro equality
  have kindEquality := congrArg kind equality
  cases kindEquality

end Evidence

/-! ## Subject warrant and public presentation -/

/-- The project-level subject warrant contains exactly the deductive
obligations at the subject.  It is not a definition of the historical
`svarthanumana` category. -/
abbrev SubjectWarrant {L : Type u}
    (model : BuddhistComparativeLogic.Dharmakirti.Model L) :=
  PramanaSynthesis.DeductiveCertificate model

/-- A certified public argument adds a positive comparison example to the
subject warrant.  It is not a definition of the historical
`pararthanumana` category. -/
abbrev CertifiedPublicArgument {L : Type u}
    (model : BuddhistComparativeLogic.Dharmakirti.Model L) :=
  PramanaSynthesis.DialecticalCertificate model

/-- A weaker marked public presentation records the three displayed marks.
It does not silently add global pervasion. -/
structure PublicPresentation {L : Type u}
    (model : BuddhistComparativeLogic.Dharmakirti.Model L) : Prop where
  subjectReason : model.toAnumana.paksadharmata
  positiveExample : model.toAnumana.anvaya
  negativeExampleRule : model.toAnumana.vyatireka

namespace PublicPresentation

variable {L : Type u} {model : BuddhistComparativeLogic.Dharmakirti.Model L}

theorem trairupya (presentation : PublicPresentation model) :
    model.toAnumana.trairupya :=
  ⟨presentation.subjectReason, presentation.positiveExample,
    presentation.negativeExampleRule⟩

theorem wheel_valid (presentation : PublicPresentation model) :
    model.toAnumana.wheelVerdict = .valid :=
  model.toAnumana.wheel_valid_iff.mpr
    ⟨presentation.positiveExample, presentation.negativeExampleRule⟩

end PublicPresentation

theorem subject_warrant_is_sound {L : Type u}
    {model : BuddhistComparativeLogic.Dharmakirti.Model L}
    (warrant : SubjectWarrant model) :
    model.sadhya model.paksa :=
  PramanaSynthesis.deductive_sound warrant

theorem certified_public_argument_contains_subject_warrant {L : Type u}
    {model : BuddhistComparativeLogic.Dharmakirti.Model L}
    (argument : CertifiedPublicArgument model) :
    SubjectWarrant model :=
  argument.toDeductiveCertificate

theorem certified_public_argument_is_public {L : Type u}
    {model : BuddhistComparativeLogic.Dharmakirti.Model L}
    (argument : CertifiedPublicArgument model) :
    PublicPresentation model where
  subjectReason := argument.subjectReason
  positiveExample := argument.comparison
  negativeExampleRule :=
    model.vyapti_gives_vyatireka argument.pervasion

theorem certified_public_argument_is_sound_and_wheel_valid {L : Type u}
    {model : BuddhistComparativeLogic.Dharmakirti.Model L}
    (argument : CertifiedPublicArgument model) :
    model.sadhya model.paksa ∧
      model.toAnumana.wheelVerdict = .valid :=
  ⟨PramanaSynthesis.dialectical_sound argument,
    PramanaSynthesis.dialectical_wheel_valid argument⟩

/-! ## Apoha as an explicit concept-selection layer -/

/-- A grounded concept uses one supplied equivalence-like relation and an
exemplar.  The exemplar class selects the positive extension; no causal
interpretation of the relation follows from this structure alone. -/
structure GroundedConcept (Object : Type u) where
  grounding : Apoha.Grounding Object
  exemplar : Object

namespace GroundedConcept

variable {Object : Type u} (concept : GroundedConcept Object)

def extension : Apoha.PredSet Object :=
  concept.grounding.cls concept.exemplar

def exclusion : Apoha.PredSet Object :=
  Apoha.compl concept.extension

theorem exemplar_mem : concept.extension concept.exemplar :=
  concept.grounding.mem_cls_self concept.exemplar

theorem extension_is_grounded :
    concept.grounding.grounded concept.extension :=
  ⟨concept.exemplar, rfl⟩

theorem extension_and_exclusion_are_apoha_pair :
    Apoha.apohaPair concept.extension concept.exclusion := by
  exact Apoha.apoha_pair_underdetermined concept.extension

/-- The combined result retains the independently supplied class grounding in
its conclusion.  The apoha-pair conjunct itself follows only from taking the
complement. -/
theorem grounded_extension_and_exclusion :
    concept.grounding.grounded concept.extension ∧
      Apoha.apohaPair concept.extension concept.exclusion :=
  ⟨concept.extension_is_grounded,
    concept.extension_and_exclusion_are_apoha_pair⟩

/-- This equivalence is classical double-negation at the selected extension.
It records the complement model's behavior, not a complete historical theory
of apoha. -/
theorem classified_iff_not_excluded (object : Object) :
    concept.extension object ↔ ¬ concept.exclusion object := by
  classical
  simp [exclusion, Apoha.compl]

end GroundedConcept

/-- In the comparison domain of an inference, the negative class is exactly
the exclusion of the positive class, together with exclusion of the subject.
This is the existing apoha/inference bridge, exposed here without changing
its scope. -/
theorem negative_comparison_is_exclusion {L : Type u}
    (inference : Anumana L) (object : L) :
    inference.vipaksa object ↔
      Apoha.compl inference.sapaksa object ∧ object ≠ inference.paksa :=
  Apoha.vipaksa_is_apoha_of_sapaksa inference object

/-- Complement structure alone does not choose whether a reason occupies the
positive or negative side of the wheel. -/
theorem apoha_form_does_not_determine_inferential_role :
    Apoha.wheelPositive.wheelVerdict = .valid ∧
      Apoha.wheelNegative.wheelVerdict = .contradictory :=
  Apoha.apoha_underdetermines_the_wheel

/-! ## Finite scope audits -/

inductive Sample where
  | included
  | excluded
  deriving DecidableEq, Repr

/-- Both finite objects present exactly the same raw datum. -/
def collapsedPerception : PerceptionModel Sample Unit where
  appearance := fun _ => ()
  nonconceptual := fun _ => True

def sampleConcept : Sample -> Prop := fun sample => sample = .included

/-- An exact conceptual classifier whose only input is the perceptual datum.
The definition deliberately contains no hidden object identity. -/
def ExactDatumClassifier {Object : Type u} {Datum : Type v}
    (model : PerceptionModel Object Datum) (concept : Object -> Prop) : Prop :=
  ∃ classify : Datum -> Bool, ∀ object,
    classify (model.appearance object) = true ↔ concept object

theorem collapsed_objects_are_observationally_equal :
    collapsedPerception.appearance .included =
      collapsedPerception.appearance .excluded :=
  rfl

/-- Raw observation cannot decide a concept that separates two objects with
the same datum. -/
theorem raw_observation_does_not_entail_conceptual_classification :
    ¬ ExactDatumClassifier collapsedPerception sampleConcept := by
  rintro ⟨classify, exactness⟩
  have includedResult : classify () = true :=
    (exactness .included).mpr rfl
  have excludedResult : sampleConcept .excluded :=
    (exactness .excluded).mp includedResult
  exact (by decide : (.excluded : Sample) ≠ .included) excludedResult

/-- The repository's finite `nofire` case already supplies all three marks
and a valid wheel cell while the subject thesis is false.  This is precisely
the missing-pervasion audit. -/
theorem three_marks_do_not_entail_subject_without_pervasion :
    ∃ inference : Anumana BuddhistComparativeLogic.Hetucakra.Locus,
      inference.trairupya ∧ inference.wheelVerdict = .valid ∧
        ¬ inference.sadhya inference.paksa :=
  PramanaSynthesis.marks_and_valid_wheel_do_not_entail_subject

/-- Put the finite `nofire` presentation behind the explicit pervasion
interface.  Here `vyapti` is the actual global implication, which is false. -/
def nofireModel : BuddhistComparativeLogic.Dharmakirti.Model BuddhistComparativeLogic.Hetucakra.Locus where
  toAnumana := BuddhistComparativeLogic.Hetucakra.nofire
  vyapti := ∀ object,
    BuddhistComparativeLogic.Hetucakra.nofire.reason object ->
      BuddhistComparativeLogic.Hetucakra.nofire.sadhya object
  vyapti_iff := Iff.rfl

theorem nofirePublicPresentation : PublicPresentation nofireModel where
  subjectReason := BuddhistComparativeLogic.Hetucakra.no_deductive_soundness.1.1
  positiveExample := BuddhistComparativeLogic.Hetucakra.no_deductive_soundness.1.2.1
  negativeExampleRule := BuddhistComparativeLogic.Hetucakra.no_deductive_soundness.1.2.2

theorem nofire_has_no_subject_warrant :
    ¬ SubjectWarrant nofireModel := by
  intro warrant
  exact BuddhistComparativeLogic.Hetucakra.no_deductive_soundness.2.2
    (subject_warrant_is_sound warrant)

theorem singleton_has_subject_warrant :
    SubjectWarrant PramanaSynthesis.singletonSound :=
  PramanaSynthesis.sound_subject_inference_need_not_have_valid_wheel.1

theorem singleton_has_no_public_presentation :
    ¬ PublicPresentation PramanaSynthesis.singletonSound := by
  intro presentation
  exact PramanaSynthesis.singleton_has_no_comparison
    presentation.positiveExample

/-- A mere marked public form and the project's subject warrant are not the
same proof object.  This is a statement about the two formal interfaces, not
an identification of them with Dignaga's historical private/public categories.
The first finite model has the public form without the subject warrant; the
singleton has the subject warrant without a distinct comparison example. -/
theorem public_form_and_subject_warrant_are_not_identical :
    (PublicPresentation nofireModel ∧
        ¬ SubjectWarrant nofireModel) ∧
      (SubjectWarrant PramanaSynthesis.singletonSound ∧
        ¬ PublicPresentation PramanaSynthesis.singletonSound) :=
  ⟨⟨nofirePublicPresentation, nofire_has_no_subject_warrant⟩,
    ⟨singleton_has_subject_warrant, singleton_has_no_public_presentation⟩⟩

end BuddhistComparativeLogic.Pramanasamuccaya
