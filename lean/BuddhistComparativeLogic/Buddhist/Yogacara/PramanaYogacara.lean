/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Yogacara.VimsatikaModels
import BuddhistComparativeLogic.Buddhist.Pramana.Dharmakirti

/-!
# Inferential scope for Yogacara observation models

The Viṃśatikā models record appearances and efficacy, while Dharmakīrti's
inference interface makes pervasion an explicit premise.  This module joins
those interfaces without treating observational adequacy as an ontological
conclusion.

An `Inquiry` assigns an observable Viṃśatikā model and a target claim to each
hypothesis.  Observational adequacy licenses the target only when an explicit
`ObservationalLicense` supplies the corresponding pervasion.  A `Defeater`
exhibits observationally equivalent adequate hypotheses on opposite sides of
the target; it refutes both that pervasion and any exact classifier computed
only from the observations.

The finite examples distinguish two questions.  Each alternative maps to
semantic data: either an appearance account alone, or an external object
carrier together with an account on that carrier.  External existence and
one-object cardinality are then defined from the resulting carrier, rather
than by inspecting the alternative's name.  First, the appearance-only
naraka account and a one-object external realization agree observationally,
so the four adequacy conditions do not establish external objects.  Second,
the one-object and two-object realizations agree observationally, so even a
prior restriction to external accounts does not determine object-domain
cardinality.  The restricted-inference result states exactly what an added
admissibility premise contributes; it is not a proof of that premise.
-/

namespace BuddhistComparativeLogic.PramanaYogacara

open BuddhistComparativeLogic.Vimsatika
open BuddhistComparativeLogic.VimsatikaModels

/-- A family of hypotheses, each with observable content and a target claim. -/
structure Inquiry (Hypothesis : Type u) (Subject : Type v)
    (Place : Type w) (Time : Type z) where
  observation : Hypothesis → Vijnapti Subject Place Time
  target : Hypothesis → Prop

namespace Inquiry

variable {Hypothesis : Type u} {Subject : Type v}
  {Place : Type w} {Time : Type z}

/-- The pervasion needed to infer the target from observational adequacy. -/
def ObservationalLicense
    (I : Inquiry Hypothesis Subject Place Time) : Prop :=
  ∀ hypothesis, (I.observation hypothesis).adequate → I.target hypothesis

/-- Restrict the pervasion to an explicitly supplied class of hypotheses. -/
def RestrictedLicense
    (I : Inquiry Hypothesis Subject Place Time)
    (admissible : Hypothesis → Prop) : Prop :=
  ∀ hypothesis, admissible hypothesis →
    (I.observation hypothesis).adequate → I.target hypothesis

/-- The associated Dharmakīrti model.  Adequacy is the reason, the inquiry's
target is the thesis, and `ObservationalLicense` is exactly pervasion. -/
def inference (I : Inquiry Hypothesis Subject Place Time)
    (subject : Hypothesis) : Dharmakirti.Model Hypothesis where
  paksa := subject
  reason := fun hypothesis => (I.observation hypothesis).adequate
  sadhya := I.target
  vyapti := I.ObservationalLicense
  vyapti_iff := Iff.rfl

theorem inference_vyapti_iff
    (I : Inquiry Hypothesis Subject Place Time) (subject : Hypothesis) :
    (I.inference subject).vyapti ↔ I.ObservationalLicense :=
  Iff.rfl

/-- Observational adequacy yields the target only after the pervasion premise
is supplied. -/
theorem conclusion_of_license
    (I : Inquiry Hypothesis Subject Place Time) (subject : Hypothesis)
    (license : I.ObservationalLicense)
    (adequate : (I.observation subject).adequate) :
    I.target subject :=
  (I.inference subject).vyapti_sound license adequate

/-- Restricting the hypothesis class produces the corresponding restricted
Dharmakīrti inference. -/
def restrictedInference
    (I : Inquiry Hypothesis Subject Place Time)
    (admissible : Hypothesis → Prop)
    (subject : { hypothesis // admissible hypothesis }) :
    Dharmakirti.Model { hypothesis // admissible hypothesis } where
  paksa := subject
  reason := fun hypothesis =>
    (I.observation hypothesis.1).adequate
  sadhya := fun hypothesis => I.target hypothesis.1
  vyapti := I.RestrictedLicense admissible
  vyapti_iff := by
    constructor
    · intro license hypothesis adequate
      exact license hypothesis.1 hypothesis.2 adequate
    · intro license hypothesis admitted adequate
      exact license ⟨hypothesis, admitted⟩ adequate

theorem restricted_conclusion
    (I : Inquiry Hypothesis Subject Place Time)
    (admissible : Hypothesis → Prop)
    (subject : { hypothesis // admissible hypothesis })
    (license : I.RestrictedLicense admissible)
    (adequate : (I.observation subject.1).adequate) :
    I.target subject.1 :=
  (I.restrictedInference admissible subject).vyapti_sound license adequate

end Inquiry

/-! ## Observational defeaters -/

/-- A positive and a negative hypothesis with the same observations.  The
positive adequacy proof transfers to the negative hypothesis. -/
structure Defeater
    {Hypothesis : Type u} {Subject : Type v}
    {P : Type w} {T : Type z}
    (I : Inquiry Hypothesis Subject P T) where
  positive : Hypothesis
  negative : Hypothesis
  equivalent : I.observation positive = I.observation negative
  positiveAdequate : (I.observation positive).adequate
  positiveTarget : I.target positive
  negativeTarget : ¬ I.target negative

namespace Defeater

variable {Hypothesis : Type u} {Subject : Type v}
  {Place : Type w} {Time : Type z}
  {I : Inquiry Hypothesis Subject Place Time}

theorem negative_adequate (defeater : Defeater I) :
    (I.observation defeater.negative).adequate :=
  defeater.equivalent ▸ defeater.positiveAdequate

/-- An observationally equivalent negative case refutes unrestricted
pervasion. -/
theorem blocks_license (defeater : Defeater I) :
    ¬ I.ObservationalLicense := by
  intro license
  exact defeater.negativeTarget
    (license defeater.negative defeater.negative_adequate)

/-- A restriction still fails if it admits the defeating hypothesis. -/
theorem blocks_restricted_license (defeater : Defeater I)
    {admissible : Hypothesis → Prop}
    (negativeAllowed : admissible defeater.negative) :
    ¬ I.RestrictedLicense admissible := by
  intro license
  exact defeater.negativeTarget
    (license defeater.negative negativeAllowed defeater.negative_adequate)

/-- Consequently, any successful restriction must exclude this particular
negative hypothesis. -/
theorem licensed_scope_excludes_negative (defeater : Defeater I)
    {admissible : Hypothesis → Prop}
    (license : I.RestrictedLicense admissible) :
    ¬ admissible defeater.negative := by
  intro negativeAllowed
  exact defeater.blocks_restricted_license negativeAllowed license

end Defeater

/-- An exact observation-only decision rule for the inquiry's target. -/
def ExactObservationClassifier
    {Hypothesis : Type u} {Subject : Type v}
    {P : Type w} {T : Type z}
    (I : Inquiry Hypothesis Subject P T) : Prop :=
  ∃ classify : Vijnapti Subject P T → Bool,
    ∀ hypothesis,
      classify (I.observation hypothesis) = true ↔ I.target hypothesis

/-- A defeater rules out every exact classifier whose input is only the two
observable predicates. -/
theorem no_exact_classifier_of_defeater
    {Hypothesis : Type u} {Subject : Type v}
    {P : Type w} {T : Type z}
    {I : Inquiry Hypothesis Subject P T}
    (defeater : Defeater I) :
    ¬ ExactObservationClassifier I := by
  rintro ⟨classify, exactness⟩
  have positiveResult :
      classify (I.observation defeater.positive) = true :=
    (exactness defeater.positive).mpr defeater.positiveTarget
  have observationEq :
      I.observation defeater.positive = I.observation defeater.negative :=
    defeater.equivalent
  have negativeResult :
      classify (I.observation defeater.negative) = true := by
    rw [← observationEq]
    exact positiveResult
  exact defeater.negativeTarget
    ((exactness defeater.negative).mp negativeResult)

/-! ## Finite rival accounts -/

/-- Semantic content of an account: an appearance model alone, or an actual
external-object carrier together with the model that uses it. -/
inductive AccountSemantics where
  | appearance
      (model : Vijnapti Vimsatika.Person Vimsatika.Place Vimsatika.Moment)
  | external
      (Object : Type)
      (model : ObjectIndexedAccount Vimsatika.Person Vimsatika.Place
        Vimsatika.Moment Object)

namespace AccountSemantics

/-- The observations supplied by either kind of account. -/
def observation : AccountSemantics →
    Vijnapti Vimsatika.Person Vimsatika.Place Vimsatika.Moment
  | .appearance model => model
  | .external _ model => model.observations

/-- The external-object carrier.  An appearance-only account has the empty
carrier; an external account exposes the carrier used by its model. -/
def objectCarrier : AccountSemantics → Type
  | .appearance _ => Empty
  | .external Object _ => Object

/-- Semantic external existence: the account's object carrier is inhabited. -/
def HasExternalObject (account : AccountSemantics) : Prop :=
  Nonempty account.objectCarrier

/-- Semantic one-object cardinality: every object in the carrier is equal to
one exhibited object. -/
def HasExactlyOneExternalObject (account : AccountSemantics) : Prop :=
  ∃ object : account.objectCarrier,
    ∀ other : account.objectCarrier, other = object

end AccountSemantics

/-- Names for the three semantic accounts used in the finite comparison. -/
inductive Account where
  | appearanceOnly
  | oneExternalObject
  | twoExternalObjects
  deriving DecidableEq, Repr

/-- Interpret each finite alternative as concrete semantic data.  The
one-object and two-object alternatives use `Unit` and `Bool` as their actual
object carriers. -/
def accountSemantics : Account → AccountSemantics
  | .appearanceOnly => .appearance Vimsatika.naraka
  | .oneExternalObject =>
      .external Unit VimsatikaModels.narakaUnitIndexed
  | .twoExternalObjects =>
      .external Bool VimsatikaModels.narakaBoolIndexed

def accountObservation :
    Account → Vijnapti Vimsatika.Person Vimsatika.Place Vimsatika.Moment
  | account => (accountSemantics account).observation

def positsExternalObjects (account : Account) : Prop :=
  (accountSemantics account).HasExternalObject

def positsExactlyOneExternalObject (account : Account) : Prop :=
  (accountSemantics account).HasExactlyOneExternalObject

theorem appearance_only_has_no_external_object :
    ¬ positsExternalObjects .appearanceOnly := by
  intro inhabited
  exact nomatch inhabited

theorem one_account_has_external_object :
    positsExternalObjects .oneExternalObject :=
  ⟨()⟩

theorem two_account_has_external_object :
    positsExternalObjects .twoExternalObjects :=
  ⟨false⟩

theorem one_account_has_exactly_one_external_object :
    positsExactlyOneExternalObject .oneExternalObject := by
  change ∃ object : Unit, ∀ other : Unit, other = object
  exact ⟨(), fun other => Subsingleton.elim other ()⟩

theorem two_account_does_not_have_exactly_one_external_object :
    ¬ positsExactlyOneExternalObject .twoExternalObjects := by
  rintro ⟨object, unique⟩
  exact Bool.false_ne_true ((unique false).trans (unique true).symm)

theorem every_account_is_adequate (account : Account) :
    (accountObservation account).adequate := by
  cases account with
  | appearanceOnly => exact Vimsatika.naraka_meets_all_four
  | oneExternalObject =>
      exact (adequacy_is_observation_invariant
        VimsatikaModels.naraka_unit_indexed_equivalent).mp
        Vimsatika.naraka_meets_all_four
  | twoExternalObjects =>
      exact (adequacy_is_observation_invariant
        VimsatikaModels.naraka_bool_indexed_equivalent).mp
        Vimsatika.naraka_meets_all_four

theorem one_and_appearance_are_equivalent :
    observationEquivalent
      (accountObservation .oneExternalObject)
      (accountObservation .appearanceOnly) :=
  observationEquivalent_symm VimsatikaModels.naraka_unit_indexed_equivalent

theorem one_and_two_are_equivalent :
    observationEquivalent
      (accountObservation .oneExternalObject)
      (accountObservation .twoExternalObjects) :=
  observationEquivalent_trans
    (observationEquivalent_symm
      VimsatikaModels.naraka_unit_indexed_equivalent)
    VimsatikaModels.naraka_bool_indexed_equivalent

def externalObjectInquiry :
    Inquiry Account Vimsatika.Person Vimsatika.Place Vimsatika.Moment where
  observation := accountObservation
  target := positsExternalObjects

def oneObjectInquiry :
    Inquiry Account Vimsatika.Person Vimsatika.Place Vimsatika.Moment where
  observation := accountObservation
  target := positsExactlyOneExternalObject

/-- Observationally adequate appearance-only and external accounts disagree
about whether any external object is posited. -/
def externalObjectDefeater : Defeater externalObjectInquiry where
  positive := .oneExternalObject
  negative := .appearanceOnly
  equivalent := eq_of_observationEquivalent one_and_appearance_are_equivalent
  positiveAdequate := every_account_is_adequate .oneExternalObject
  positiveTarget := one_account_has_external_object
  negativeTarget := appearance_only_has_no_external_object

/-- Two observationally adequate external accounts disagree about whether the
external domain has exactly one object. -/
def oneObjectDefeater : Defeater oneObjectInquiry where
  positive := .oneExternalObject
  negative := .twoExternalObjects
  equivalent := eq_of_observationEquivalent one_and_two_are_equivalent
  positiveAdequate := every_account_is_adequate .oneExternalObject
  positiveTarget := one_account_has_exactly_one_external_object
  negativeTarget := two_account_does_not_have_exactly_one_external_object

theorem external_objects_not_observationally_licensed :
    ¬ externalObjectInquiry.ObservationalLicense :=
  externalObjectDefeater.blocks_license

theorem external_object_count_not_observationally_licensed :
    ¬ oneObjectInquiry.ObservationalLicense :=
  oneObjectDefeater.blocks_license

theorem no_exact_observation_classifier_for_external_objects :
    ¬ ExactObservationClassifier externalObjectInquiry :=
  no_exact_classifier_of_defeater externalObjectDefeater

theorem no_exact_observation_classifier_for_one_object :
    ¬ ExactObservationClassifier oneObjectInquiry :=
  no_exact_classifier_of_defeater oneObjectDefeater

/-! ## The three marks do not repair the missing pervasion -/

def externalInference : Dharmakirti.Model Account :=
  externalObjectInquiry.inference .appearanceOnly

theorem external_inference_has_three_marks :
    externalInference.toAnumana.trairupya := by
  refine ⟨every_account_is_adequate .appearanceOnly, ?_, ?_⟩
  · refine ⟨.oneExternalObject, ?_,
      every_account_is_adequate .oneExternalObject⟩
    exact ⟨by decide, one_account_has_external_object⟩
  · intro account hypothesis _
    rcases hypothesis with ⟨different, negative⟩
    cases account with
    | appearanceOnly => exact different rfl
    | oneExternalObject => exact negative one_account_has_external_object
    | twoExternalObjects => exact negative two_account_has_external_object

/-- In this finite model the reason occurs at the subject, all three marks
hold, and the wheel is valid, while both pervasion and the subject thesis are
false.  This isolates the quantifier-scope boundary between the wheel and the
explicit Dharmakīrti premise. -/
theorem three_marks_do_not_establish_external_objects :
    externalInference.toAnumana.paksadharmata ∧
      externalInference.toAnumana.trairupya ∧
      externalInference.toAnumana.wheelVerdict = .valid ∧
      ¬ externalInference.vyapti ∧
      ¬ externalInference.sadhya .appearanceOnly := by
  have marks := external_inference_has_three_marks
  exact ⟨marks.1, marks,
    externalInference.toAnumana.wheel_valid_iff.mpr marks.2,
    external_objects_not_observationally_licensed,
    appearance_only_has_no_external_object⟩

/-! ## What an explicit scope premise contributes -/

def externallyAdmissible : Account → Prop := positsExternalObjects

/-- Once the candidate class is explicitly restricted to accounts already
known to posit external objects, the restricted pervasion holds.  The proof
uses the admissibility hypothesis itself, exposing rather than deriving the
ontological commitment. -/
theorem external_scope_is_licensed :
    externalObjectInquiry.RestrictedLicense externallyAdmissible := by
  intro account admitted _
  exact admitted

def oneExternalCandidate : { account // externallyAdmissible account } :=
  ⟨.oneExternalObject, one_account_has_external_object⟩

theorem restricted_inference_recovers_its_scope_commitment :
    externalObjectInquiry.target oneExternalCandidate.1 :=
  externalObjectInquiry.restricted_conclusion externallyAdmissible
    oneExternalCandidate external_scope_is_licensed
    (every_account_is_adequate .oneExternalObject)

/-- Restricting attention merely to external accounts still leaves the
one-versus-two cardinality question defeated. -/
theorem external_scope_does_not_fix_cardinality :
    ¬ oneObjectInquiry.RestrictedLicense externallyAdmissible :=
  oneObjectDefeater.blocks_restricted_license two_account_has_external_object

end BuddhistComparativeLogic.PramanaYogacara
