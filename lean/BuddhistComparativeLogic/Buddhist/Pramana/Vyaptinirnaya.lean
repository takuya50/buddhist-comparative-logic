/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis

/-!
# A causal and scope-bounded audit of pervasion determination

This module gives a deliberately small reconstruction inspired by
Ratnakirti's *Vyaptinirnaya*.  It separates finite observed concomitance from
global reason-to-thesis pervasion.  A global conclusion is licensed here only
when a causal-production rule is joined to an explicit scope, proof that every
reason case is covered by that scope, and proof that the scope contains no
defeating condition.

The predicate called `upadhi` below is a generic defeating condition in this
model.  The name records the comparative problem being audited; it does not
identify Ratnakirti's analysis with the later Navya-Nyaya taxonomy, nor does
the module claim to translate every argument in the Sanskrit work.

Text and study:

* https://gretil.sub.uni-goettingen.de/gretil/corpustei/transformations/html/sa_ratnakIrti-nibandhAvalI.htm
* https://www.oeaw.ac.at/en/ikga/research/buddhist-studies/concluded/ratnakirtis-vyaptinirnaya
-/

namespace BuddhistComparativeLogic.Vyaptinirnaya

open BuddhistComparativeLogic.Hetucakra

universe u

/-! ## Observation and causal determination are different evidence -/

/-- Agreement on a registered finite list.  Membership in the list is the
only observational claim made by this predicate. -/
def RegisteredConcomitance {L : Type u} (argument : Anumana L)
    (registered : List L) : Prop :=
  forall object, object ∈ registered -> argument.reason object ->
    argument.sadhya object

/-- A causal schema exposes both the enabling condition under which the
reason produces or warrants the thesis and a possible defeating condition.
`causalProduction` is conditional and therefore is not global pervasion by
itself. -/
structure CausalSchema {L : Type u} (argument : Anumana L) where
  enabled : L -> Prop
  upadhi : L -> Prop
  causalProduction : forall object,
    argument.reason object -> enabled object -> ¬ upadhi object ->
      argument.sadhya object

/-- The additional certificate needed to lift the conditional causal rule to
the full inference domain.  `noncognition` records that no defeating condition
is cognized in the scope; `detectsScopedUpadhi` is the independent
perceptibility/completeness premise that makes this noncognition probative.
Without the latter premise, a finite failure to observe an `upadhi` proves no
absence. -/
structure ScopeCertificate {L : Type u} {argument : Anumana L}
    (schema : CausalSchema argument) where
  scope : L -> Prop
  cognizedUpadhi : L -> Prop
  coversReason : forall object, argument.reason object -> scope object
  scopeEnabled : forall object, scope object -> schema.enabled object
  noncognition : forall object, scope object -> ¬ cognizedUpadhi object
  detectsScopedUpadhi : forall object, scope object -> schema.upadhi object ->
    cognizedUpadhi object

namespace ScopeCertificate

variable {L : Type u} {argument : Anumana L}
  {schema : CausalSchema argument}

/-- Noncognition entails absence only through the certificate's explicit
detection-completeness premise. -/
theorem excludesUpadhi (certificate : ScopeCertificate schema)
    {object : L} (inScope : certificate.scope object) :
    ¬ schema.upadhi object := by
  intro upadhi
  exact certificate.noncognition object inScope
    (certificate.detectsScopedUpadhi object inScope upadhi)

/-- Causal production becomes the existing global pervasion only after all
three scope obligations have been supplied. -/
theorem toPervasion (certificate : ScopeCertificate schema) :
    BuddhistComparativeLogic.InferenceScope.Pervasion argument := by
  intro object reason
  have inScope := certificate.coversReason object reason
  exact schema.causalProduction object reason
    (certificate.scopeEnabled object inScope)
    (certificate.excludesUpadhi inScope)

end ScopeCertificate

/-- Package an ordinary `Anumana` as the existing Dharmakirti model, taking
global pervasion itself as the proposition named by `vyapti`. -/
def pervasionModel {L : Type u} (argument : Anumana L) :
    BuddhistComparativeLogic.Dharmakirti.Model L where
  toAnumana := argument
  vyapti := BuddhistComparativeLogic.InferenceScope.Pervasion argument
  vyapti_iff := Iff.rfl

/-- A determined pervasion plus possession of the reason at the subject gives
the common proof certificate used by the pramana synthesis. -/
theorem ScopeCertificate.toDeductiveCertificate
    {L : Type u} {argument : Anumana L}
    {schema : CausalSchema argument}
    (certificate : ScopeCertificate schema)
    (subjectReason : argument.paksadharmata) :
    BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (pervasionModel argument) where
  subjectReason := subjectReason
  pervasion := certificate.toPervasion

/-! ## A finite, nonvacuous positive model -/

inductive Site where
  | hearth
  | kitchen
  | lake
  deriving DecidableEq, Repr

open Site

/-- Smoke is registered at two fire sites.  The lake remains in the domain
and bears neither reason nor thesis. -/
def smokeFire : Anumana Site where
  paksa := .hearth
  reason := fun site => site = .hearth ∨ site = .kitchen
  sadhya := fun site => site ≠ .lake

def inspected : List Site := [.hearth, .kitchen]

def dryAndOpen : Site -> Prop
  | .hearth | .kitchen => True
  | .lake => False

/-- The lake witnesses that the possible-defeater predicate is not globally
empty; the certified inference scope excludes it because it has no smoke. -/
def obstruction : Site -> Prop
  | .hearth | .kitchen => False
  | .lake => True

def smokeCausalSchema : CausalSchema smokeFire where
  enabled := dryAndOpen
  upadhi := obstruction
  causalProduction := by
    intro site _smoke enabled _unobstructed
    cases site <;> simp [dryAndOpen, smokeFire] at enabled ⊢

theorem smoke_registered_concomitance :
    RegisteredConcomitance smokeFire inspected := by
  intro site _registered smoke
  rcases smoke with rfl | rfl <;> simp [smokeFire]

def smokeScopeCertificate : ScopeCertificate smokeCausalSchema where
  scope := fun site => site = .hearth ∨ site = .kitchen
  cognizedUpadhi := obstruction
  coversReason := by
    intro site smoke
    exact smoke
  scopeEnabled := by
    intro site inScope
    rcases inScope with rfl | rfl <;> trivial
  noncognition := by
    intro site inScope
    rcases inScope with rfl | rfl <;> simp [obstruction]
  detectsScopedUpadhi := by
    intro site _inScope upadhi
    exact upadhi

theorem causal_scope_yields_global_pervasion :
    BuddhistComparativeLogic.InferenceScope.Pervasion smokeFire :=
  smokeScopeCertificate.toPervasion

theorem smokeDeductiveCertificate :
    BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (pervasionModel smokeFire) :=
  smokeScopeCertificate.toDeductiveCertificate (Or.inl rfl)

theorem causal_scope_yields_subject_thesis :
    smokeFire.sadhya smokeFire.paksa :=
  BuddhistComparativeLogic.PramanaSynthesis.deductive_sound smokeDeductiveCertificate

/-- The result has two registered positive cases, a genuine negative case,
and a possible defeating condition outside the reason-covered scope. -/
theorem causal_model_nonvacuous :
    smokeFire.reason .hearth /\
      smokeFire.reason .kitchen /\
      ¬ smokeFire.reason .lake /\
      smokeFire.sadhya .hearth /\
      smokeFire.sadhya .kitchen /\
      ¬ smokeFire.sadhya .lake /\
      obstruction .lake /\
      BuddhistComparativeLogic.InferenceScope.Pervasion smokeFire := by
  exact ⟨Or.inl rfl, Or.inr rfl, by simp [smokeFire], by simp [smokeFire],
    by simp [smokeFire], by simp [smokeFire], trivial,
    causal_scope_yields_global_pervasion⟩

/-! ## Finite observation does not supply the global quantifier -/

inductive SurveySite where
  | first
  | second
  | hidden
  deriving DecidableEq, Repr

open SurveySite

def survey : Anumana SurveySite where
  paksa := .first
  reason := fun _ => True
  sadhya
    | .first | .second => True
    | .hidden => False

def surveyRegistry : List SurveySite := [.first, .second]

def surveyUpadhi : SurveySite -> Prop
  | .first | .second => False
  | .hidden => True

def surveyEnabled : SurveySite -> Prop := fun _ => True

def surveyCausalSchema : CausalSchema survey where
  enabled := surveyEnabled
  upadhi := surveyUpadhi
  causalProduction := by
    intro site _reason _enabled unobstructed
    cases site <;> simp [surveyUpadhi, survey] at unobstructed ⊢

theorem survey_registered_concomitance :
    RegisteredConcomitance survey surveyRegistry := by
  intro site registered _reason
  cases site <;> simp [surveyRegistry, survey] at registered ⊢

def NoRegisteredUpadhi {L : Type u} {argument : Anumana L}
    (schema : CausalSchema argument)
    (registered : List L) : Prop :=
  forall object, object ∈ registered -> ¬ schema.upadhi object

def NoReasonUpadhi {L : Type u} {argument : Anumana L}
    (schema : CausalSchema argument) : Prop :=
  forall object, argument.reason object -> ¬ schema.upadhi object

theorem survey_has_no_registered_upadhi :
    NoRegisteredUpadhi surveyCausalSchema surveyRegistry := by
  intro site registered
  cases site <;>
    simp [surveyRegistry, surveyCausalSchema, surveyUpadhi] at registered ⊢

theorem survey_not_globally_pervaded :
    ¬ BuddhistComparativeLogic.InferenceScope.Pervasion survey := by
  intro pervasion
  exact pervasion .hidden trivial

theorem survey_not_globally_upadhi_free :
    ¬ NoReasonUpadhi surveyCausalSchema := by
  intro globallyFree
  exact globallyFree .hidden trivial trivial

/-- A three-element model records two positive observations and no observed
defeater, while the unregistered third case defeats both global pervasion and
global freedom from a defeating condition. -/
theorem finite_observations_and_upadhi_search_are_insufficient :
    RegisteredConcomitance survey surveyRegistry /\
      NoRegisteredUpadhi surveyCausalSchema surveyRegistry /\
      survey.reason .first /\ survey.sadhya .first /\
      survey.reason .second /\ survey.sadhya .second /\
      survey.reason .hidden /\ ¬ survey.sadhya .hidden /\
      surveyCausalSchema.upadhi .hidden /\
      ¬ NoReasonUpadhi surveyCausalSchema /\
      ¬ BuddhistComparativeLogic.InferenceScope.Pervasion survey := by
  exact ⟨survey_registered_concomitance, survey_has_no_registered_upadhi,
    trivial, trivial, trivial, trivial, trivial, by simp [survey], trivial,
    survey_not_globally_upadhi_free, survey_not_globally_pervaded⟩

/-! ## Any finite registry admits an unseen extension -/

def liftRegistry {L : Type u} (registered : List L) : Option L -> Prop
  | .some object => object ∈ registered
  | .none => False

/-- Add one unregistered reason-bearing countercase to any finite registry.
All lifted registered objects satisfy the thesis, while the new `none` case
does not. -/
def registryExtension {L : Type u} (subject : L) : Anumana (Option L) where
  paksa := some subject
  reason := fun _ => True
  sadhya
    | .some _ => True
    | .none => False

theorem every_finite_registry_admits_an_unseen_countercase
    {L : Type u} (registered : List L) (subject : L) :
    (forall object, liftRegistry registered object ->
      (registryExtension subject).reason object ->
        (registryExtension subject).sadhya object) /\
      ¬ BuddhistComparativeLogic.InferenceScope.Pervasion (registryExtension subject) := by
  constructor
  · intro object observed _reason
    cases object with
    | none => exact False.elim observed
    | some _ => trivial
  · intro pervasion
    exact pervasion none trivial

end BuddhistComparativeLogic.Vyaptinirnaya
