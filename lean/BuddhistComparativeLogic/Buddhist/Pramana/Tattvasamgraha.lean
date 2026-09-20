/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis
import BuddhistComparativeLogic.Buddhist.Madhyamaka.FourfoldCausation
import BuddhistComparativeLogic.Buddhist.Pramana.DirectedMomentariness
import BuddhistComparativeLogic.Buddhist.Pramana.ApohaSelection
import BuddhistComparativeLogic.Buddhist.Yogacara.VimsatikaModels

/-!
# Scoped debate certificates motivated by the Tattvasaṃgraha

Śāntarakṣita's *Tattvasaṃgraha* is a large, internally varied collection of
arguments against rival positions.  This module does not claim to translate
every verse or to turn the whole work into one axiomatic theory.  It instead
registers a selected group of arguments that can be connected carefully to
the existing developments: inference, dependence, fourfold causation,
momentariness, theories of the three times, apoha, and the observational
underdetermination exposed by the *Viṃśatikā* models.

Every rule exposes five items: an opponent thesis, a reason, a scope, a
reason-to-result bridge, and the incompatibility of that result with the
opponent thesis.  A certificate adds evidence that one subject lies in scope
and possesses the reason.  Topic lists are unchecked descriptive annotations:
no proof below derives their historical provenance, chapter numbering, or a
claim that these arguments all occur in one voice.  The generic coverage
countermodel at the end does not assert coverage by the exported adapters.

The finite models at the end block three overstatements.  Merely covering all
registered topics does not make their verdicts jointly consistent; refuting
one rival thesis does not establish every Buddhist alternative; and a premise
licensed in one examination does not thereby hold in every examination.
-/

namespace BuddhistComparativeLogic.Tattvasamgraha

universe u v w

/-! ## Rules and certificates -/

/-- Selected argumentative topics, deliberately not a complete chapter list. -/
inductive Topic where
  | inferenceMethod
  | dependentOwnBeing
  | madhyamakaEmptiness
  | causalOrigin
  | momentariness
  | threeTimesActivity
  | wordMeaning
  | appearanceAndObjects
  deriving DecidableEq, Repr

/-- An open debate rule.  The scope predicate prevents a chapter-local bridge
from being read as a universal metaphysical law.  `topics` is non-proof-bearing
metadata and is not consumed by `pervasion` or `refutes`. -/
structure DebateRule (D : Type u) where
  topics : List Topic
  scope : D -> Prop
  opponentThesis : D -> Prop
  reason : D -> Prop
  result : D -> Prop
  pervasion : forall x, scope x -> reason x -> result x
  refutes : forall x, scope x -> result x -> ¬ opponentThesis x

/-- A closed use of a debate rule at one specified subject. -/
structure DebateCertificate (D : Type u) (subject : D)
    extends DebateRule D where
  subjectInScope : scope subject
  subjectReason : reason subject

namespace DebateCertificate

variable {D : Type u} {subject : D}

/-- A certificate yields its registered result at the selected subject. -/
theorem result_at_subject (certificate : DebateCertificate D subject) :
    certificate.result subject :=
  certificate.pervasion subject certificate.subjectInScope
    certificate.subjectReason

/-- The registered result rejects the registered opponent thesis at the
selected subject. -/
theorem rejects_opponent (certificate : DebateCertificate D subject) :
    ¬ certificate.opponentThesis subject :=
  certificate.refutes subject certificate.subjectInScope
    certificate.result_at_subject

/-- Soundness exposes both the positive result and the negative dialectical
consequence. -/
theorem sound (certificate : DebateCertificate D subject) :
    certificate.result subject ∧
      ¬ certificate.opponentThesis subject :=
  And.intro certificate.result_at_subject certificate.rejects_opponent

end DebateCertificate

namespace DebateRule

variable {D : Type u}

/-- Sequential composition records both topic trails.  The explicit
connector is the only route from the first result to the second reason. -/
def compose (first second : DebateRule D)
    (connector : forall x, first.scope x -> second.scope x ->
      first.result x -> second.reason x) : DebateRule D where
  topics := first.topics ++ second.topics
  scope := fun x => first.scope x ∧ second.scope x
  opponentThesis := second.opponentThesis
  reason := first.reason
  result := second.result
  pervasion := by
    intro x hx hreason
    have firstResult : first.result x :=
      first.pervasion x hx.1 hreason
    exact second.pervasion x hx.2
      (connector x hx.1 hx.2 firstResult)
  refutes := by
    intro x hx hresult
    exact second.refutes x hx.2 hresult

/-- Composition cannot manufacture a conclusion without the first reason and
both scope checks. -/
theorem compose_sound (first second : DebateRule D)
    (connector : forall x, first.scope x -> second.scope x ->
      first.result x -> second.reason x)
    {x : D} (inScope : first.scope x ∧ second.scope x)
    (hasReason : first.reason x) :
    (first.compose second connector).result x :=
  (first.compose second connector).pervasion x inScope hasReason

end DebateRule

/-! ## Inference and dependence -/

/-- A Dharmakīrti-style deductive certificate becomes a debate certificate.
The positive comparison example needed for a public three-mark presentation
is intentionally not added here. -/
def ofInference {L : Type u} (model : BuddhistComparativeLogic.Dharmakirti.Model L)
    (certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate model) :
    DebateCertificate L model.paksa where
  topics := [.inferenceMethod]
  scope := fun _ => True
  opponentThesis := fun x => ¬ model.sadhya x
  reason := model.reason
  result := model.sadhya
  pervasion := by
    intro x _ hreason
    exact (model.vyapti_iff.mp certificate.pervasion) x hreason
  refutes := by
    intro x _ hresult hopponent
    exact hopponent hresult
  subjectInScope := trivial
  subjectReason := certificate.subjectReason

theorem inference_certificate_is_sound {L : Type u}
    (model : BuddhistComparativeLogic.Dharmakirti.Model L)
    (certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate model) :
    model.sadhya model.paksa ∧
      ¬ ¬ model.sadhya model.paksa :=
  (ofInference model certificate).sound

/-- The Madhyamaka adapter registers the existing universal-emptiness
inference under both its Madhyamaka and inference topics.  It inherits the
substantive premises already stored in `Madhyamaka`; it does not establish
those premises from the registry interface alone. -/
def ofMadhyamaka {V : Type u} (model : BuddhistComparativeLogic.Madhyamaka V)
    (subject : BuddhistComparativeLogic.Dharma) :
    DebateCertificate BuddhistComparativeLogic.Dharma subject :=
  { ofInference
      (BuddhistComparativeLogic.EmptinessInference.ofMadhyamaka model subject)
      (BuddhistComparativeLogic.PramanaSynthesis.ofMadhyamaka model subject) with
    topics := [.madhyamakaEmptiness, .inferenceMethod] }

theorem madhyamaka_registry_result {V : Type u}
    (model : BuddhistComparativeLogic.Madhyamaka V) (subject : BuddhistComparativeLogic.Dharma) :
    model.toEmptiness.emptyOf subject ∧
      ¬ ¬ model.toEmptiness.emptyOf subject :=
  (ofMadhyamaka model subject).sound

/-- Dependence in one admitted mode is the reason; invariance of own-being in
that mode supplies the bridge to absence of own-being. -/
def dependenceRule {D : Type u} (model : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode) : DebateRule D where
  topics := [.dependentOwnBeing]
  scope := fun _ => True
  opponentThesis := model.own
  reason := fun x => exists source, model.DependsAt mode source x
  result := fun x => ¬ model.own x
  pervasion := by
    intro x _ hreason
    obtain ⟨source, edge⟩ := hreason
    exact model.dependence_excludes_own_at mode invariant x source edge
  refutes := by
    intro x _ hresult hopponent
    exact hresult hopponent

/-- This second rule records the inferential presentation of absence of
own-being.  Its bridge is definitional; it contributes no new metaphysical
premise. -/
def emptinessRegistrationRule {D : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode) : DebateRule D where
  topics := [.inferenceMethod]
  scope := fun _ => True
  opponentThesis := model.own
  reason := fun x => ¬ model.own x
  result := (model.toDependenceAt mode).emptyOf
  pervasion := by
    intro x _ hreason
    exact hreason
  refutes := by
    intro x _ hresult hopponent
    exact hresult hopponent

/-- The chapter-spanning rule keeps the dependence bridge and its inferential
registration as two visible steps. -/
def dependenceInferenceRule {D : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode) : DebateRule D :=
  (dependenceRule model mode invariant).compose
    (emptinessRegistrationRule model mode)
    (fun _ _ _ hresult => hresult)

def dependenceInferenceCertificate {D : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode) {subject source : D}
    (edge : model.DependsAt mode source subject) :
    DebateCertificate D subject where
  toDebateRule := dependenceInferenceRule model mode invariant
  subjectInScope := And.intro trivial trivial
  subjectReason := Exists.intro source edge

theorem dependence_inference_refutes_own {D : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode) {subject source : D}
    (edge : model.DependsAt mode source subject) :
    (model.toDependenceAt mode).emptyOf subject ∧
      ¬ model.own subject :=
  (dependenceInferenceCertificate model mode invariant edge).sound

/-- The composed registry conclusion agrees extensionally with the existing
Dharmakīrti-style dependence inference. -/
theorem dependence_composition_agrees_with_pramana {D : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode) (x : D) :
    (dependenceInferenceRule model mode invariant).result x <->
      (BuddhistComparativeLogic.SupportingArguments.modeInference model mode x).sadhya x :=
  Iff.rfl

/-- The same local edge simultaneously closes the scoped registry argument
and the existing subject-level pramāṇa certificate. -/
theorem dependence_has_pramana_certificate {D : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode) {subject source : D}
    (edge : model.DependsAt mode source subject) :
    BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
        (BuddhistComparativeLogic.SupportingArguments.modeInference model mode subject) ∧
      (dependenceInferenceRule model mode invariant).result subject := by
  exact And.intro
    (BuddhistComparativeLogic.PramanaSynthesis.ofModeDependence
      model mode invariant edge)
    (dependenceInferenceCertificate model mode invariant edge).result_at_subject

/-! ## Causation, momentariness, and the three times -/

/-- The exact fourfold origin analysis rejects intrinsic production under
the five explicit laws in `FourfoldCausation.Model.Laws`.  Its scope is the
admitted occurrences, even though the reusable theorem is stronger. -/
def ofFourfoldCausation {E : Type u} {K : Type v} {T : Type w}
    (model : BuddhistComparativeLogic.FourfoldCausation.Model E K T)
    (laws : model.Laws) {event : E} (occurs : model.occurs event) :
    DebateCertificate E event where
  topics := [.causalOrigin]
  scope := model.occurs
  opponentThesis := model.intrinsic
  reason := fun _ => model.Laws
  result := fun x => ¬ model.intrinsic x
  pervasion := by
    intro x _ suppliedLaws
    exact model.no_intrinsic_by_four_cases suppliedLaws x
  refutes := by
    intro x _ hresult hopponent
    exact hresult hopponent
  subjectInScope := occurs
  subjectReason := laws

theorem fourfold_causation_refutes_intrinsic {E : Type u} {K : Type v}
    {T : Type w} (model : BuddhistComparativeLogic.FourfoldCausation.Model E K T)
    (laws : model.Laws) {event : E} (occurs : model.occurs event) :
    ¬ model.intrinsic event :=
  (ofFourfoldCausation model laws occurs).rejects_opponent

/-- Rejection of intrinsic production preserves the concrete ordinary causal
history; the argument is not a denial that conditional production occurs. -/
theorem fourfold_refutation_preserves_ordinary_production :
    ¬ BuddhistComparativeLogic.FourfoldCausation.chain.intrinsic true ∧
      BuddhistComparativeLogic.FourfoldCausation.chain.OrdinaryConditional true :=
  BuddhistComparativeLogic.FourfoldCausation.nonarising_preserves_ordinary_production

/-- Existence and causal efficacy at one time refute time-invariant intrinsic
power.  This is the first step of the momentariness argument, not yet the
claim that the object exists at exactly one time. -/
def ofCausalNonuniformity {D : Type u} {E : Type v} {T : Type w}
    (model : BuddhistComparativeLogic.Momentariness.Theory D E T) (time : T)
    {object : D} (existsNow : model.existsAt object time) :
    DebateCertificate D object where
  topics := [.momentariness]
  scope := fun x => model.existsAt x time
  opponentThesis := model.IntrinsicPower
  reason := fun x => model.Efficacious x time
  result := fun x => ¬ model.IntrinsicPower x
  pervasion := by
    intro x _ hefficacious
    exact model.causal_nonuniformity
      ((model.efficacious_iff_exists x time).mp hefficacious)
  refutes := by
    intro x _ hresult hopponent
    exact hresult hopponent
  subjectInScope := existsNow
  subjectReason := (model.efficacious_iff_exists object time).mpr existsNow

theorem causal_nonuniformity_refutes_intrinsic_power
    {D : Type u} {E : Type v} {T : Type w}
    (model : BuddhistComparativeLogic.Momentariness.Theory D E T) (time : T)
    {object : D} (existsNow : model.existsAt object time) :
    ¬ model.IntrinsicPower object :=
  (ofCausalNonuniformity model time existsNow).rejects_opponent

/-- The exact boundary inherited from the finite `eachMoment` model: causal
nonuniformity by itself is weaker than literal momentariness. -/
theorem causal_nonuniformity_is_not_literal_momentariness :
    (forall time, BuddhistComparativeLogic.Momentariness.eachMoment.existsAt () time) ∧
      ¬ BuddhistComparativeLogic.Momentariness.eachMoment.IntrinsicPower () ∧
      ¬ BuddhistComparativeLogic.Momentariness.eachMoment.Momentary () :=
  BuddhistComparativeLogic.Momentariness.causal_nonuniformity_is_not_yet_momentariness

/-- Uniform intrinsic activity and witnessed change are incompatible.  This
targets the activity account; it does not deny the `sarvasti` existence field. -/
def activityRule {D : Type u} {T : Type v}
    (model : BuddhistComparativeLogic.Sarvastivada.TriTemporal D T) : DebateRule D where
  topics := [.threeTimesActivity]
  scope := fun _ => True
  opponentThesis := fun d => forall t t', model.active d t <-> model.active d t'
  reason := fun d => exists t t', model.active d t ∧ ¬ model.active d t'
  result := fun d =>
    ¬ (forall t t', model.active d t <-> model.active d t')
  pervasion := by
    intro d _ hchange uniform
    obtain ⟨t, t', activeAt, inactiveAt⟩ := hchange
    exact inactiveAt ((uniform t t').mp activeAt)
  refutes := by
    intro d _ hresult hopponent
    exact hresult hopponent

def activityCertificate {D : Type u} {T : Type v}
    (model : BuddhistComparativeLogic.Sarvastivada.TriTemporal D T) {object : D}
    (changes : exists t t', model.active object t ∧
      ¬ model.active object t') : DebateCertificate D object where
  toDebateRule := activityRule model
  subjectInScope := trivial
  subjectReason := changes

/-- The concrete model retains existence at every time while its activity is
not uniform.  Thus this refutation cannot be promoted to a refutation of
Sarvāstivāda's all-times existence thesis. -/
theorem activity_refutation_does_not_refute_sarvasti :
    (forall time, BuddhistComparativeLogic.Sarvastivada.once.existsAt () time) ∧
      ¬ (forall t t', BuddhistComparativeLogic.Sarvastivada.once.active () t <->
        BuddhistComparativeLogic.Sarvastivada.once.active () t') := by
  refine And.intro (fun time =>
    BuddhistComparativeLogic.Sarvastivada.once.sarvasti () time) ?_
  have changes : exists t t', BuddhistComparativeLogic.Sarvastivada.once.active () t ∧
      ¬ BuddhistComparativeLogic.Sarvastivada.once.active () t' := by
    exact Exists.intro 5 (Exists.intro 0
      (And.intro rfl (by simp [BuddhistComparativeLogic.Sarvastivada.once])))
  exact (activityCertificate BuddhistComparativeLogic.Sarvastivada.once changes).rejects_opponent

/-! ## Apoha and appearance-model underdetermination -/

/-- Once a feature profile and its required features are fixed, two grounded
apoha pairs cannot disagree.  The fixed requirement is the substantive scope
restriction. -/
def ofFixedApohaGrounding {Object : Type u} {Feature : Type v}
    (has : BuddhistComparativeLogic.ApohaFeatures.FeatureProfile Object Feature)
    (requires : BuddhistComparativeLogic.ApohaFeatures.Requirements Feature)
    {positive negative positive' negative' : BuddhistComparativeLogic.Apoha.PredSet Object}
    (first : BuddhistComparativeLogic.ApohaFeatures.featureGroundedPair
      has requires positive negative)
    (second : BuddhistComparativeLogic.ApohaFeatures.featureGroundedPair
      has requires positive' negative') : DebateCertificate Unit () where
  topics := [.wordMeaning]
  scope := fun _ => True
  opponentThesis := fun _ => positive ≠ positive' ∨ negative ≠ negative'
  reason := fun _ =>
    BuddhistComparativeLogic.ApohaFeatures.featureGroundedPair
        has requires positive negative ∧
      BuddhistComparativeLogic.ApohaFeatures.featureGroundedPair
        has requires positive' negative'
  result := fun _ => positive = positive' ∧ negative = negative'
  pervasion := by
    intro _ _ hpairs
    exact BuddhistComparativeLogic.ApohaFeatures.fixed_features_determine_unique_pair
      has requires hpairs.1 hpairs.2
  refutes := by
    intro _ _ hequal hdisagree
    cases hdisagree with
    | inl hpositive => exact hpositive hequal.1
    | inr hnegative => exact hnegative hequal.2
  subjectInScope := trivial
  subjectReason := And.intro first second

theorem fixed_apoha_grounding_refutes_semantic_nonuniqueness
    {Object : Type u} {Feature : Type v}
    (has : BuddhistComparativeLogic.ApohaFeatures.FeatureProfile Object Feature)
    (requires : BuddhistComparativeLogic.ApohaFeatures.Requirements Feature)
    {positive negative positive' negative' : BuddhistComparativeLogic.Apoha.PredSet Object}
    (first : BuddhistComparativeLogic.ApohaFeatures.featureGroundedPair
      has requires positive negative)
    (second : BuddhistComparativeLogic.ApohaFeatures.featureGroundedPair
      has requires positive' negative') :
    positive = positive' ∧ negative = negative' :=
  (ofFixedApohaGrounding has requires first second).result_at_subject

/-- Varying the required feature restores semantic underdetermination, so the
preceding uniqueness theorem is not an unconditional theory of word meaning. -/
theorem feature_inventory_does_not_select_one_apoha_pair :
    BuddhistComparativeLogic.ApohaFeatures.componentClass
        BuddhistComparativeLogic.ApohaFeatures.sampleProfile
        BuddhistComparativeLogic.ApohaFeatures.requiresRed ≠
      BuddhistComparativeLogic.ApohaFeatures.componentClass
        BuddhistComparativeLogic.ApohaFeatures.sampleProfile
        BuddhistComparativeLogic.ApohaFeatures.requiresHot ∧
    BuddhistComparativeLogic.Apoha.compl
        (BuddhistComparativeLogic.ApohaFeatures.componentClass
          BuddhistComparativeLogic.ApohaFeatures.sampleProfile
          BuddhistComparativeLogic.ApohaFeatures.requiresRed) ≠
      BuddhistComparativeLogic.Apoha.compl
        (BuddhistComparativeLogic.ApohaFeatures.componentClass
          BuddhistComparativeLogic.ApohaFeatures.sampleProfile
          BuddhistComparativeLogic.ApohaFeatures.requiresHot) :=
  BuddhistComparativeLogic.ApohaFeatures.feature_inventory_alone_is_underdetermined

/-- Adequacy and the two observation-equivalence facts used by the finite
appearance comparison.  This bundle contains no cardinality conclusion. -/
def AppearanceEvidence : Prop :=
  BuddhistComparativeLogic.Vimsatika.naraka.adequate ∧
    BuddhistComparativeLogic.VimsatikaModels.observationEquivalent
      BuddhistComparativeLogic.Vimsatika.naraka
      BuddhistComparativeLogic.VimsatikaModels.narakaUnitIndexed.observations ∧
    BuddhistComparativeLogic.VimsatikaModels.observationEquivalent
      BuddhistComparativeLogic.Vimsatika.naraka
      BuddhistComparativeLogic.VimsatikaModels.narakaBoolIndexed.observations

/-- The certificate retains the observational evidence and rejects a
bijection between the finite index types.  The non-bijection follows from the
types themselves; the observational facts show that the two presentations
remain observationally equivalent despite that difference.  The index
carriers are not thereby interpreted as mind-independent substances. -/
def ofAppearanceUnderdetermination : DebateCertificate Unit () where
  topics := [.appearanceAndObjects]
  scope := fun _ => True
  opponentThesis := fun _ => exists f : Bool -> Unit,
    BuddhistComparativeLogic.VimsatikaModels.isBijection f
  reason := fun _ => AppearanceEvidence
  result := fun _ => AppearanceEvidence ∧
    ¬ (exists f : Bool -> Unit, BuddhistComparativeLogic.VimsatikaModels.isBijection f)
  pervasion := by
    intro _ _ evidence
    exact And.intro evidence
      BuddhistComparativeLogic.VimsatikaModels.no_bijection_bool_unit
  refutes := by
    intro _ _ hresult hopponent
    exact hresult.2 hopponent
  subjectInScope := trivial
  subjectReason := And.intro
    BuddhistComparativeLogic.Vimsatika.naraka_meets_all_four
    (And.intro BuddhistComparativeLogic.VimsatikaModels.naraka_unit_indexed_equivalent
      BuddhistComparativeLogic.VimsatikaModels.naraka_bool_indexed_equivalent)

theorem appearance_adequacy_does_not_fix_index_carrier_cardinality :
    AppearanceEvidence ∧
      ¬ (exists f : Bool -> Unit,
        BuddhistComparativeLogic.VimsatikaModels.isBijection f) :=
  ofAppearanceUnderdetermination.result_at_subject

/-! ## Finite registry countermodels -/

/-- A small vocabulary for testing claims about a multi-topic registry. -/
inductive DoctrinalClaim where
  | permanentSubstance
  | literalMomentaryDharma
  | representationOnly
  | emptyOwnBeing
  | exclusionMeaning
  deriving DecidableEq, Repr

inductive Polarity where
  | affirms
  | rejects
  deriving DecidableEq, Repr

/-- A generic registry records signed claims under topics; it is separate from
the heterogeneous debate adapters above and carries no consistency law unless
one is added explicitly. -/
abbrev Registry := Topic -> DoctrinalClaim -> Polarity -> Prop

def CoversEveryTopic (registry : Registry) : Prop :=
  forall topic, exists claim polarity, registry topic claim polarity

def JointlyConsistent (registry : Registry) : Prop :=
  forall claim, ¬
    ((exists topic, registry topic claim .affirms) ∧
      exists topic, registry topic claim .rejects)

/-- The total finite relation covers every topic and records both polarities
of every claim.  Coverage alone therefore has no consistency force. -/
def conflictingRegistry : Registry := fun _ _ _ => True

theorem debate_coverage_does_not_entail_joint_consistency :
    CoversEveryTopic conflictingRegistry ∧
      ¬ JointlyConsistent conflictingRegistry := by
  constructor
  · intro topic
    exact Exists.intro .permanentSubstance
      (Exists.intro .affirms trivial)
  · intro consistent
    exact consistent .permanentSubstance
      (And.intro
        (Exists.intro .momentariness trivial)
        (Exists.intro .wordMeaning trivial))

/-- A Boolean valuation is separate from a registry's negative verdicts. -/
def Supported (valuation : DoctrinalClaim -> Bool)
    (claim : DoctrinalClaim) : Prop := valuation claim = true

def Rejected (valuation : DoctrinalClaim -> Bool)
    (claim : DoctrinalClaim) : Prop := valuation claim = false

def AllBuddhistAlternatives (valuation : DoctrinalClaim -> Bool) : Prop :=
  Supported valuation .literalMomentaryDharma ∧
    Supported valuation .representationOnly ∧
    Supported valuation .emptyOwnBeing ∧
    Supported valuation .exclusionMeaning

def noPositiveAlternative : DoctrinalClaim -> Bool := fun _ => false

/-- A valuation may reject permanence while supporting none of the four
listed alternatives.  A reductio of one opponent is not a proof of a whole
positive system. -/
theorem one_refutation_does_not_prove_all_buddhist_alternatives :
    Rejected noPositiveAlternative .permanentSubstance ∧
      ¬ AllBuddhistAlternatives noPositiveAlternative := by
  constructor
  · rfl
  · intro allSupported
    exact Bool.noConfusion allSupported.1

/-- One premise is licensed only in the momentariness examination. -/
def localPremise : Topic -> Prop
  | .momentariness => True
  | _ => False

/-- A chapter-local premise can hold nonvacuously while universal promotion
over the selected registry fails. -/
theorem chapter_local_premise_does_not_become_universal :
    localPremise .momentariness ∧
      ¬ (forall topic, localPremise topic) := by
  constructor
  · trivial
  · intro universal
    exact universal .wordMeaning

end BuddhistComparativeLogic.Tattvasamgraha
