/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Apoha

/-!
# Feature-grounded apoha

Bare mutual complementation determines the negative extension only after a
positive extension has already been chosen.  This module adds a component
semantics: a concept is fixed by the features it requires, and its positive
extension contains exactly the objects having every required feature.

The result is deliberately conditional.  A fixed feature profile and a fixed
requirement determine one apoha pair uniquely, but the feature inventory alone
does not determine which requirements constitute the concept.  The final
finite model witnesses that remaining choice.
-/

namespace BuddhistComparativeLogic.ApohaFeatures

open BuddhistComparativeLogic.Apoha

abbrev FeatureProfile (Object : Type u) (Feature : Type v) :=
  Object → Feature → Prop

abbrev Requirements (Feature : Type v) := Feature → Prop

/-- An object falls under a component concept exactly when it has every
feature required by the concept. -/
def componentClass (has : FeatureProfile Object Feature)
    (requires : Requirements Feature) : PredSet Object :=
  fun x => ∀ f, requires f → has x f

/-- Adding requirements composes concepts by intersection. -/
theorem componentClass_or
    (has : FeatureProfile Object Feature)
    (left right : Requirements Feature) :
    componentClass has (fun f => left f ∨ right f) =
      fun x => componentClass has left x ∧ componentClass has right x := by
  funext x
  apply propext
  constructor
  · intro hx
    constructor
    · intro f hf
      exact hx f (Or.inl hf)
    · intro f hf
      exact hx f (Or.inr hf)
  · rintro ⟨hl, hr⟩ f (hf | hf)
    · exact hl f hf
    · exact hr f hf

/-- Membership depends only on the required components of a profile. -/
theorem component_extensional
    (has : FeatureProfile Object Feature)
    (requires : Requirements Feature) {x y : Object}
    (agree : ∀ f, requires f → (has x f ↔ has y f)) :
    componentClass has requires x ↔ componentClass has requires y := by
  constructor
  · intro hx f hf
    exact (agree f hf).mp (hx f hf)
  · intro hy f hf
    exact (agree f hf).mpr (hy f hf)

/-- A feature-grounded apoha analysis records both the constructive positive
criterion and exclusion of its complement. -/
def featureGroundedPair
    (has : FeatureProfile Object Feature)
    (requires : Requirements Feature)
    (positive negative : PredSet Object) : Prop :=
  positive = componentClass has requires ∧ apohaPair positive negative

theorem featureGroundedPair_exists
    (has : FeatureProfile Object Feature)
    (requires : Requirements Feature) :
    featureGroundedPair has requires
      (componentClass has requires) (compl (componentClass has requires)) := by
  exact ⟨rfl, apoha_pair_underdetermined _⟩

/-- Once the component criterion is fixed, both extensions are fixed.  Thus
features remove the arbitrary choice exposed by `apoha_pair_underdetermined`
at the level of extensions. -/
theorem fixed_features_determine_unique_pair
    (has : FeatureProfile Object Feature)
    (requires : Requirements Feature)
    {positive negative positive' negative' : PredSet Object}
    (h : featureGroundedPair has requires positive negative)
    (h' : featureGroundedPair has requires positive' negative') :
    positive = positive' ∧ negative = negative' := by
  have hp : positive = positive' := h.1.trans h'.1.symm
  have hn : negative = compl positive :=
    (apoha_pair_no_constraint positive negative).mp h.2
  have hn' : negative' = compl positive' :=
    (apoha_pair_no_constraint positive' negative').mp h'.2
  exact ⟨hp, hn.trans ((congrArg compl hp).trans hn'.symm)⟩

/-! ## A finite regression test for residual underdetermination -/

inductive SampleObject where
  | ruby
  | ember
  deriving DecidableEq, Repr

inductive SampleFeature where
  | red
  | hot
  deriving DecidableEq, Repr

open SampleObject SampleFeature

def sampleProfile : FeatureProfile SampleObject SampleFeature
  | .ruby, .red => True
  | .ruby, .hot => False
  | .ember, .red => False
  | .ember, .hot => True

def requiresRed : Requirements SampleFeature := fun f => f = .red

def requiresHot : Requirements SampleFeature := fun f => f = .hot

theorem ruby_is_red_not_hot :
    componentClass sampleProfile requiresRed .ruby ∧
      ¬ componentClass sampleProfile requiresHot .ruby := by
  constructor
  · intro f hf
    subst f
    trivial
  · intro h
    exact h .hot rfl

theorem ember_is_hot_not_red :
    componentClass sampleProfile requiresHot .ember ∧
      ¬ componentClass sampleProfile requiresRed .ember := by
  constructor
  · intro f hf
    subst f
    trivial
  · intro h
    exact h .red rfl

/-- The same objects and feature facts support distinct concepts when the
required component is allowed to vary.  Feature grounding therefore moves the
remaining underdetermination to the choice of a feature specification rather
than eliminating it unconditionally. -/
theorem feature_inventory_alone_is_underdetermined :
    componentClass sampleProfile requiresRed ≠
        componentClass sampleProfile requiresHot ∧
      compl (componentClass sampleProfile requiresRed) ≠
        compl (componentClass sampleProfile requiresHot) := by
  have hpos : componentClass sampleProfile requiresRed ≠
      componentClass sampleProfile requiresHot := by
    intro h
    have hruby := congrFun h .ruby
    exact ruby_is_red_not_hot.2 (hruby.mp ruby_is_red_not_hot.1)
  constructor
  · exact hpos
  · intro hcompl
    have h := congrArg compl hcompl
    have heq : componentClass sampleProfile requiresRed =
        componentClass sampleProfile requiresHot := by
      simpa [compl_compl] using h
    exact hpos heq

/-- Exact diagnosis: fixed requirements give uniqueness, while merely
quantifying over some feature requirement restores multiple grounded pairs. -/
theorem conditional_resolution_of_apoha_underdetermination :
    (∀ positive negative positive' negative',
        featureGroundedPair sampleProfile requiresRed positive negative →
        featureGroundedPair sampleProfile requiresRed positive' negative' →
        positive = positive' ∧ negative = negative') ∧
      (∃ redPositive redNegative hotPositive hotNegative,
        featureGroundedPair sampleProfile requiresRed redPositive redNegative ∧
        featureGroundedPair sampleProfile requiresHot hotPositive hotNegative ∧
        redPositive ≠ hotPositive ∧ redNegative ≠ hotNegative) := by
  constructor
  · intro positive negative positive' negative'
    exact fixed_features_determine_unique_pair sampleProfile requiresRed
  · refine ⟨componentClass sampleProfile requiresRed,
      compl (componentClass sampleProfile requiresRed),
      componentClass sampleProfile requiresHot,
      compl (componentClass sampleProfile requiresHot),
      featureGroundedPair_exists _ _, featureGroundedPair_exists _ _, ?_⟩
    exact feature_inventory_alone_is_underdetermined

/-! ## Features as terms: a second grounding layer and its boundary

The preceding results take the requirement on features as fixed.  A second
component layer can instead treat features themselves as the objects to be
classified by higher features.  This removes the lower choice only when the
higher requirement is fixed; it does not make the hierarchy terminate by
itself.
-/

/-- A lower feature requirement is grounded by the higher features that every
selected lower feature must possess. -/
def RequirementGroundedBy
    (hasHigher : FeatureProfile Feature HigherFeature)
    (higherRequires : Requirements HigherFeature)
    (lowerRequires : Requirements Feature) : Prop :=
  lowerRequires = componentClass hasHigher higherRequires

/-- Both the lower requirement and the resulting apoha pair are grounded in a
two-layer component analysis. -/
def twoLayerGroundedPair
    (hasObject : FeatureProfile Object Feature)
    (hasHigher : FeatureProfile Feature HigherFeature)
    (higherRequires : Requirements HigherFeature)
    (lowerRequires : Requirements Feature)
    (positive negative : PredSet Object) : Prop :=
  RequirementGroundedBy hasHigher higherRequires lowerRequires ∧
    featureGroundedPair hasObject lowerRequires positive negative

/-- Fixing the higher profile and its requirement fixes the induced lower
requirement and hence both extensions.  This is the explicit stopping
condition for the two-layer construction. -/
theorem fixed_higher_requirement_stops_two_layer_regress
    (hasObject : FeatureProfile Object Feature)
    (hasHigher : FeatureProfile Feature HigherFeature)
    (higherRequires : Requirements HigherFeature)
    {lower lower' : Requirements Feature}
    {positive negative positive' negative' : PredSet Object}
    (h : twoLayerGroundedPair hasObject hasHigher higherRequires
      lower positive negative)
    (h' : twoLayerGroundedPair hasObject hasHigher higherRequires
      lower' positive' negative') :
    lower = lower' ∧ positive = positive' ∧ negative = negative' := by
  have hlower : lower = lower' := h.1.trans h'.1.symm
  have hpairs := fixed_features_determine_unique_pair hasObject lower
    h.2 (hlower ▸ h'.2)
  exact ⟨hlower, hpairs⟩

/-! Reapplying component grounding to requirements of one fixed feature type
makes the regress executable. -/

/-- One higher-feature step when features at adjacent levels share a type. -/
def liftRequirement (hasHigher : FeatureProfile Feature Feature)
    (requires : Requirements Feature) : Requirements Feature :=
  componentClass hasHigher requires

/-- The requirement obtained after `n` successively higher feature layers. -/
def requirementChain (hasHigher : FeatureProfile Feature Feature)
    (seed : Requirements Feature) : Nat → Requirements Feature
  | 0 => seed
  | n + 1 => liftRequirement hasHigher (requirementChain hasHigher seed n)

def StableRequirement (hasHigher : FeatureProfile Feature Feature)
    (requires : Requirements Feature) : Prop :=
  liftRequirement hasHigher requires = requires

/-- A fixed requirement is a genuine finite stopping basis: adding any number
of further copies of the same grounding layer changes nothing. -/
theorem stable_requirement_stops_regress
    (hasHigher : FeatureProfile Feature Feature)
    (requires : Requirements Feature)
    (stable : StableRequirement hasHigher requires) (n : Nat) :
    requirementChain hasHigher requires n = requires := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [requirementChain, ih]
      exact stable

/-! A finite countermodel shows that a higher-feature layer need not supply a
stopping basis.  If each Boolean feature is selected by excluding itself, the
grounding operator is exactly predicate complementation. -/

def selfExcludingProfile : FeatureProfile Bool Bool :=
  fun feature higherFeature => feature ≠ higherFeature

theorem self_excluding_lift_is_complement (requires : Requirements Bool) :
    liftRequirement selfExcludingProfile requires = compl requires := by
  funext feature
  apply propext
  constructor
  · intro h hFeature
    exact h feature hFeature rfl
  · intro hNot feature' hFeature' hEq
    subst feature'
    exact hNot hFeature'

/-- Self-excluding feature grounding alternates with period two. -/
theorem self_excluding_regress_oscillates
    (requires : Requirements Bool) (n : Nat) :
    requirementChain selfExcludingProfile requires (n + 2) =
      requirementChain selfExcludingProfile requires n := by
  change liftRequirement selfExcludingProfile
      (liftRequirement selfExcludingProfile
        (requirementChain selfExcludingProfile requires n)) = _
  rw [self_excluding_lift_is_complement,
    self_excluding_lift_is_complement, compl_compl]

/-- Thus no finite level of the self-excluding hierarchy is stable.  A
primitive or fixed higher requirement is an additional premise, rather than a
consequence of component semantics alone. -/
theorem self_excluding_regress_never_stops
    (requires : Requirements Bool) (n : Nat) :
    requirementChain selfExcludingProfile requires (n + 1) ≠
      requirementChain selfExcludingProfile requires n := by
  change liftRequirement selfExcludingProfile
      (requirementChain selfExcludingProfile requires n) ≠ _
  rw [self_excluding_lift_is_complement]
  intro stable
  exact apoha_no_fixpoint (α := Bool)
    (requirementChain selfExcludingProfile requires n) stable.symm

end BuddhistComparativeLogic.ApohaFeatures
