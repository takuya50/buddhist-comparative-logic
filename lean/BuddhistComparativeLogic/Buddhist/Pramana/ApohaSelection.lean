/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.ApohaFeatures

/-!
# Selection principles for feature-grounded apoha

Feature grounding fixes an apoha pair only after its required features have
been fixed.  This module makes the remaining selection step explicit.  A rule
states which requirements are admissible and when one admissible requirement
is no worse than another.  Antisymmetry on admissible candidates makes an
optimal requirement unique, after which the existing component theorem fixes
both the positive and negative extensions.

The final two-feature model distinguishes this substantive selection
principle from mere admissibility.  The same admissible candidates are unique
when evidence ranks red above hot and remain underdetermined when every
candidate ties.
-/

namespace BuddhistComparativeLogic.ApohaSelection

open Apoha
open ApohaFeatures

universe u v

/-- A requirement-selection rule separates the candidate filter from its
comparative standard. -/
structure SelectionRule (Feature : Type v) where
  admissible : Requirements Feature → Prop
  noWorse : Requirements Feature → Requirements Feature → Prop

namespace SelectionRule

variable {Feature : Type v} (R : SelectionRule Feature)

/-- An optimal requirement is admissible and no worse than every admissible
alternative. -/
def Optimal (requires : Requirements Feature) : Prop :=
  R.admissible requires ∧
    ∀ alternative, R.admissible alternative → R.noWorse requires alternative

/-- Antisymmetry is required only on the admitted candidate domain. -/
def AntisymmetricOnAdmissible : Prop :=
  ∀ {left right}, R.admissible left → R.admissible right →
    R.noWorse left right → R.noWorse right left → left = right

theorem optimal_unique (antisymmetric : R.AntisymmetricOnAdmissible)
    {left right : Requirements Feature}
    (hleft : R.Optimal left) (hright : R.Optimal right) : left = right := by
  exact antisymmetric hleft.1 hright.1
    (hleft.2 right hright.1) (hright.2 left hleft.1)

end SelectionRule

/-- The selection layer and the component layer are kept as separate
conjuncts so each can be audited independently. -/
def SelectedGrounding
    (R : SelectionRule Feature) (has : FeatureProfile Object Feature)
    (requires : Requirements Feature)
    (positive negative : PredSet Object) : Prop :=
  R.Optimal requires ∧ featureGroundedPair has requires positive negative

/-- An antisymmetric selection principle removes the requirement-level choice;
component grounding then removes the remaining extension-level choice. -/
theorem selected_grounding_unique
    (R : SelectionRule Feature) (has : FeatureProfile Object Feature)
    (antisymmetric : R.AntisymmetricOnAdmissible)
    {requires requires' : Requirements Feature}
    {positive negative positive' negative' : PredSet Object}
    (h : SelectedGrounding R has requires positive negative)
    (h' : SelectedGrounding R has requires' positive' negative') :
    requires = requires' ∧ positive = positive' ∧ negative = negative' := by
  have hrequires : requires = requires' :=
    R.optimal_unique antisymmetric h.1 h'.1
  have hpairs := fixed_features_determine_unique_pair has requires
    h.2 (hrequires ▸ h'.2)
  exact ⟨hrequires, hpairs⟩

/-- Existence is separate from uniqueness: an explicitly supplied optimal
candidate always induces a selected grounded pair. -/
theorem selected_grounding_exists
    (R : SelectionRule Feature) (has : FeatureProfile Object Feature)
    {requires : Requirements Feature} (optimal : R.Optimal requires) :
    SelectedGrounding R has requires
      (componentClass has requires) (compl (componentClass has requires)) := by
  exact ⟨optimal, featureGroundedPair_exists has requires⟩

/-! ## A finite selection and omission audit -/

open SampleFeature

def redOrHot (requires : Requirements SampleFeature) : Prop :=
  requires = requiresRed ∨ requires = requiresHot

/-- Evidence prefers the red requirement; equality covers comparison with
the selected candidate itself. -/
def redEvidenceRule : SelectionRule SampleFeature where
  admissible := redOrHot
  noWorse left right := left = requiresRed ∨ left = right

theorem sample_requirements_distinct : requiresRed ≠ requiresHot := by
  intro equal
  have atRed := congrFun equal .red
  simp [requiresRed, requiresHot] at atRed

theorem redEvidence_optimal : redEvidenceRule.Optimal requiresRed := by
  constructor
  · exact Or.inl rfl
  · intro alternative _
    exact Or.inl rfl

theorem redEvidence_antisymmetric :
    redEvidenceRule.AntisymmetricOnAdmissible := by
  intro left right hleft hright hlr hrl
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright <;>
      subst left <;> subst right
  · rfl
  · rcases hrl with impossible | impossible
    · exact False.elim (sample_requirements_distinct impossible.symm)
    · exact False.elim (sample_requirements_distinct impossible.symm)
  · rcases hlr with impossible | impossible
    · exact False.elim (sample_requirements_distinct impossible.symm)
    · exact False.elim (sample_requirements_distinct impossible.symm)
  · rfl

theorem redEvidence_selects_exactly_red
    {requires : Requirements SampleFeature} :
    redEvidenceRule.Optimal requires ↔ requires = requiresRed := by
  constructor
  · intro optimal
    exact redEvidenceRule.optimal_unique redEvidence_antisymmetric
      optimal redEvidence_optimal
  · intro equal
    cases equal
    exact redEvidence_optimal

theorem redEvidence_unique_grounded_pair
    {requires requires' : Requirements SampleFeature}
    {positive negative positive' negative' : PredSet SampleObject}
    (h : SelectedGrounding redEvidenceRule sampleProfile requires
      positive negative)
    (h' : SelectedGrounding redEvidenceRule sampleProfile requires'
      positive' negative') :
    requires = requires' ∧ positive = positive' ∧ negative = negative' :=
  selected_grounding_unique redEvidenceRule sampleProfile
    redEvidence_antisymmetric h h'

/-- The red evidence rule yields a nonvacuous selected pair. -/
theorem redEvidence_grounding_nonempty :
    SelectedGrounding redEvidenceRule sampleProfile requiresRed
      (componentClass sampleProfile requiresRed)
      (compl (componentClass sampleProfile requiresRed)) :=
  selected_grounding_exists redEvidenceRule sampleProfile redEvidence_optimal

/-- Keeping the same candidates but treating every comparison as a tie. -/
def tiedRule : SelectionRule SampleFeature where
  admissible := redOrHot
  noWorse _ _ := True

theorem tied_red_optimal : tiedRule.Optimal requiresRed := by
  exact ⟨Or.inl rfl, fun _ _ => trivial⟩

theorem tied_hot_optimal : tiedRule.Optimal requiresHot := by
  exact ⟨Or.inr rfl, fun _ _ => trivial⟩

/-- Admissibility and total comparability alone do not select a requirement. -/
theorem admissibility_without_antisymmetry_is_underdetermined :
    tiedRule.Optimal requiresRed ∧ tiedRule.Optimal requiresHot ∧
      requiresRed ≠ requiresHot ∧
      ¬ tiedRule.AntisymmetricOnAdmissible := by
  refine ⟨tied_red_optimal, tied_hot_optimal,
    sample_requirements_distinct, ?_⟩
  intro antisymmetric
  exact sample_requirements_distinct
    (tiedRule.optimal_unique antisymmetric tied_red_optimal tied_hot_optimal)

/-- The missing selection principle propagates to two distinct apoha pairs,
even though each pair is fully grounded relative to its own requirement. -/
theorem tied_rule_leaves_apoha_pair_underdetermined :
    SelectedGrounding tiedRule sampleProfile requiresRed
        (componentClass sampleProfile requiresRed)
        (compl (componentClass sampleProfile requiresRed)) ∧
      SelectedGrounding tiedRule sampleProfile requiresHot
        (componentClass sampleProfile requiresHot)
        (compl (componentClass sampleProfile requiresHot)) ∧
      componentClass sampleProfile requiresRed ≠
        componentClass sampleProfile requiresHot ∧
      compl (componentClass sampleProfile requiresRed) ≠
        compl (componentClass sampleProfile requiresHot) := by
  exact ⟨selected_grounding_exists tiedRule sampleProfile tied_red_optimal,
    selected_grounding_exists tiedRule sampleProfile tied_hot_optimal,
    feature_inventory_alone_is_underdetermined⟩

end BuddhistComparativeLogic.ApohaSelection
