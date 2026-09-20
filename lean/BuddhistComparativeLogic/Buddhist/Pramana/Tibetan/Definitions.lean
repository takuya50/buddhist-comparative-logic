/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.ApohaFeatures
import BuddhistComparativeLogic.Buddhist.Pramana.Pramanasamuccaya

/-!
# Definition, definiendum, and definitional basis

This module gives a restrained predicate model of the three items commonly
distinguished in Tibetan discussions of definition: a defining condition, a
definiendum, and a basis on which the condition is instantiated.  It is not
an edition of a Tibetan *bsdus grwa* text and does not claim that extensional
predicates capture every intensional, linguistic, or pedagogical constraint
used by a particular author or monastery.

The defining condition reuses the component semantics of `ApohaFeatures`.
A parameterized standard records any further admissibility condition instead
of deriving it from coextension.  A certified triad supplies coextension, an
actual basis, and that independent license.  It then induces both a
feature-grounded apoha pair and a `Pramanasamuccaya.GroundedConcept`.  Finite
models show that coextension plus a basis does not imply admissibility, and
that the same extension and basis need not determine a unique requirement.
-/

namespace BuddhistComparativeLogic.TibetanDefinitions

open BuddhistComparativeLogic.Apoha
open BuddhistComparativeLogic.ApohaFeatures

/-- Additional constraints on which feature requirements count as acceptable
definitions.  The formalism leaves the standard parameterized rather than
pretending that extensional agreement supplies historical correctness. -/
structure DefinitionStandard (Feature : Type v) where
  licensed : Requirements Feature -> Prop

/-- The three explicit terms of the model.  `requires` generates the defining
condition from `hasFeatures`; `definiendum` is the target predicate; and
`basis` is the object offered as an instance. -/
structure DefinitionTriad (Object : Type u) (Feature : Type v) where
  hasFeatures : FeatureProfile Object Feature
  requires : Requirements Feature
  definiendum : PredSet Object
  basis : Object

namespace DefinitionTriad

variable {Object : Type u} {Feature : Type v}

def definingCondition (triad : DefinitionTriad Object Feature) :
    PredSet Object :=
  componentClass triad.hasFeatures triad.requires

/-- Extensional fit is one auditable obligation, kept separate from both
instantiation and the governing definition standard. -/
def Coextensive (triad : DefinitionTriad Object Feature) : Prop :=
  forall object, triad.definiendum object <-> triad.definingCondition object

/-- The proposed basis actually satisfies the defining condition. -/
def BasisFits (triad : DefinitionTriad Object Feature) : Prop :=
  triad.definingCondition triad.basis

end DefinitionTriad

/-- A certificate records three independent checks.  The third is abstract
because different textual contexts may license definitions differently. -/
structure DefinitionCertificate
    (standard : DefinitionStandard Feature)
    (triad : DefinitionTriad Object Feature) : Prop where
  coextensive : triad.Coextensive
  basisFits : triad.BasisFits
  licensed : standard.licensed triad.requires

namespace DefinitionCertificate

variable {Object : Type u} {Feature : Type v}
  {standard : DefinitionStandard Feature}
  {triad : DefinitionTriad Object Feature}

theorem basis_is_definiendum
    (certificate : DefinitionCertificate standard triad) :
    triad.definiendum triad.basis :=
  (certificate.coextensive triad.basis).mpr certificate.basisFits

/-- A certified extensional fit determines the positive extension and its
complement once the feature requirement has been supplied. -/
theorem determines_feature_grounded_pair
    (certificate : DefinitionCertificate standard triad) :
    featureGroundedPair triad.hasFeatures triad.requires triad.definiendum
      (compl triad.definiendum) := by
  have positive : triad.definiendum = triad.definingCondition := by
    funext object
    exact propext (certificate.coextensive object)
  exact ⟨positive, apoha_pair_underdetermined triad.definiendum⟩

end DefinitionCertificate

/-! ## Bridge to the existing grounded-concept interface -/

/-- Objects are equivalent here when they agree on every required feature.
This is only an equivalence-like grounding relation; the construction makes
no causal claim about the features. -/
def requiredFeatureGrounding (triad : DefinitionTriad Object Feature) :
    Grounding Object where
  sameEffect left right :=
    forall feature, triad.requires feature ->
      (triad.hasFeatures left feature <-> triad.hasFeatures right feature)
  refl := by
    intro object feature required
    exact Iff.rfl
  symm := by
    intro left right agreement feature required
    exact (agreement feature required).symm
  trans := by
    intro left middle right first second feature required
    exact (first feature required).trans (second feature required)

/-- Repackage the basis and required-feature relation using the grounded
concept API of the `Pramanasamuccaya` module. -/
def asGroundedConcept (triad : DefinitionTriad Object Feature) :
    Pramanasamuccaya.GroundedConcept Object where
  grounding := requiredFeatureGrounding triad
  exemplar := triad.basis

namespace DefinitionCertificate

variable {Object : Type u} {Feature : Type v}
  {standard : DefinitionStandard Feature}
  {triad : DefinitionTriad Object Feature}

/-- Because the certified basis has every required feature, its equivalence
class contains exactly the objects satisfying the defining condition, hence
exactly the definiendum. -/
theorem groundedConcept_extension_eq
    (certificate : DefinitionCertificate standard triad) :
    (asGroundedConcept triad).extension = triad.definiendum := by
  funext object
  apply propext
  constructor
  · intro agreement
    apply (certificate.coextensive object).mpr
    intro feature required
    exact (agreement feature required).mp
      (certificate.basisFits feature required)
  · intro belongs feature required
    have objectHas : triad.hasFeatures object feature :=
      (certificate.coextensive object).mp belongs feature required
    exact ⟨fun _ => objectHas,
      fun _ => certificate.basisFits feature required⟩

/-- The certified triad has a licensed requirement, an inhabited target, a
feature-grounded complement pair, and an equivalence-grounded extension.
Each conjunct retains the premise from which it arises. -/
theorem sound_and_grounded
    (certificate : DefinitionCertificate standard triad) :
    standard.licensed triad.requires /\
      triad.definiendum triad.basis /\
      featureGroundedPair triad.hasFeatures triad.requires triad.definiendum
        (compl triad.definiendum) /\
      (asGroundedConcept triad).grounding.grounded triad.definiendum := by
  refine ⟨certificate.licensed, certificate.basis_is_definiendum,
    certificate.determines_feature_grounded_pair, ?_⟩
  rw [← certificate.groundedConcept_extension_eq]
  exact (asGroundedConcept triad).extension_is_grounded

/-- The existing apoha exclusion theorem transports across the certified
identification of the grounded extension with the definiendum. -/
theorem classified_iff_not_excluded
    (certificate : DefinitionCertificate standard triad) (object : Object) :
    triad.definiendum object <->
      ¬ (asGroundedConcept triad).exclusion object := by
  rw [← certificate.groundedConcept_extension_eq]
  exact (asGroundedConcept triad).classified_iff_not_excluded object

end DefinitionCertificate

/-! ## Existing finite feature model: an inhabited certificate -/

def redStandard : DefinitionStandard SampleFeature where
  licensed := fun requirements => requirements = requiresRed

def redTriad : DefinitionTriad SampleObject SampleFeature where
  hasFeatures := sampleProfile
  requires := requiresRed
  definiendum := componentClass sampleProfile requiresRed
  basis := .ruby

theorem redCertificate : DefinitionCertificate redStandard redTriad where
  coextensive := fun _ => Iff.rfl
  basisFits := ruby_is_red_not_hot.1
  licensed := rfl

/-- Nonvacuity: an actual certificate classifies the ruby and excludes the
ember, so neither the basis nor the target extension is merely postulated as
an empty predicate. -/
theorem certified_definition_nonvacuous :
    Nonempty (DefinitionCertificate redStandard redTriad) /\
      redTriad.definiendum .ruby /\
      ¬ redTriad.definiendum .ember := by
  exact ⟨⟨redCertificate⟩, ruby_is_red_not_hot.1,
    ember_is_hot_not_red.2⟩

/-! ## Missing-license and reverse-uniqueness countermodels -/

def hotOnlyStandard : DefinitionStandard SampleFeature where
  licensed := fun requirements => requirements = requiresHot

theorem red_and_hot_requirements_distinct : requiresRed ≠ requiresHot := by
  intro equality
  have atRed := congrFun equality SampleFeature.red
  simp [requiresRed, requiresHot] at atRed

/-- On the two-object sample, the red proposal is exactly coextensive with
its target and has a genuine basis.  Those facts do not make it licensed by
an independently supplied hot-only standard. -/
theorem coextension_and_basis_do_not_entail_license :
    redTriad.Coextensive /\ redTriad.BasisFits /\
      ¬ hotOnlyStandard.licensed redTriad.requires /\
      ¬ DefinitionCertificate hotOnlyStandard redTriad := by
  refine ⟨fun _ => Iff.rfl, ruby_is_red_not_hot.1, ?_, ?_⟩
  · exact red_and_hot_requirements_distinct
  · intro certificate
    exact red_and_hot_requirements_distinct certificate.licensed

inductive TwinObject where
  | marked
  | plain
  deriving DecidableEq, Repr

inductive TwinFeature where
  | left
  | right
  deriving DecidableEq, Repr

/-- Both features have the same distribution over the two objects. -/
def twinProfile : FeatureProfile TwinObject TwinFeature
  | .marked, _ => True
  | .plain, _ => False

def requiresLeft : Requirements TwinFeature := fun feature => feature = .left
def requiresRight : Requirements TwinFeature := fun feature => feature = .right

theorem twin_requirements_distinct : requiresLeft ≠ requiresRight := by
  intro equality
  have atLeft := congrFun equality TwinFeature.left
  simp [requiresLeft, requiresRight] at atLeft

theorem twin_conditions_coextensive :
    componentClass twinProfile requiresLeft =
      componentClass twinProfile requiresRight := by
  funext object
  apply propext
  cases object <;>
    simp [componentClass, twinProfile, requiresLeft, requiresRight]

def leftTriad : DefinitionTriad TwinObject TwinFeature where
  hasFeatures := twinProfile
  requires := requiresLeft
  definiendum := fun object => object = .marked
  basis := .marked

def rightTriad : DefinitionTriad TwinObject TwinFeature where
  hasFeatures := twinProfile
  requires := requiresRight
  definiendum := fun object => object = .marked
  basis := .marked

/-- Even with the same finite object profile, target extension, and basis,
equality of defining conditions does not reverse to equality of feature
requirements.  An intensional or rule-based uniqueness premise would have to
be supplied separately. -/
theorem extension_and_basis_do_not_determine_requirement :
    leftTriad.definiendum = rightTriad.definiendum /\
      leftTriad.basis = rightTriad.basis /\
      leftTriad.definingCondition = rightTriad.definingCondition /\
      leftTriad.requires ≠ rightTriad.requires /\
      ¬ (leftTriad.definingCondition = rightTriad.definingCondition ->
        leftTriad.requires = rightTriad.requires) := by
  refine ⟨rfl, rfl, ?_, twin_requirements_distinct, ?_⟩
  · exact twin_conditions_coextensive
  · intro reverse
    exact twin_requirements_distinct (reverse twin_conditions_coextensive)

end BuddhistComparativeLogic.TibetanDefinitions
