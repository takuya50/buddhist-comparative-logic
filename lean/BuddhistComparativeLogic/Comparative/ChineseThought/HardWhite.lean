/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.ApohaFeatures
import BuddhistComparativeLogic.Comparative.ChineseThought.WhiteHorse
import BuddhistComparativeLogic.Buddhist.Yogacara.Sahopalambha

/-!
# Sensory access and co-inherence in a Hard/White audit

This module gives a small typed reconstruction motivated by the received
"Hard and White" discussion in the *Gongsun Longzi*.  Sight and touch are
modeled as different access channels, while whiteness and hardness are
modeled as qualities which can inhere in one stone.  Distinct sensory access
profiles are provable without identifying sensory distinction with separate
substances.

The textual history and philosophical interpretation of the received
dialogue are disputed.  The development therefore isolates one argument
boundary: a difference between what sight and touch register does not, by
itself, entail that the registered qualities have numerically distinct
bearers.  It does not claim that this model is the uniquely correct reading
of Gongsun Long, or that sensory reports exhaust the dialogue's metaphysics.

Source status (accessed 2026-09-19): the received Chinese *Jianbai lun* is
located at <https://ctext.org/gongsunlongzi/jian-bai-lun>.  Graham's historical
study is <https://doi.org/10.1017/S0041977X00062261>, and the University of
Zurich records the work's disputed textual history at
<https://www.aoi.uzh.ch/en/institut/geschichte/asienundeuropa/aboutus/bulletin/2015/gongsunlongzi.html>.
Only the Chinese witness is used; the site's user/AI English rendering is not
adopted or reproduced.  `SensoryModel` and the one-stone countermodel are
project-authored reconstructions.
-/

namespace BuddhistComparativeLogic.HardWhite

universe u v w

/-! ## Generic sensory-access semantics -/

/-- A sensory model separates the inherence of a quality from a sense's
registration of it.  `detectionSound` is the only generic bridge from access
to inherence. -/
structure SensoryModel
    (Substance : Type u) (Quality : Type v) (Sense : Type w) where
  hasQuality : Substance -> Quality -> Prop
  detects : Sense -> Substance -> Quality -> Prop
  detectionSound : forall sense substance quality,
    detects sense substance quality -> hasQuality substance quality

namespace SensoryModel

variable {Substance : Type u} {Quality : Type v} {Sense : Type w}
  (model : SensoryModel Substance Quality Sense)

/-- The complete sensory trace of one quality at one substance. -/
def accessProfile (substance : Substance) (quality : Quality) : Sense -> Prop :=
  fun sense => model.detects sense substance quality

/-- Two qualities are observationally distinct when their access profiles
differ at the selected substance. -/
def ObservationallyDistinct
    (substance : Substance) (left right : Quality) : Prop :=
  model.accessProfile substance left ≠ model.accessProfile substance right

/-- Each quality is selectively available to some channel which does not
register the other. -/
def SeparatelyAccessible
    (substance : Substance) (left right : Quality) : Prop :=
  exists leftSense rightSense,
    model.detects leftSense substance left /\
      ¬ model.detects leftSense substance right /\
      model.detects rightSense substance right /\
      ¬ model.detects rightSense substance left

/-- Both qualities inhere in the same supplied substance. -/
def CoInhere (substance : Substance) (left right : Quality) : Prop :=
  model.hasQuality substance left /\ model.hasQuality substance right

/-- There are distinct bearers of the two qualities.  This is deliberately
stronger than either access-profile difference or co-inherence. -/
def SeparateBearers (left right : Quality) : Prop :=
  exists leftBearer rightBearer,
    leftBearer ≠ rightBearer /\
      model.hasQuality leftBearer left /\
      model.hasQuality rightBearer right

/-- A single asymmetric observation already distinguishes two complete
access profiles. -/
theorem profilesDistinctOfDetectionGap
    {substance : Substance} {left right : Quality} {sense : Sense}
    (detectsLeft : model.detects sense substance left)
    (missesRight : ¬ model.detects sense substance right) :
    model.ObservationallyDistinct substance left right := by
  intro equalProfiles
  apply missesRight
  change model.accessProfile substance right sense
  rw [← equalProfiles]
  exact detectsLeft

/-- Selective access entails observational distinction in both orientations.
It does not mention the number of substances. -/
theorem separatelyAccessibleProfilesDistinct
    {substance : Substance} {left right : Quality}
    (separate : model.SeparatelyAccessible substance left right) :
    model.ObservationallyDistinct substance left right /\
      model.ObservationallyDistinct substance right left := by
  obtain ⟨leftSense, rightSense, leftSeen, rightMissed,
    rightSeen, leftMissed⟩ := separate
  exact ⟨model.profilesDistinctOfDetectionGap leftSeen rightMissed,
    model.profilesDistinctOfDetectionGap rightSeen leftMissed⟩

/-- Under the stated detection-soundness bridge, selective access to both
qualities supplies a shared bearer rather than forcing distinct bearers. -/
theorem coInhereOfSeparateAccess
    {substance : Substance} {left right : Quality}
    (separate : model.SeparatelyAccessible substance left right) :
    model.CoInhere substance left right := by
  obtain ⟨leftSense, rightSense, leftSeen, _, rightSeen, _⟩ := separate
  exact ⟨model.detectionSound leftSense substance left leftSeen,
    model.detectionSound rightSense substance right rightSeen⟩

/-! ## Typed projections to existing semantic APIs -/

/-- The inherence relation is directly reusable as an apoha feature profile;
sensory access remains outside that extensional feature inventory. -/
def toFeatureProfile :
    BuddhistComparativeLogic.ApohaFeatures.FeatureProfile Substance Quality :=
  model.hasQuality

/-- A one-quality requirement suitable for both `ApohaFeatures` and the
`WhiteHorse.SearchRequest` interface. -/
def qualityRequirement (quality : Quality) :
    BuddhistComparativeLogic.ApohaFeatures.Requirements Quality :=
  fun candidate => candidate = quality

/-- The class of substances possessing a specified quality, generated by the
existing component-class semantics. -/
def qualityClass (quality : Quality) : BuddhistComparativeLogic.Apoha.PredSet Substance :=
  BuddhistComparativeLogic.ApohaFeatures.componentClass model.toFeatureProfile
    (qualityRequirement quality)

theorem belongsQualityClassIff
    (substance : Substance) (quality : Quality) :
    model.qualityClass quality substance <->
      model.hasQuality substance quality := by
  constructor
  · intro belongs
    exact belongs quality rfl
  · intro hasQuality candidate required
    subst candidate
    exact hasQuality

/-- Package a one-quality requirement using the request type from the White
Horse audit.  The shared type does not identify the two historical texts. -/
def toSearchRequest (quality : Quality) :
    BuddhistComparativeLogic.WhiteHorse.SearchRequest Quality where
  requires := qualityRequirement quality

/-- Turn one substance's sense/quality incidence table into the observation
interface used by the `Sahopalambha` development.  A sense token registers
itself as a cognition; cross-category numerical identity is left false. -/
def toCoapprehensionModel (substance : Substance) :
    BuddhistComparativeLogic.Sahopalambha.Model Quality Sense Unit Sense where
  causallyProduces := fun quality sense =>
    model.detects sense substance quality
  imageSimilar := fun quality sense =>
    model.detects sense substance quality
  tokenTime := fun _ => ()
  registersObject := fun sense quality =>
    model.detects sense substance quality
  registersCognition := fun token cognition => token = cognition
  externallyCoupled := fun quality sense =>
    model.detects sense substance quality
  sameEntity := fun _ _ => False

end SensoryModel

/-! ## The finite hard/white stone -/

inductive Sense where
  | sight
  | touch
  deriving DecidableEq, Repr

inductive Quality where
  | white
  | hard
  deriving DecidableEq, Repr

inductive Substance where
  | stone
  deriving DecidableEq, Repr

open Sense Quality Substance

/-- One stone bears both qualities.  Sight selectively registers white and
touch selectively registers hard. -/
def stoneModel : SensoryModel Substance Quality Sense where
  hasQuality := fun _ _ => True
  detects
    | .sight, .stone, .white => True
    | .touch, .stone, .hard => True
    | _, _, _ => False
  detectionSound := by
    intro sense substance quality _
    trivial

theorem sight_white_touch_hard_access_pattern :
    stoneModel.detects .sight .stone .white /\
      ¬ stoneModel.detects .sight .stone .hard /\
      stoneModel.detects .touch .stone .hard /\
      ¬ stoneModel.detects .touch .stone .white := by
  exact ⟨trivial, id, trivial, id⟩

theorem hardWhiteSeparatelyAccessible :
    stoneModel.SeparatelyAccessible .stone .white .hard :=
  ⟨.sight, .touch,
    sight_white_touch_hard_access_pattern.1,
    sight_white_touch_hard_access_pattern.2.1,
    sight_white_touch_hard_access_pattern.2.2.1,
    sight_white_touch_hard_access_pattern.2.2.2⟩

/-- The requested distinctness result: white and hard have different sight
and touch profiles in the finite model. -/
theorem sight_white_touch_hard_profiles_are_distinct :
    stoneModel.ObservationallyDistinct .stone .white .hard /\
      stoneModel.ObservationallyDistinct .stone .hard .white :=
  stoneModel.separatelyAccessibleProfilesDistinct hardWhiteSeparatelyAccessible

theorem hard_and_white_coinhere_in_stone :
    stoneModel.CoInhere .stone .white .hard :=
  stoneModel.coInhereOfSeparateAccess hardWhiteSeparatelyAccessible

theorem stone_model_has_no_separate_bearers :
    ¬ stoneModel.SeparateBearers .white .hard := by
  rintro ⟨leftBearer, rightBearer, distinct, _, _⟩
  cases leftBearer
  cases rightBearer
  exact distinct rfl

/-- The inhabited finite countermodel: selective access and co-inherence hold,
while the conclusion that the qualities require distinct substances fails. -/
theorem sensory_separability_does_not_force_separate_substances :
    Nonempty Substance /\
      stoneModel.SeparatelyAccessible .stone .white .hard /\
      stoneModel.ObservationallyDistinct .stone .white .hard /\
      stoneModel.CoInhere .stone .white .hard /\
      ¬ stoneModel.SeparateBearers .white .hard :=
  ⟨⟨.stone⟩, hardWhiteSeparatelyAccessible,
    sight_white_touch_hard_profiles_are_distinct.1,
    hard_and_white_coinhere_in_stone,
    stone_model_has_no_separate_bearers⟩

/-- The concrete model refutes a universal promotion from sensory separation
to distinct bearers. -/
theorem universal_separation_to_bearers_bridge_fails :
    ¬ (forall substance left right,
      stoneModel.SeparatelyAccessible substance left right ->
        stoneModel.SeparateBearers left right) := by
  intro bridge
  exact stone_model_has_no_separate_bearers
    (bridge .stone .white .hard hardWhiteSeparatelyAccessible)

/-! ## Concrete reuse of ApohaFeatures and WhiteHorse -/

theorem stone_belongs_to_both_feature_classes :
    stoneModel.qualityClass .white .stone /\
      stoneModel.qualityClass .hard .stone := by
  constructor
  · exact (stoneModel.belongsQualityClassIff .stone .white).mpr trivial
  · exact (stoneModel.belongsQualityClassIff .stone .hard).mpr trivial

def whiteRequest : BuddhistComparativeLogic.WhiteHorse.SearchRequest Quality :=
  SensoryModel.toSearchRequest .white

def hardRequest : BuddhistComparativeLogic.WhiteHorse.SearchRequest Quality :=
  SensoryModel.toSearchRequest .hard

theorem hard_white_requests_are_distinct : whiteRequest ≠ hardRequest := by
  intro requestsEqual
  have requirementsEqual :=
    congrArg BuddhistComparativeLogic.WhiteHorse.SearchRequest.requires requestsEqual
  have atWhite := congrFun requirementsEqual Quality.white
  simp [whiteRequest, hardRequest, SensoryModel.toSearchRequest,
    SensoryModel.qualityRequirement] at atWhite

/-- The two distinct WhiteHorse-style requests generate the same extension in
the one-stone model.  Coextension therefore does not erase the typed access
or request distinction. -/
theorem coextensive_quality_classes_do_not_identify_requests :
    stoneModel.qualityClass .white = stoneModel.qualityClass .hard /\
      whiteRequest ≠ hardRequest := by
  constructor
  · funext substance
    apply propext
    cases substance
    constructor
    · intro _
      exact stone_belongs_to_both_feature_classes.2
    · intro _
      exact stone_belongs_to_both_feature_classes.1
  · exact hard_white_requests_are_distinct

/-! ## Concrete reuse of Sahopalambha -/

abbrev stoneObservation := stoneModel.toCoapprehensionModel .stone

theorem white_is_constantly_coapprehended_with_sight :
    stoneObservation.ConstantCoapprehension .white .sight := by
  intro token
  cases token <;>
    simp [stoneObservation, SensoryModel.toCoapprehensionModel, stoneModel]

theorem hard_is_constantly_coapprehended_with_touch :
    stoneObservation.ConstantCoapprehension .hard .touch := by
  intro token
  cases token <;>
    simp [stoneObservation, SensoryModel.toCoapprehensionModel, stoneModel]

/-- The existing co-apprehension interface recovers matching trace equality,
but its deliberately false cross-category identity relation does not identify
a quality with a sensory cognition. -/
theorem coapprehension_preserves_the_identity_boundary :
    stoneObservation.ObservationallyNonseparate .white .sight /\
      stoneObservation.ObservationallyNonseparate .hard .touch /\
      ¬ stoneObservation.NumericallyIdentical .white .sight /\
      ¬ stoneObservation.NumericallyIdentical .hard .touch := by
  exact ⟨
    BuddhistComparativeLogic.Sahopalambha.Model.trace_equality_of_constant_coapprehension
      white_is_constantly_coapprehended_with_sight,
    BuddhistComparativeLogic.Sahopalambha.Model.trace_equality_of_constant_coapprehension
      hard_is_constantly_coapprehended_with_touch,
    id, id⟩

end BuddhistComparativeLogic.HardWhite
