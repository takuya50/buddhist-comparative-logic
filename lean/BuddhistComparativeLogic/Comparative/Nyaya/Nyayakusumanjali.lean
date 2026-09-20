/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Nyaya.Nyaya
import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis

/-!
# A bounded maker-inference audit inspired by the Nyayakusumanjali

This module reconstructs one narrow proof pattern associated with Udayana's
`karyat` inference: effecthood is the reason, and the existence of an agent
who knows the relevant materials, wills the product, and makes it is the
thesis.  The reason reaches that thesis only through an explicit universal
maker-pervasion premise.  A single manufactured example is kept separate
from that premise.

This is not a formalization of the complete *Nyayakusumanjali* and not a proof
of God.  In particular, the interface-level conclusion is only that some
qualified maker exists for the selected object.  Uniqueness, knowledge of
every object in the finite domain, and existence at every represented moment
are stronger claims with independent obligations.  The finite models below
make all of these boundaries executable; they do not settle the historical
interpretation of `karyat` or Udayana's other arguments.

Source mapping (accessed 2026-09-19): the exact textual target is the received
*Nyāyakusumāñjali*, fifth *stabaka*, verse 5.1 and prose beginning
`kṣityādi kartṛpūrvakaṃ kāryatvāt` at GRETIL
(https://gretil.sub.uni-goettingen.de/gretil/1_sanskr/6_sastra/3_phil/nyaya/udnyku5u.htm).
That electronic text says that it is unproofread and does not name a critical
edition.  Ferenc Ruzsa, “Structure and Authorship of the Kusumāñjali,”
*Journal of Indian Philosophy* 50 (2022), 803–819, supplies peer-reviewed
orientation and cautions against assuming uniform authorship of verse and
prose.  The English descriptions and the predicates `Effect`,
`QualifiedMaker`, and `MakerPervasion` are project-authored paraphrases; they
do not translate the passage or identify the transmitted verse uniquely with
Udayana's own wording.
-/

namespace BuddhistComparativeLogic.Nyayakusumanjali

open BuddhistComparativeLogic.Hetucakra

universe u v w

/-! ## Typed maker inference -/

/-- Objects, agents, and moments have different types.  The four predicates
used in the maker thesis remain independent data; effecthood alone contains
none of them. -/
structure MakerModel (Object : Type u) (Agent : Type v) (Moment : Type w) where
  Effect : Object -> Prop
  KnowsMaterials : Agent -> Object -> Prop
  Wills : Agent -> Object -> Prop
  Makes : Agent -> Object -> Prop
  ExistsAt : Agent -> Moment -> Prop

namespace MakerModel

variable {Object : Type u} {Agent : Type v} {Moment : Type w}
    (M : MakerModel Object Agent Moment)

/-- The deliberately modest agent condition used by the thesis. -/
def QualifiedMaker (agent : Agent) (object : Object) : Prop :=
  M.KnowsMaterials agent object /\
    M.Wills agent object /\ M.Makes agent object

/-- The thesis of the bounded inference: at least one qualified maker exists
for this object. -/
def HasIntelligentMaker (object : Object) : Prop :=
  exists agent, M.QualifiedMaker agent object

/-- The universal bridge required to move from effecthood to the maker
thesis.  It is an input, not a consequence of the name `Effect`. -/
def MakerPervasion : Prop :=
  forall object, M.Effect object -> M.HasIntelligentMaker object

/-- The maker inference as the repository's common reason/thesis object. -/
def inference (subject : Object) : Anumana Object where
  paksa := subject
  reason := M.Effect
  sadhya := M.HasIntelligentMaker

theorem inference_pervasion_iff (subject : Object) :
    BuddhistComparativeLogic.InferenceScope.Pervasion (M.inference subject) <->
      M.MakerPervasion :=
  Iff.rfl

/-- An interface-local proxy for omniscience.  It quantifies only over
knowledge of the materials of every represented object, not all truths. -/
def KnowsMaterialsOfEveryObject (agent : Agent) : Prop :=
  forall object, M.KnowsMaterials agent object

/-- Eternity is likewise bounded to every moment in the supplied type. -/
def ExistsAtEveryMoment (agent : Agent) : Prop :=
  forall moment, M.ExistsAt agent moment

/-- Uniqueness of the qualified maker for one selected object. -/
def UniqueMakerAt (object : Object) : Prop :=
  forall left right,
    M.QualifiedMaker left object -> M.QualifiedMaker right object ->
      left = right

/-- A stronger conclusion often liable to be read into the weak existential.
All three extra conjuncts are visible here. -/
def StrongMakerClaim (object : Object) : Prop :=
  exists agent,
    M.QualifiedMaker agent object /\
      (forall other, M.QualifiedMaker other object -> other = agent) /\
      M.KnowsMaterialsOfEveryObject agent /\
      M.ExistsAtEveryMoment agent

end MakerModel

/-- Exactly the two premises needed for the subject conclusion. -/
structure MakerCertificate
    {Object : Type u} {Agent : Type v} {Moment : Type w}
    (M : MakerModel Object Agent Moment) (subject : Object) : Prop where
  subjectEffect : M.Effect subject
  makerPervasion : M.MakerPervasion

namespace MakerCertificate

variable {Object : Type u} {Agent : Type v} {Moment : Type w}
    {M : MakerModel Object Agent Moment} {subject : Object}

/-- Typed export to the existing Nyaya semantic certificate. -/
theorem toNyayaSemanticProof (certificate : MakerCertificate M subject) :
    BuddhistComparativeLogic.Nyaya.SemanticProof (M.inference subject) where
  subjectReason := certificate.subjectEffect
  pervasion := certificate.makerPervasion

theorem sound (certificate : MakerCertificate M subject) :
    M.HasIntelligentMaker subject :=
  certificate.toNyayaSemanticProof.sound

end MakerCertificate

/-- Package the same inference for the shared pramana certificate API. -/
def pramanaModel
    {Object : Type u} {Agent : Type v} {Moment : Type w}
    (M : MakerModel Object Agent Moment) (subject : Object) :
    BuddhistComparativeLogic.Dharmakirti.Model Object where
  toAnumana := M.inference subject
  vyapti := M.MakerPervasion
  vyapti_iff := Iff.rfl

/-- Typed export to the common deductive certificate.  This adapter does not
identify Udayana's argument with a Buddhist theory of pervasion. -/
theorem MakerCertificate.toDeductiveCertificate
    {Object : Type u} {Agent : Type v} {Moment : Type w}
    {M : MakerModel Object Agent Moment} {subject : Object}
    (certificate : MakerCertificate M subject) :
    BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (pramanaModel M subject) where
  subjectReason := certificate.subjectEffect
  pervasion := certificate.makerPervasion

/-! ## A nonvacuous manufactured-object model -/

inductive Artifact where
  | pot
  | cloth
  | stone
  deriving DecidableEq, Repr

inductive Artisan where
  | potter
  | weaver
  deriving DecidableEq, Repr

inductive WorkshopMoment where
  | work
  | later
  deriving DecidableEq, Repr

open Artifact Artisan WorkshopMoment

/-- Two effects have different qualified makers; the stone is a genuine
negative case.  Neither artisan exists at the later represented moment. -/
def workshop : MakerModel Artifact Artisan WorkshopMoment where
  Effect object := object = .pot \/ object = .cloth
  KnowsMaterials agent object :=
    (agent = .potter /\ object = .pot) \/
      (agent = .weaver /\ object = .cloth)
  Wills agent object :=
    (agent = .potter /\ object = .pot) \/
      (agent = .weaver /\ object = .cloth)
  Makes agent object :=
    (agent = .potter /\ object = .pot) \/
      (agent = .weaver /\ object = .cloth)
  ExistsAt _ moment := moment = .work

theorem workshop_maker_pervasion : workshop.MakerPervasion := by
  intro object effect
  rcases effect with rfl | rfl
  · exact ⟨.potter, Or.inl ⟨rfl, rfl⟩,
      Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨.weaver, Or.inr ⟨rfl, rfl⟩,
      Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem potCertificate : MakerCertificate workshop .pot where
  subjectEffect := Or.inl rfl
  makerPervasion := workshop_maker_pervasion

theorem pot_has_qualified_maker :
    workshop.HasIntelligentMaker .pot :=
  potCertificate.sound

/-- The positive comparison example is separate from the subject and from
the universal pervasion field. -/
def clothExample :
    BuddhistComparativeLogic.Nyaya.PositiveExample (workshop.inference .pot) where
  witness := .cloth
  distinct := by decide
  hasReason := Or.inr rfl
  hasThesis := ⟨.weaver, Or.inr ⟨rfl, rfl⟩,
    Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem workshop_positive_model_is_nonvacuous :
    workshop.Effect .pot /\
      workshop.Effect .cloth /\
      (¬ workshop.Effect .stone) /\
      workshop.HasIntelligentMaker .pot /\
      workshop.HasIntelligentMaker .cloth /\
      BuddhistComparativeLogic.InferenceScope.Pervasion (workshop.inference .pot) := by
  exact ⟨Or.inl rfl, Or.inr rfl, by
      intro effect
      rcases effect with stoneIsPot | stoneIsCloth
      · exact Artifact.noConfusion stoneIsPot
      · exact Artifact.noConfusion stoneIsCloth,
    pot_has_qualified_maker, clothExample.hasThesis,
    workshop_maker_pervasion⟩

/-- The very same certificate is accepted by both existing proof APIs. -/
theorem workshop_api_bridges_reach_the_same_subject :
    (workshop.inference .pot).sadhya .pot /\
      (pramanaModel workshop .pot).sadhya .pot :=
  ⟨potCertificate.toNyayaSemanticProof.sound,
    BuddhistComparativeLogic.PramanaSynthesis.deductive_sound
      potCertificate.toDeductiveCertificate⟩

/-- The potter is the only qualified maker of the pot in this model. -/
theorem workshop_pot_has_unique_maker :
    workshop.UniqueMakerAt .pot := by
  intro left right leftMaker rightMaker
  rcases leftMaker with ⟨leftKnows, _leftWills, _leftMakes⟩
  rcases rightMaker with ⟨rightKnows, _rightWills, _rightMakes⟩
  rcases leftKnows with ⟨rfl, _⟩ | ⟨leftWeaver, cloth⟩
  · rcases rightKnows with ⟨rfl, _⟩ | ⟨rightWeaver, cloth⟩
    · rfl
    · cases cloth
  · cases cloth

/-- Even the unique local maker lacks the two stronger bounded properties.
Thus a successful single-maker inference does not derive either one. -/
theorem one_maker_does_not_supply_omniscience_or_eternity :
    workshop.HasIntelligentMaker .pot /\
      workshop.UniqueMakerAt .pot /\
      (¬ workshop.KnowsMaterialsOfEveryObject .potter) /\
      (¬ workshop.ExistsAtEveryMoment .potter) /\
      (¬ workshop.StrongMakerClaim .pot) := by
  refine ⟨pot_has_qualified_maker, workshop_pot_has_unique_maker, ?_, ?_, ?_⟩
  · intro allKnowledge
    have stoneKnowledge := allKnowledge .stone
    simp [workshop] at stoneKnowledge
  · intro allMoments
    have laterExistence := allMoments .later
    simp [workshop] at laterExistence
  · rintro ⟨agent, maker, _unique, allKnowledge, _eternal⟩
    rcases maker with ⟨knows, _wills, _makes⟩
    rcases knows with ⟨rfl, _⟩ | ⟨potterIsWeaver, clothIsPot⟩
    · have stoneKnowledge := allKnowledge .stone
      simp [workshop] at stoneKnowledge
    · cases clothIsPot

/-! ## Natural effect and finite-sample countermodel -/

inductive MixedObject where
  | pot
  | sprout
  deriving DecidableEq, Repr

inductive MixedAgent where
  | potter
  deriving DecidableEq, Repr

/-- Both objects count as effects, but only the pot has a qualified maker. -/
def mixedWorld : MakerModel MixedObject MixedAgent Unit where
  Effect _ := True
  KnowsMaterials _ object := object = .pot
  Wills _ object := object = .pot
  Makes _ object := object = .pot
  ExistsAt _ _ := True

theorem natural_effect_without_intelligent_maker :
    mixedWorld.Effect .sprout /\
      ¬ mixedWorld.HasIntelligentMaker .sprout := by
  constructor
  · trivial
  · rintro ⟨agent, knows, _wills, _makes⟩
    cases agent
    exact MixedObject.noConfusion knows

/-- The manufactured pot is an actual positive comparison example for the
sprout-subject inference. -/
def mixedPotExample :
    BuddhistComparativeLogic.Nyaya.PositiveExample (mixedWorld.inference .sprout) where
  witness := .pot
  distinct := by decide
  hasReason := trivial
  hasThesis := ⟨.potter, rfl, rfl, rfl⟩

/-- One positive artifact leaves the global bridge false because the
unobserved style of effect represented by the sprout is a countercase. -/
theorem positive_artifact_does_not_establish_global_pervasion :
    mixedWorld.Effect .pot /\
      mixedWorld.HasIntelligentMaker .pot /\
      mixedWorld.Effect .sprout /\
      (¬ mixedWorld.HasIntelligentMaker .sprout) /\
      (¬ mixedWorld.MakerPervasion) := by
  refine ⟨mixedPotExample.hasReason, mixedPotExample.hasThesis,
    trivial, natural_effect_without_intelligent_maker.2, ?_⟩
  intro pervasion
  exact natural_effect_without_intelligent_maker.2
    (pervasion .sprout trivial)

/-! ## Multiple makers do not establish the stronger conclusion -/

inductive JointAgent where
  | first
  | second
  deriving DecidableEq, Repr

inductive JointObject where
  | vessel
  | unstudiedStone
  deriving DecidableEq, Repr

inductive JointMoment where
  | making
  | after
  deriving DecidableEq, Repr

/-- Both agents qualify for the vessel; neither knows the second object or
exists at the later moment. -/
def jointWorkshop : MakerModel JointObject JointAgent JointMoment where
  Effect object := object = .vessel
  KnowsMaterials _ object := object = .vessel
  Wills _ object := object = .vessel
  Makes _ object := object = .vessel
  ExistsAt _ moment := moment = .making

theorem joint_vessel_has_two_distinct_makers :
    jointWorkshop.QualifiedMaker .first .vessel /\
      jointWorkshop.QualifiedMaker .second .vessel /\
      (.first : JointAgent) ≠ .second := by
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, by decide⟩

theorem multiple_makers_do_not_supply_uniqueness_omniscience_or_eternity :
    jointWorkshop.HasIntelligentMaker .vessel /\
      (¬ jointWorkshop.UniqueMakerAt .vessel) /\
      (forall agent, ¬ jointWorkshop.KnowsMaterialsOfEveryObject agent) /\
      (forall agent, ¬ jointWorkshop.ExistsAtEveryMoment agent) /\
      (¬ jointWorkshop.StrongMakerClaim .vessel) := by
  refine ⟨⟨.first, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro unique
    have equality := unique .first .second
      joint_vessel_has_two_distinct_makers.1
      joint_vessel_has_two_distinct_makers.2.1
    exact joint_vessel_has_two_distinct_makers.2.2 equality
  · intro agent allKnowledge
    have stoneKnowledge := allKnowledge .unstudiedStone
    simp [jointWorkshop] at stoneKnowledge
  · intro agent allMoments
    have laterExistence := allMoments .after
    simp [jointWorkshop] at laterExistence
  · rintro ⟨agent, maker, unique, _allKnowledge, _eternal⟩
    cases agent with
    | first =>
        have equality := unique .second
          joint_vessel_has_two_distinct_makers.2.1
        exact JointAgent.noConfusion equality
    | second =>
        have equality := unique .first
          joint_vessel_has_two_distinct_makers.1
        exact JointAgent.noConfusion equality

end BuddhistComparativeLogic.Nyayakusumanjali
