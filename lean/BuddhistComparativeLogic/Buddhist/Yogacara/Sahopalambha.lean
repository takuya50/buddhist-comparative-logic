/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Yogacara.Alambanapariksa
import BuddhistComparativeLogic.Buddhist.Yogacara.VimsatikaModels
import BuddhistComparativeLogic.Buddhist.Pramana.Pramanasamuccaya

/-!
# Constant co-apprehension and the scope of non-difference

This module gives a restrained reconstruction of the argument commonly called
`sahopalambhaniyama`.  Objects, cognitions, observation tokens and times have
different types.  Tokenwise co-apprehension first yields only equality of
observable traces and of their time profiles.  Numerical identity is a
separate primitive relation on a tagged sum and follows only from an explicit
identity-from-extension bridge.

An external coupling can explain why two traces coincide without identifying
their bearers.  A finite model below therefore has two differently tagged
elements which occur together in every observation while numerical identity
fails.  A second model shows that one direction of tokenwise accompaniment
does not supply the converse or identity.

The word `abheda` in the historical literature admits readings weaker than
numerical identity, including denial of an independently presented difference
and non-separation within awareness.  The predicates below keep these readings
apart rather than selecting one interpretation by definition.
-/

namespace BuddhistComparativeLogic.Sahopalambha

universe u v w z

/-- A tagged carrier on which cross-category identity claims can be stated.
The constructors do not themselves identify an object with a cognition. -/
inductive Phenomenon (Object : Type u) (Cognition : Type v) where
  | object : Object -> Phenomenon Object Cognition
  | cognition : Cognition -> Phenomenon Object Cognition

/-- An episodic observation model.  The first two fields admit the existing
two-condition intentional-object analysis; the remaining fields distinguish
observation, coupling and numerical identity. -/
structure Model (Object : Type u) (Cognition : Type v)
    (Time : Type w) (Token : Type z) where
  causallyProduces : Object -> Cognition -> Prop
  imageSimilar : Object -> Cognition -> Prop
  tokenTime : Token -> Time
  registersObject : Token -> Object -> Prop
  registersCognition : Token -> Cognition -> Prop
  externallyCoupled : Object -> Cognition -> Prop
  sameEntity : Phenomenon Object Cognition ->
    Phenomenon Object Cognition -> Prop

namespace Model

variable {Object : Type u} {Cognition : Type v}
  {Time : Type w} {Token : Type z}

/-- Projection to the two-condition object interface used by the
`Alambanapariksa` development. -/
def toAlambanaModel (model : Model Object Cognition Time Token) :
    BuddhistComparativeLogic.Alambanapariksa.Model Object Cognition where
  causallyProduces := model.causallyProduces
  imageSimilar := model.imageSimilar

/-- The tokens in which a particular object is registered. -/
def objectTrace (model : Model Object Cognition Time Token)
    (object : Object) : Token -> Prop :=
  fun token => model.registersObject token object

/-- The tokens in which a particular cognition is registered. -/
def cognitionTrace (model : Model Object Cognition Time Token)
    (cognition : Cognition) : Token -> Prop :=
  fun token => model.registersCognition token cognition

/-- Joint registration in one observation token at one time. -/
def JointlyApprehendedAt (model : Model Object Cognition Time Token)
    (object : Object) (cognition : Cognition) (time : Time) : Prop :=
  exists token, model.tokenTime token = time /\
    model.registersObject token object /\
    model.registersCognition token cognition

/-- The object is registered in at least one token at this time. -/
def ObjectObservedAt (model : Model Object Cognition Time Token)
    (object : Object) (time : Time) : Prop :=
  exists token, model.tokenTime token = time /\
    model.registersObject token object

/-- The cognition is registered in at least one token at this time. -/
def CognitionObservedAt (model : Model Object Cognition Time Token)
    (cognition : Cognition) (time : Time) : Prop :=
  exists token, model.tokenTime token = time /\
    model.registersCognition token cognition

/-- The minimal tokenwise reconstruction of constant co-apprehension.  It is
pointwise accompaniment, not an identity assertion. -/
def ConstantCoapprehension (model : Model Object Cognition Time Token)
    (object : Object) (cognition : Cognition) : Prop :=
  forall token, model.registersObject token object <->
    model.registersCognition token cognition

/-- Observational non-separation is extensional equality of token traces. -/
def ObservationallyNonseparate
    (model : Model Object Cognition Time Token)
    (object : Object) (cognition : Cognition) : Prop :=
  model.objectTrace object = model.cognitionTrace cognition

/-- Numerical identity is deliberately delegated to the model's primitive
cross-category identity relation. -/
def NumericallyIdentical (model : Model Object Cognition Time Token)
    (object : Object) (cognition : Cognition) : Prop :=
  model.sameEntity (.object object) (.cognition cognition)

/-- Constant co-apprehension entails the trace equality that the observation
interface can express. -/
theorem trace_equality_of_constant_coapprehension
    {model : Model Object Cognition Time Token} {object : Object}
    {cognition : Cognition}
    (coapprehended : model.ConstantCoapprehension object cognition) :
    model.ObservationallyNonseparate object cognition := by
  funext token
  apply propext
  exact coapprehended token

/-- The same premise entails equality of time-indexed observation profiles.
This remains an extensional conclusion about appearances. -/
theorem time_profile_of_constant_coapprehension
    {model : Model Object Cognition Time Token} {object : Object}
    {cognition : Cognition}
    (coapprehended : model.ConstantCoapprehension object cognition) :
    forall time,
      model.ObjectObservedAt object time <->
        model.CognitionObservedAt cognition time := by
  intro time
  constructor
  · rintro ⟨token, tokenTime, observed⟩
    exact ⟨token, tokenTime, (coapprehended token).mp observed⟩
  · rintro ⟨token, tokenTime, observed⟩
    exact ⟨token, tokenTime, (coapprehended token).mpr observed⟩

/-- The forward half of accompaniment, recorded separately for the second
finite countermodel. -/
def ObjectImpliesCognition (model : Model Object Cognition Time Token)
    (object : Object) (cognition : Cognition) : Prop :=
  forall token, model.registersObject token object ->
    model.registersCognition token cognition

/-- The reverse half of accompaniment. -/
def CognitionImpliesObject (model : Model Object Cognition Time Token)
    (object : Object) (cognition : Cognition) : Prop :=
  forall token, model.registersCognition token cognition ->
    model.registersObject token object

/-- A bridge saying that an admitted external coupling explains the complete
co-apprehension pattern.  The bridge still has no identity conclusion. -/
structure CouplingTracksObservations
    (model : Model Object Cognition Time Token) : Prop where
  tracks : forall object cognition,
    model.externallyCoupled object cognition ->
      model.ConstantCoapprehension object cognition

/-- The disputed extensional-to-identity principle.  Keeping it in a separate
record prevents trace equality from becoming numerical identity by reduction. -/
structure IdentityFromExtension
    (model : Model Object Cognition Time Token) : Prop where
  identifies : forall object cognition,
    model.ObservationallyNonseparate object cognition ->
      model.NumericallyIdentical object cognition

/-- The strong identity conclusion follows for an explicitly coupled pair
when both the coupling-to-observation bridge and the extensional identity
principle are supplied. -/
theorem numerical_identity_of_explicit_bridges
    {model : Model Object Cognition Time Token}
    (couplingBridge : CouplingTracksObservations model)
    (identityBridge : IdentityFromExtension model)
    {object : Object} {cognition : Cognition}
    (coupled : model.externallyCoupled object cognition) :
    model.NumericallyIdentical object cognition :=
  identityBridge.identifies object cognition
    (trace_equality_of_constant_coapprehension
      (couplingBridge.tracks object cognition coupled))

/-- Co-apprehension can accompany the existing causal and similarity
conditions.  The result is exactly the older two-condition `IsAlambana`
certificate together with the joint episode, with no identity conclusion. -/
theorem jointly_apprehended_alambana_of_object_conditions
    {model : Model Object Cognition Time Token}
    {object : Object} {cognition : Cognition} {time : Time}
    (joint : model.JointlyApprehendedAt object cognition time)
    (cause : model.causallyProduces object cognition)
    (similarity : model.imageSimilar object cognition) :
    model.JointlyApprehendedAt object cognition time /\
      model.toAlambanaModel.IsAlambana object cognition :=
  ⟨joint,
    BuddhistComparativeLogic.Alambanapariksa.Model.alambana_of_cause_and_similarity
      cause similarity⟩

/-- Project joint episodes to an object-indexed appearance account.  The
subject position is occupied by a cognition and the location is trivial; the
object index remains independent of the observation token. -/
def toObjectIndexedAccount (model : Model Object Cognition Time Token) :
    BuddhistComparativeLogic.VimsatikaModels.ObjectIndexedAccount
      Cognition Unit Time Object where
  presents cognition object _ time :=
    model.JointlyApprehendedAt object cognition time
  acts cognition object _ time :=
    model.causallyProduces object cognition /\
      model.JointlyApprehendedAt object cognition time

theorem indexed_appearance_iff_joint_episode
    (model : Model Object Cognition Time Token)
    (cognition : Cognition) (time : Time) :
    model.toObjectIndexedAccount.observations.appears cognition () time <->
      exists object, model.JointlyApprehendedAt object cognition time :=
  Iff.rfl

/-- Duplicating the object indices of the joint-episode projection leaves the
generated observations unchanged, reusing the Viṃśatikā comparison theorem. -/
theorem duplicate_indices_preserve_joint_observations
    (model : Model Object Cognition Time Token) :
    BuddhistComparativeLogic.VimsatikaModels.observationEquivalent
      model.toObjectIndexedAccount.observations
      model.toObjectIndexedAccount.duplicate.observations :=
  BuddhistComparativeLogic.VimsatikaModels.duplicate_is_observation_equivalent
    model.toObjectIndexedAccount

/-- An observed episode packages the witness needed to feed the existing
perception-evidence interface. -/
structure ObservedEpisode (model : Model Object Cognition Time Token) where
  object : Object
  cognition : Cognition
  time : Time
  joint : model.JointlyApprehendedAt object cognition time

/-- The perceptual datum records cognition and time; nonconceptuality remains
an explicitly supplied predicate, as in the Pramāṇasamuccaya interface. -/
def episodePerception (model : Model Object Cognition Time Token)
    (nonconceptual : Cognition -> Prop) :
    BuddhistComparativeLogic.Pramanasamuccaya.PerceptionModel
      (ObservedEpisode model) (Cognition × Time) where
  appearance episode := (episode.cognition, episode.time)
  nonconceptual datum := nonconceptual datum.1

def episodeEvidence {model : Model Object Cognition Time Token}
    (nonconceptual : Cognition -> Prop) (episode : ObservedEpisode model)
    (isNonconceptual : nonconceptual episode.cognition) :
    BuddhistComparativeLogic.Pramanasamuccaya.PerceptualEvidence
      (episodePerception model nonconceptual) episode where
  datum := (episode.cognition, episode.time)
  presented := rfl
  nonconceptual := isNonconceptual

/-- The imported perceptual-evidence theorem applies to the joint episode,
without converting nonconceptual presentation into numerical identity. -/
theorem episode_appearance_is_nonconceptual
    {model : Model Object Cognition Time Token}
    (nonconceptual : Cognition -> Prop) (episode : ObservedEpisode model)
    (isNonconceptual : nonconceptual episode.cognition) :
    (episodePerception model nonconceptual).nonconceptual
      ((episodePerception model nonconceptual).appearance episode) :=
  (episodeEvidence nonconceptual episode isNonconceptual).appearance_is_nonconceptual

end Model

/-! ## Finite countermodel: complete co-occurrence without identity -/

inductive CoupledObject where
  | bluePatch
  deriving DecidableEq, Repr

inductive CoupledCognition where
  | visualAwareness
  deriving DecidableEq, Repr

inductive Moment where
  | first
  | second
  deriving DecidableEq, Repr

inductive Observation where
  | firstEpisode
  | secondEpisode
  deriving DecidableEq, Repr

def coupledModel : Model CoupledObject CoupledCognition Moment Observation where
  causallyProduces _ _ := True
  imageSimilar _ _ := True
  tokenTime
    | .firstEpisode => .first
    | .secondEpisode => .second
  registersObject _ _ := True
  registersCognition _ _ := True
  externallyCoupled _ _ := True
  sameEntity := fun left right => left = right

theorem coupled_at_every_moment :
    forall time, coupledModel.JointlyApprehendedAt
      .bluePatch .visualAwareness time := by
  intro time
  cases time with
  | first => exact ⟨.firstEpisode, rfl, trivial, trivial⟩
  | second => exact ⟨.secondEpisode, rfl, trivial, trivial⟩

theorem coupled_constant_coapprehension :
    coupledModel.ConstantCoapprehension .bluePatch .visualAwareness := by
  intro token
  exact ⟨fun _ => trivial, fun _ => trivial⟩

theorem coupled_trace_nonseparation :
    coupledModel.ObservationallyNonseparate .bluePatch .visualAwareness :=
  Model.trace_equality_of_constant_coapprehension
    coupled_constant_coapprehension

theorem coupled_tracks_observations :
    Model.CouplingTracksObservations coupledModel where
  tracks := by
    intro object cognition _ token
    cases object
    cases cognition
    exact ⟨fun _ => trivial, fun _ => trivial⟩

theorem coupled_elements_are_not_numerically_identical :
    ¬ coupledModel.NumericallyIdentical .bluePatch .visualAwareness := by
  intro identity
  cases identity

theorem complete_coapprehension_does_not_force_identity :
    coupledModel.externallyCoupled .bluePatch .visualAwareness /\
      coupledModel.ConstantCoapprehension .bluePatch .visualAwareness /\
      coupledModel.ObservationallyNonseparate .bluePatch .visualAwareness /\
      ¬ coupledModel.NumericallyIdentical .bluePatch .visualAwareness :=
  ⟨trivial, coupled_constant_coapprehension, coupled_trace_nonseparation,
    coupled_elements_are_not_numerically_identical⟩

theorem coupled_model_has_no_identity_from_extension_bridge :
    ¬ Model.IdentityFromExtension coupledModel := by
  intro bridge
  exact coupled_elements_are_not_numerically_identical
    (bridge.identifies .bluePatch .visualAwareness
      coupled_trace_nonseparation)

theorem coapprehended_alambana_still_lacks_identity :
    coupledModel.toAlambanaModel.IsAlambana
        .bluePatch .visualAwareness /\
      ¬ coupledModel.NumericallyIdentical .bluePatch .visualAwareness := by
  exact ⟨BuddhistComparativeLogic.Alambanapariksa.Model.alambana_of_cause_and_similarity
      trivial trivial,
    coupled_elements_are_not_numerically_identical⟩

/-! ## Finite countermodel: one direction is not the biconditional -/

inductive AsymmetricToken where
  | shared
  | cognitionOnly
  deriving DecidableEq, Repr

def oneWayModel : Model Unit Unit Unit AsymmetricToken where
  causallyProduces _ _ := True
  imageSimilar _ _ := True
  tokenTime _ := ()
  registersObject token _ := token = .shared
  registersCognition _ _ := True
  externallyCoupled _ _ := False
  sameEntity := fun left right => left = right

theorem one_way_object_to_cognition :
    oneWayModel.ObjectImpliesCognition () () := by
  intro token _
  trivial

theorem converse_accompaniment_fails :
    ¬ oneWayModel.CognitionImpliesObject () () := by
  intro converse
  have registered : oneWayModel.registersObject .cognitionOnly () :=
    converse .cognitionOnly trivial
  change AsymmetricToken.cognitionOnly = .shared at registered
  cases registered

theorem one_direction_does_not_force_biconditional_or_identity :
    oneWayModel.ObjectImpliesCognition () () /\
      ¬ oneWayModel.CognitionImpliesObject () () /\
      ¬ oneWayModel.ConstantCoapprehension () () /\
      ¬ oneWayModel.NumericallyIdentical () () := by
  refine ⟨one_way_object_to_cognition, converse_accompaniment_fails, ?_, ?_⟩
  · intro bothDirections
    exact converse_accompaniment_fails
      (fun token cognitionObserved =>
        (bothDirections token).mpr cognitionObserved)
  · intro identity
    cases identity

end BuddhistComparativeLogic.Sahopalambha
