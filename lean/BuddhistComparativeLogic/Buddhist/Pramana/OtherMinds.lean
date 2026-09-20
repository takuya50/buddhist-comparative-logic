/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Dharmakirti

/-!
# Behaviour and the inference to another stream of cognition

This module gives a deliberately small reconstruction of one issue connecting
Dharmakīrti's argument for other streams of cognition with Ratnakīrti's
criticism.  An agent's behaviour is observable and its volition is the target
of inference.  The deductive argument therefore needs a pervasion from the
selected behaviour to volition; a calibrated first-person case does not by
itself supply that pervasion.

The finite accounts below have exactly the same observable behaviour while
disagreeing about another agent's volition.  They establish an
underdetermination result for this interface, not the historical conclusion
of either author and not the impossibility of defeasible or probabilistic
support for other minds.
-/

namespace BuddhistComparativeLogic.OtherMinds

universe u v

/-- A neutral interface separating publicly observable behaviour from the
volition that an other-mind inference seeks to establish. -/
structure StreamModel (Agent : Type u) (Action : Type v) where
  behaves : Agent → Action → Prop
  wills : Agent → Action → Prop

namespace StreamModel

variable {Agent : Type u} {Action : Type v}
    (M : StreamModel Agent Action)

/-- The minimal target established directly by the inference: an agent has at
least one volition.  This alone does not yet say that the agent is other. -/
def HasVolition (agent : Agent) : Prop :=
  ∃ action, M.wills agent action

/-- A minimal conventional other-stream proxy adds numerical distinction from
the designated self to the volition target. -/
def ConventionalOtherStream (self other : Agent) : Prop :=
  self ≠ other ∧ M.HasVolition other

/-- First-person calibration at one action records both observed performance
and the corresponding known volition.  It is local to the selected agent. -/
def SelfCalibration (self : Agent) (action : Action) : Prop :=
  M.behaves self action ∧ M.wills self action

/-- The pervasion required to infer the selected volition from behaviour. -/
def BehaviourLicense (action : Action) : Prop :=
  ∀ agent, M.behaves agent action → M.wills agent action

/-- The behaviour-to-volition argument represented by the existing
Dharmakīrti inference interface. -/
def inference (subject : Agent) (action : Action) :
    BuddhistComparativeLogic.Dharmakirti.Model Agent where
  paksa := subject
  reason := fun agent => M.behaves agent action
  sadhya := fun agent => M.wills agent action
  vyapti := M.BehaviourLicense action
  vyapti_iff := Iff.rfl

theorem inference_vyapti_iff (subject : Agent) (action : Action) :
    (M.inference subject action).vyapti ↔ M.BehaviourLicense action :=
  Iff.rfl

/-- Behaviour establishes the corresponding volition when the explicit
pervasion is supplied. -/
theorem volition_of_license {subject : Agent} {action : Action}
    (license : M.BehaviourLicense action)
    (observed : M.behaves subject action) :
    M.wills subject action :=
  (M.inference subject action).vyapti_sound license observed

/-- The same licensed observation witnesses the deliberately weak volition
target used in this module. -/
theorem has_volition_of_license {subject : Agent} {action : Action}
    (license : M.BehaviourLicense action)
    (observed : M.behaves subject action) :
    M.HasVolition subject :=
  ⟨action, M.volition_of_license license observed⟩

/-- Otherness is a separate premise: licensed behaviour supplies volition,
while distinction from the selected self must be established independently. -/
theorem other_stream_of_license {self other : Agent} {action : Action}
    (distinct : self ≠ other)
    (license : M.BehaviourLicense action)
    (observed : M.behaves other action) :
    M.ConventionalOtherStream self other :=
  ⟨distinct, M.has_volition_of_license license observed⟩

end StreamModel

/-! ## Observation-only classifiers -/

/-- Two accounts are observationally equivalent when their behaviour
predicates agree.  Volition is intentionally absent from this definition. -/
def ObservationEquivalent
    {Agent : Type u} {Action : Type v}
    (left right : StreamModel Agent Action) : Prop :=
  left.behaves = right.behaves

/-- A positive and negative account for the same other-mind target with
identical observable behaviour. -/
structure Defeater
    {Agent : Type u} {Action : Type v}
    (self other : Agent) where
  positive : StreamModel Agent Action
  negative : StreamModel Agent Action
  observationallyEquivalent : ObservationEquivalent positive negative
  positiveOther : positive.ConventionalOtherStream self other
  negativeOther : ¬ negative.ConventionalOtherStream self other

/-- No exact decision rule whose sole input is behaviour can classify all
stream models correctly when a defeating pair is available. -/
theorem no_exact_behaviour_classifier_of_defeater
    {Agent : Type u} {Action : Type v} {self other : Agent}
    (defeater : Defeater (Action := Action) self other) :
    ¬ ∃ classify : (Agent → Action → Prop) → Bool,
        ∀ M : StreamModel Agent Action,
          classify M.behaves = true ↔
            M.ConventionalOtherStream self other := by
  rcases defeater with
    ⟨positive, negative, equivalent, positiveOther, negativeOther⟩
  rintro ⟨classify, exactness⟩
  have positiveResult : classify positive.behaves = true :=
    (exactness positive).mpr positiveOther
  have negativeResult : classify negative.behaves = true := by
    rw [← equivalent]
    exact positiveResult
  exact negativeOther ((exactness negative).mp negativeResult)

/-! ## Finite rival accounts -/

inductive Person where
  | self
  | apparentOther
  deriving DecidableEq, Repr

inductive Signal where
  | gesture
  deriving DecidableEq, Repr

/-- Both agents behave and possess the corresponding volition. -/
def mindedAccount : StreamModel Person Signal where
  behaves _ _ := True
  wills _ _ := True

/-- The same observable behaviour is produced while only the first agent is
assigned a volition.  The name `automatonAccount` is descriptive metadata for
this finite countermodel, not a psychological thesis. -/
def automatonAccount : StreamModel Person Signal where
  behaves _ _ := True
  wills person _ := person = .self

theorem rival_accounts_observationally_equivalent :
    ObservationEquivalent mindedAccount automatonAccount :=
  rfl

theorem minded_other_exists :
    mindedAccount.ConventionalOtherStream .self .apparentOther := by
  exact ⟨by decide, ⟨.gesture, trivial⟩⟩

/-- The positive finite account supplies all inputs of the existing
Dharmakīrti-style subject inference and reaches the selected volition. -/
theorem minded_inference_is_nonvacuous :
    mindedAccount.BehaviourLicense .gesture ∧
      mindedAccount.behaves .apparentOther .gesture ∧
      (mindedAccount.inference .apparentOther .gesture).vyapti ∧
      mindedAccount.ConventionalOtherStream .self .apparentOther := by
  refine ⟨fun _ _ => trivial, trivial, fun _ _ => trivial, ?_⟩
  exact mindedAccount.other_stream_of_license (action := .gesture) (by decide)
    (fun _ _ => trivial) trivial

theorem automaton_other_absent :
    ¬ automatonAccount.ConventionalOtherStream .self .apparentOther := by
  rintro ⟨_distinct, action, volition⟩
  exact Person.noConfusion volition

def finiteDefeater :
    Defeater (Action := Signal) Person.self Person.apparentOther where
  positive := mindedAccount
  negative := automatonAccount
  observationallyEquivalent := rival_accounts_observationally_equivalent
  positiveOther := minded_other_exists
  negativeOther := automaton_other_absent

/-- The finite pair rules out a universal, exact observation-only classifier
for other minds at this interface. -/
theorem behaviour_does_not_exactly_classify_other_minds :
    ¬ ∃ classify : (Person → Signal → Prop) → Bool,
        ∀ M : StreamModel Person Signal,
          classify M.behaves = true ↔
            M.ConventionalOtherStream .self .apparentOther :=
  no_exact_behaviour_classifier_of_defeater finiteDefeater

/-- A first-person calibration and the very same behaviour in another agent
do not entail the other agent's volition. -/
theorem first_person_analogy_needs_pervasion :
    automatonAccount.SelfCalibration .self .gesture ∧
      automatonAccount.behaves .apparentOther .gesture ∧
      ¬ automatonAccount.wills .apparentOther .gesture ∧
      ¬ automatonAccount.BehaviourLicense .gesture := by
  refine ⟨⟨trivial, rfl⟩, trivial, ?_, ?_⟩
  · intro h
    exact Person.noConfusion h
  · intro license
    exact Person.noConfusion (license .apparentOther trivial)

/-- Conversely, absence of the selected public behaviour does not refute a
volition unless a further manifestation premise is supplied. -/
def silentMindAccount : StreamModel Person Signal where
  behaves person _ := person = .self
  wills _ _ := True

theorem unmanifest_volition_boundary :
    silentMindAccount.ConventionalOtherStream .self .apparentOther ∧
      ¬ silentMindAccount.behaves .apparentOther .gesture := by
  refine ⟨⟨by decide, ⟨.gesture, trivial⟩⟩, ?_⟩
  intro h
  exact Person.noConfusion h

/-! ## Conventional target and a stronger identity claim -/

/-- An additional relation can represent a stronger claim that two streams
are ultimately distinct.  It is deliberately independent of behaviour and
volition so that its extra proof obligation remains visible. -/
structure StandpointAccount (Agent : Type u) (Action : Type v)
    extends StreamModel Agent Action where
  conventionallyDistinct : Agent → Agent → Prop
  ultimatelyDistinct : Agent → Agent → Prop

namespace StandpointAccount

variable {Agent : Type u} {Action : Type v}
    (M : StandpointAccount Agent Action)

def ConventionalOtherMind (self other : Agent) : Prop :=
  M.conventionallyDistinct self other ∧
    M.toStreamModel.HasVolition other

def UltimateDistinctOther (self other : Agent) : Prop :=
  M.ConventionalOtherMind self other ∧ M.ultimatelyDistinct self other

/-- The licensed inference establishes the conventional target represented by
volition.  The stronger distinctness conjunct still requires its own premise. -/
theorem conventional_of_license {self other : Agent} {action : Action}
    (distinct : M.conventionallyDistinct self other)
    (license : M.toStreamModel.BehaviourLicense action)
    (observed : M.behaves other action) :
    M.ConventionalOtherMind self other :=
  ⟨distinct, M.toStreamModel.has_volition_of_license license observed⟩

end StandpointAccount

def nonDistinctAccount : StandpointAccount Person Signal where
  behaves _ _ := True
  wills _ _ := True
  conventionallyDistinct left right := left ≠ right
  ultimatelyDistinct _ _ := False

/-- Even a universally licensed behaviour-to-volition inference does not
manufacture the separately represented ultimate-distinctness premise. -/
theorem conventional_does_not_entail_ultimate_distinctness :
    nonDistinctAccount.behaves .apparentOther .gesture ∧
      nonDistinctAccount.toStreamModel.BehaviourLicense .gesture ∧
      nonDistinctAccount.ConventionalOtherMind .self .apparentOther ∧
      ¬ nonDistinctAccount.UltimateDistinctOther
        .self .apparentOther := by
  have license :
      nonDistinctAccount.toStreamModel.BehaviourLicense .gesture :=
    fun _ _ => trivial
  have observed :
      nonDistinctAccount.behaves .apparentOther .gesture :=
    trivial
  have conventional :
      nonDistinctAccount.ConventionalOtherMind .self .apparentOther :=
    nonDistinctAccount.conventional_of_license
      (by change Person.self ≠ Person.apparentOther; decide) license observed
  exact ⟨observed, license, conventional, fun ultimate => ultimate.2⟩

end BuddhistComparativeLogic.OtherMinds
