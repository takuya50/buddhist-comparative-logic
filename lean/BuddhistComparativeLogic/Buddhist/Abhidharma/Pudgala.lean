/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.Dharma

/-!
# Aggregate streams and the person

This module gives a deliberately scoped reconstruction inspired by the
discussion of the person in chapter IX of Vasubandhu's
*Abhidharmakosabhasya*.  The mathematical target is narrow: it distinguishes
a conventional designation over a time-indexed stream of the five aggregates
from a putative separate substantial person, and it records exactly which
dependence and change premises exclude an immutable, causally active extra
person.

The source text is available through
<https://gretil.sub.uni-goettingen.de/gretil/corpustei/transformations/html/sa_vasubandhu-abhidharmakozabhASya.htm>;
background and the interpretive setting are surveyed at
<https://plato.stanford.edu/entries/vasubandhu/> and
<https://iep.utm.edu/pudgalavada-buddhist-philosophy/>.

This is not asserted to be a literal translation of Vasubandhu or of a
Pudgalavadin position.  In particular, the exclusion theorem does not erase
conventional persons, and the countermodels expose premises that a historical
argument would still have to defend.
-/

namespace BuddhistComparativeLogic.Pudgala

/-! ## A five-aggregate stream -/

/-- A history of the five aggregate dimensions.  `follows` is kept separate
from the Boolean aggregate profile, so temporal succession is not built into
mere difference of profiles. -/
structure AggregateStream (T : Type u) where
  present : T -> Skandha -> Bool
  follows : T -> T -> Prop

namespace AggregateStream

variable {T : Type u} (stream : AggregateStream T)

/-- At least one aggregate dimension differs between two times. -/
def Changes (t t' : T) : Prop :=
  exists aggregate, stream.present t aggregate ≠ stream.present t' aggregate

/-- A directed succession whose aggregate profile changes. -/
def ChangingStep (t t' : T) : Prop :=
  stream.follows t t' /\ stream.Changes t t'

theorem changingStep_changes {t t' : T}
    (step : stream.ChangingStep t t') : stream.Changes t t' :=
  step.2

end AggregateStream

/-! ## Conventional designation and an extra substantial-person candidate -/

/-- The data distinguish persons, aggregate dimensions, times, and the state
used to track a person's causal profile.  None of the four types is identified
with another by construction. -/
structure Model (Person : Type u) (T : Type v) (State : Type w) where
  stream : AggregateStream T
  designatedAt : Person -> T -> Prop
  substantial : Person -> Prop
  separate : Person -> Prop
  causalSupport : Person -> Skandha -> Prop
  conceptualSupport : Person -> Skandha -> Prop
  actsAt : Person -> T -> Prop
  profileAt : Person -> T -> State

namespace Model

variable {Person : Type u} {T : Type v} {State : Type w}
    (model : Model Person T State)

/-- A conventional person is designated throughout the admitted history.
This definition does not assert a further substance behind that history. -/
def ConventionallyDesignated (person : Person) : Prop :=
  forall time, model.designatedAt person time

/-- Persistence at the conventional level is repeated designation at two
times, rather than equality of an underlying stage or substance. -/
def PersistsAsDesignation (person : Person) (first second : T) : Prop :=
  model.designatedAt person first /\ model.designatedAt person second

theorem conventionally_designated_persists
    {person : Person} (designated : model.ConventionallyDesignated person)
    (first second : T) :
    model.PersistsAsDesignation person first second :=
  ⟨designated first, designated second⟩

def CausallyDependent (person : Person) : Prop :=
  exists aggregate, model.causalSupport person aggregate

def ConceptuallyDependent (person : Person) : Prop :=
  exists aggregate, model.conceptualSupport person aggregate

/-- Untyped talk of dependence forgets whether the support was causal or
conceptual.  The first countermodel below shows why this union alone is too
weak for an exclusion argument. -/
def DependsOn (person : Person) (aggregate : Skandha) : Prop :=
  model.causalSupport person aggregate \/
    model.conceptualSupport person aggregate

def CausallyActive (person : Person) : Prop :=
  exists time, model.actsAt person time

/-- Immutability is constancy of the stipulated causal profile across all
admitted times. -/
def Immutable (person : Person) : Prop :=
  forall time time', model.profileAt person time = model.profileAt person time'

/-- The conjunction challenged by the conditional exclusion theorem. -/
def ExtraPersonCandidate (person : Person) : Prop :=
  model.substantial person /\
    model.separate person /\
    model.CausallyActive person /\
    model.Immutable person

/-- Every causally active, separate substantial candidate falls under one of
the two stated dependence alternatives.  This is an explicit coverage premise,
not a consequence of the bare model fields. -/
def DependenceExhaustive : Prop :=
  forall person,
    model.substantial person ->
    model.separate person ->
    model.CausallyActive person ->
      model.CausallyDependent person \/ model.ConceptuallyDependent person

/-- Conceptual dependence is incompatible with being separate.  Keeping this
as a premise prevents a definition from deciding the disputed conclusion. -/
def ConceptualDependencePrecludesSeparation : Prop :=
  forall person, model.ConceptuallyDependent person ->
    Not (model.separate person)

/-- Aggregate change propagates to the causal profile of every active causal
dependent.  Bare causal support does not include this bridge. -/
def ChangePropagation : Prop :=
  forall person time time',
    model.CausallyDependent person ->
    model.CausallyActive person ->
    model.stream.Changes time time' ->
      model.profileAt person time ≠ model.profileAt person time'

/-- The complete, inspectable certificate used by the exclusion theorem. -/
structure ExclusionPremises : Prop where
  exhaustive : model.DependenceExhaustive
  conceptualPrecludesSeparation :
    model.ConceptualDependencePrecludesSeparation
  aggregateChanges : exists time time', model.stream.Changes time time'
  changePropagates : model.ChangePropagation

/-- An active causal dependent cannot remain profile-immutable when aggregate
change is known to propagate to it. -/
theorem causal_dependence_excludes_immutability
    (propagates : model.ChangePropagation)
    (aggregateChanges : exists time time', model.stream.Changes time time')
    {person : Person}
    (dependent : model.CausallyDependent person)
    (active : model.CausallyActive person) :
    Not (model.Immutable person) := by
  intro immutable
  obtain ⟨time, time', changes⟩ := aggregateChanges
  exact propagates person time time' dependent active changes
    (immutable time time')

/-- Conditional exclusion of a causally active, immutable, separate
substantial person.  The proof uses dependence coverage, the conceptual horn,
a witnessed aggregate change, and causal change propagation; none is hidden
in the definition of a substantial person. -/
theorem no_active_immutable_separate_substantial_person
    (premises : model.ExclusionPremises) :
    forall person, Not (model.ExtraPersonCandidate person) := by
  intro person candidate
  rcases candidate with ⟨substantial, separate, active, immutable⟩
  cases premises.exhaustive person substantial separate active with
  | inl causal =>
      exact model.causal_dependence_excludes_immutability
        premises.changePropagates premises.aggregateChanges causal active
        immutable
  | inr conceptual =>
      exact premises.conceptualPrecludesSeparation person conceptual separate

theorem no_extra_person_exists (premises : model.ExclusionPremises) :
    Not (exists person, model.ExtraPersonCandidate person) := by
  rintro ⟨person, candidate⟩
  exact model.no_active_immutable_separate_substantial_person premises
    person candidate

/-- The theorem's scope leaves conventional designation intact. -/
theorem conventional_designation_compatible_with_exclusion
    (premises : model.ExclusionPremises)
    (conventional : exists person, model.ConventionallyDesignated person) :
    (exists person, model.ConventionallyDesignated person) /\
      Not (exists person, model.ExtraPersonCandidate person) :=
  ⟨conventional, model.no_extra_person_exists premises⟩

end Model

/-! ## Bare dependence is insufficient -/

inductive TwoTimes where
  | earlier
  | later
  deriving DecidableEq, Repr

open TwoTimes

/-! ## A finite positive model for the exclusion certificate -/

inductive DemoPerson where
  | conventionalContinuant
  | mutableCandidate
  deriving DecidableEq, Repr

open DemoPerson

/-- Both tokens causally depend on `rupa` and have time-varying profiles.  The
first is conventionally designated but not substantial; the second is a
separate substantial proposal but is mutable. -/
def changingPersonModel : Model DemoPerson TwoTimes TwoTimes where
  stream := {
    present := fun time aggregate =>
      match time, aggregate with
      | .later, .rupa => true
      | _, _ => false
    follows := fun first second => first = .earlier /\ second = .later
  }
  designatedAt := fun person _ => person = .conventionalContinuant
  substantial := fun person => person = .mutableCandidate
  separate := fun person => person = .mutableCandidate
  causalSupport := fun _ aggregate => aggregate = .rupa
  conceptualSupport := fun person aggregate =>
    person = .conventionalContinuant /\ aggregate = .rupa
  actsAt := fun _ time => time = .earlier
  profileAt := fun _ time => time

theorem changing_person_aggregate_changes :
    changingPersonModel.stream.Changes .earlier .later :=
  ⟨.rupa, by decide⟩

theorem changing_person_exclusion_premises :
    changingPersonModel.ExclusionPremises := by
  refine {
    exhaustive := ?_
    conceptualPrecludesSeparation := ?_
    aggregateChanges := ⟨.earlier, .later,
      changing_person_aggregate_changes⟩
    changePropagates := ?_
  }
  · intro person _ _ _
    exact Or.inl ⟨.rupa, rfl⟩
  · rintro person ⟨aggregate, conceptualPerson, _⟩
    intro separate
    exact (by decide :
      DemoPerson.conventionalContinuant ≠ DemoPerson.mutableCandidate)
      (conceptualPerson.symm.trans separate)
  · intro person first second _ _ changes
    intro sameProfile
    have sameTime : first = second := sameProfile
    subst second
    obtain ⟨aggregate, changed⟩ := changes
    exact changed rfl

theorem changing_person_positive_instance :
    (exists person,
      changingPersonModel.ConventionallyDesignated person) /\
      Not (exists person,
        changingPersonModel.ExtraPersonCandidate person) := by
  apply changingPersonModel.conventional_designation_compatible_with_exclusion
    changing_person_exclusion_premises
  exact ⟨.conventionalContinuant, fun _ => rfl⟩

/-- The positive model is not secured by an empty causal domain: the
conventional continuant is active and causally supported, while the separate
substantial proposal is also active but demonstrably mutable. -/
theorem changing_person_positive_instance_is_nonvacuous :
    changingPersonModel.stream.ChangingStep .earlier .later /\
      changingPersonModel.CausallyActive .conventionalContinuant /\
      changingPersonModel.CausallyDependent .conventionalContinuant /\
      changingPersonModel.ConceptuallyDependent .conventionalContinuant /\
      changingPersonModel.substantial .mutableCandidate /\
      changingPersonModel.separate .mutableCandidate /\
      changingPersonModel.CausallyActive .mutableCandidate /\
      Not (changingPersonModel.Immutable .mutableCandidate) := by
  refine ⟨⟨⟨rfl, rfl⟩, changing_person_aggregate_changes⟩,
    ⟨.earlier, rfl⟩, ⟨.rupa, rfl⟩,
    ⟨.rupa, rfl, rfl⟩, rfl, rfl,
    ⟨.earlier, rfl⟩, ?_⟩
  intro immutable
  exact (by decide : TwoTimes.earlier ≠ TwoTimes.later)
    (immutable .earlier .later)

/-- One aggregate dimension changes, while the alleged extra person's causal
profile remains constant.  This is allowed because no change-propagation law
is part of `Model`. -/
def stableExtraPerson : Model Unit TwoTimes Unit where
  stream := {
    present := fun time aggregate =>
      match time, aggregate with
      | .later, .rupa => true
      | _, _ => false
    follows := fun first second => first = .earlier /\ second = .later
  }
  designatedAt := fun _ _ => True
  substantial := fun _ => True
  separate := fun _ => True
  causalSupport := fun _ aggregate => aggregate = .rupa
  conceptualSupport := fun _ _ => False
  actsAt := fun _ time => time = .earlier
  profileAt := fun _ _ => ()

theorem stable_extra_aggregate_changes :
    stableExtraPerson.stream.Changes .earlier .later := by
  exact ⟨.rupa, by decide⟩

theorem stable_extra_is_nonvacuous :
    stableExtraPerson.stream.ChangingStep .earlier .later /\
      stableExtraPerson.ConventionallyDesignated () /\
      stableExtraPerson.DependsOn () .rupa /\
      stableExtraPerson.ExtraPersonCandidate () := by
  refine ⟨⟨⟨rfl, rfl⟩, stable_extra_aggregate_changes⟩,
    fun _ => trivial, Or.inl rfl, trivial, trivial, ?_, ?_⟩
  · exact ⟨.earlier, rfl⟩
  · intro _ _
    rfl

/-- Thus even witnessed aggregate change plus a bare `DependsOn` fact does
not exclude a stable extra person.  The failed bridge is exhibited directly. -/
theorem bare_dependsOn_does_not_exclude_a_stable_extra_person :
    stableExtraPerson.DependsOn () .rupa /\
      stableExtraPerson.ExtraPersonCandidate () /\
      Not stableExtraPerson.ChangePropagation := by
  refine ⟨stable_extra_is_nonvacuous.2.2.1,
    stable_extra_is_nonvacuous.2.2.2, ?_⟩
  intro propagation
  have changedProfile :
      stableExtraPerson.profileAt () .earlier ≠
        stableExtraPerson.profileAt () .later :=
    propagation () .earlier .later ⟨.rupa, rfl⟩
      ⟨.earlier, rfl⟩ stable_extra_aggregate_changes
  exact changedProfile rfl

/-! ## Causal, memory, and responsibility continuity without identity -/

/-- A separate relation model for stages of a conventionally designated
person.  The directions of `remembers` and `inheritsResponsibility` run from
the later stage to the earlier stage. -/
structure ContinuityModel (Person : Type u) (T : Type v) (Stage : Type w) where
  stageAt : Person -> T -> Stage
  causes : Stage -> Stage -> Prop
  remembers : Stage -> Stage -> Prop
  inheritsResponsibility : Stage -> Stage -> Prop

namespace ContinuityModel

variable {Person : Type u} {T : Type v} {Stage : Type w}
    (model : ContinuityModel Person T Stage)

def CausalContinuity (person : Person) (earlier later : T) : Prop :=
  model.causes (model.stageAt person earlier) (model.stageAt person later)

def MemoryContinuity (person : Person) (earlier later : T) : Prop :=
  model.remembers (model.stageAt person later) (model.stageAt person earlier)

def ResponsibilityContinuity
    (person : Person) (earlier later : T) : Prop :=
  model.inheritsResponsibility
    (model.stageAt person later) (model.stageAt person earlier)

def ContinuityPackage (person : Person) (earlier later : T) : Prop :=
  model.CausalContinuity person earlier later /\
    model.MemoryContinuity person earlier later /\
    model.ResponsibilityContinuity person earlier later

/-- Numerical identity is literal equality of the two stage tokens.  It is
not defined from causal, mnemonic, or normative continuity. -/
def NumericallyIdentical (person : Person) (first second : T) : Prop :=
  model.stageAt person first = model.stageAt person second

end ContinuityModel

inductive PersonStage where
  | earlyStage
  | lateStage
  deriving DecidableEq, Repr

open PersonStage

def inheritedContinuity : ContinuityModel Unit TwoTimes PersonStage where
  stageAt := fun _ time =>
    match time with
    | .earlier => .earlyStage
    | .later => .lateStage
  causes := fun source target =>
    source = .earlyStage /\ target = .lateStage
  remembers := fun laterStage rememberedStage =>
    laterStage = .lateStage /\ rememberedStage = .earlyStage
  inheritsResponsibility := fun laterStage earlierStage =>
    laterStage = .lateStage /\ earlierStage = .earlyStage

/-- A finite two-time, two-stage countermodel: all three continuities hold,
including responsibility inheritance, while the stage tokens are not
numerically identical. -/
theorem causal_memory_responsibility_do_not_imply_numerical_identity :
    inheritedContinuity.ContinuityPackage () .earlier .later /\
      Not (inheritedContinuity.NumericallyIdentical () .earlier .later) := by
  refine ⟨⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ?_⟩
  simp [ContinuityModel.NumericallyIdentical, inheritedContinuity]

/-- The countermodel is nontrivial both temporally and at the stage level. -/
theorem inherited_continuity_is_nonvacuous :
    TwoTimes.earlier ≠ TwoTimes.later /\
      inheritedContinuity.stageAt () .earlier ≠
        inheritedContinuity.stageAt () .later /\
      inheritedContinuity.ResponsibilityContinuity () .earlier .later := by
  exact ⟨by decide, by decide, ⟨rfl, rfl⟩⟩

end BuddhistComparativeLogic.Pudgala
