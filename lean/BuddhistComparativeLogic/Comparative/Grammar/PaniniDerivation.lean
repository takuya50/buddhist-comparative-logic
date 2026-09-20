/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Grammar.Bhartrhari

/-!
# Ranked priority rewriting

This module gives a small, executable rewrite interface inspired by the
rule ordering and conflict-resolution questions associated with Pāṇini.  A
finite rule inventory is separated from an explicit resolver.  Every
applicable rewrite must lower a natural-number rank, while the resolver must
choose an applicable rule of maximal declared priority.  These premises give
a terminating chosen derivation.  Uniqueness of normal forms is proved only
for a step relation supplied with an explicit determinism premise.

This is a bounded priority-rewrite interface, not a formalization of the full
*Aṣṭādhyāyī*.  In particular, list order and numeric priority below are modern
formal devices; the development does not assert that they give the unique
historical reading of *vipratiṣedha* or of Pāṇini's metarules.

Source mapping (accessed 2026-09-19): Pāṇini, *Aṣṭādhyāyī* 1.4.2,
`vipratiṣedhe paraṃ kāryam`, is fixed by the Sanskrit Library sūtra record
(https://sanskritlibrary.org/grammatical/data/A.1.4.2.html).  Rishi Rajpopat,
“The Evolution of Conflict-Resolution Tools in the Early Pāṇinian Tradition,”
*Bhasha* 2.1 (2023), 31–58, doi:10.30687/bhasha/2785-5953/2023/01/002,
provides peer-reviewed orientation on the usual serial-order reading and its
historical qualifications.  `priority` is a modern parameter which can encode
that reading; numeric ranks, list enumeration, the resolver, termination, and
normal-form uniqueness are project-authored formal infrastructure, not a
translation or consequence asserted by sūtra 1.4.2.  The `Bhartrhari` import
is used only for its generic rewrite adapter and carries no historical claim.
-/

namespace BuddhistComparativeLogic.PaniniDerivation

universe u v

/-! ## Finite ranked systems and an explicit resolver -/

/-- A finite rewrite inventory.  Applicability is Boolean so that concrete
instances can be executed.  The decrease proof is required for every
applicable rule, independently of whichever rule the resolver later picks. -/
structure FiniteRankedRewrite (Term : Type u) (Rule : Type v) where
  applies : Rule -> Term -> Bool
  result : Rule -> Term -> Term
  priority : Rule -> Nat
  rank : Term -> Nat
  rules : List Rule
  rulesComplete : forall rule, rule ∈ rules
  rulesNodup : rules.Nodup
  decreases : forall {rule term}, applies rule term = true ->
    rank (result rule term) < rank term

/-- A resolver makes conflict handling explicit.  It either returns no rule
because none applies, or returns an applicable rule whose numeric priority is
at least that of every applicable rule. -/
structure PrioritySystem (Term : Type u) (Rule : Type v)
    extends FiniteRankedRewrite Term Rule where
  choose : Term -> Option Rule
  chooseSound : forall {term rule}, choose term = some rule ->
    applies rule term = true
  chooseComplete : forall {term}, choose term = none ->
    forall rule, applies rule term = false
  chooseMaximal : forall {term rule}, choose term = some rule ->
    forall alternative, applies alternative term = true ->
      priority alternative ≤ priority rule

variable {Term : Type u} {Rule : Type v}

namespace FiniteRankedRewrite

/-- One raw step may use any applicable rule. -/
def RawStep (system : FiniteRankedRewrite Term Rule)
    (source target : Term) : Prop :=
  exists rule, system.applies rule source = true /\
    system.result rule source = target

/-- A term is normal for the full raw rule inventory, not merely stuck under
an incomplete resolver. -/
def Normal (system : FiniteRankedRewrite Term Rule) (term : Term) : Prop :=
  forall rule, system.applies rule term = false

end FiniteRankedRewrite

namespace PrioritySystem

/-- One chosen step uses exactly the rule returned by the resolver. -/
def ChosenStep (system : PrioritySystem Term Rule)
    (source target : Term) : Prop :=
  exists rule, system.choose source = some rule /\
    system.result rule source = target

theorem choose_none_iff_normal (system : PrioritySystem Term Rule)
    (term : Term) :
    system.choose term = none <-> system.toFiniteRankedRewrite.Normal term := by
  constructor
  · exact system.chooseComplete
  · intro normal
    cases chosen : system.choose term with
    | none => rfl
    | some rule =>
        have applies := system.chooseSound chosen
        have misses := normal rule
        simp_all

theorem chosen_step_is_raw (system : PrioritySystem Term Rule)
    {source target : Term} (step : system.ChosenStep source target) :
    system.toFiniteRankedRewrite.RawStep source target := by
  rcases step with ⟨rule, selected, rfl⟩
  exact ⟨rule, system.chooseSound selected, rfl⟩

theorem chosen_step_decreases (system : PrioritySystem Term Rule)
    {source target : Term} (step : system.ChosenStep source target) :
    system.rank target < system.rank source := by
  rcases step with ⟨rule, selected, rfl⟩
  exact system.decreases (system.chooseSound selected)

/-- The resolver makes the chosen successor functional even if several raw
rules apply. -/
theorem chosen_step_deterministic (system : PrioritySystem Term Rule)
    {source left right : Term}
    (leftStep : system.ChosenStep source left)
    (rightStep : system.ChosenStep source right) : left = right := by
  rcases leftStep with ⟨leftRule, leftChosen, rfl⟩
  rcases rightStep with ⟨rightRule, rightChosen, rightResult⟩
  have sameRule : leftRule = rightRule := by
    rw [leftChosen] at rightChosen
    exact Option.some.inj rightChosen
  subst rightRule
  exact rightResult

/-- The executable one-step checker/runner. -/
def next? (system : PrioritySystem Term Rule) (term : Term) : Option Term :=
  match system.choose term with
  | none => none
  | some rule => some (system.result rule term)

theorem next_some_sound (system : PrioritySystem Term Rule)
    {source target : Term} (next : system.next? source = some target) :
    system.ChosenStep source target := by
  unfold next? at next
  cases selected : system.choose source with
  | none => simp [selected] at next
  | some rule =>
      simp [selected] at next
      subst target
      exact ⟨rule, selected, rfl⟩

/-- Run at most the supplied number of selected rewrites.  Once no rule is
available, remaining fuel leaves the term unchanged. -/
def run (system : PrioritySystem Term Rule) : Nat -> Term -> Term
  | 0, term => term
  | fuel + 1, term =>
      match system.choose term with
      | none => term
      | some rule => system.run fuel (system.result rule term)

theorem run_is_normal_above_rank (system : PrioritySystem Term Rule) :
    forall fuel term, system.rank term < fuel ->
      system.toFiniteRankedRewrite.Normal (system.run fuel term) := by
  intro fuel
  induction fuel with
  | zero =>
      intro term below
      omega
  | succ fuel ih =>
      intro term below
      unfold run
      cases selected : system.choose term with
      | none =>
          exact (system.choose_none_iff_normal term).mp selected
      | some rule =>
          apply ih (system.result rule term)
          have decrease : system.rank (system.result rule term) <
              system.rank term :=
            system.decreases (system.chooseSound selected)
          omega

/-- A canonical executable output, with a rank-derived fuel bound. -/
def normalize (system : PrioritySystem Term Rule) (term : Term) : Term :=
  system.run (system.rank term + 1) term

theorem normalize_is_normal (system : PrioritySystem Term Rule)
    (term : Term) :
    system.toFiniteRankedRewrite.Normal (system.normalize term) := by
  apply system.run_is_normal_above_rank (fuel := system.rank term + 1)
    (term := term)
  omega

end PrioritySystem

/-! ## Why uniqueness needs a separate premise -/

/-- Finite reflexive-transitive closure, kept generic so the uniqueness
theorem applies to either raw or resolved steps. -/
inductive Reaches (step : Term -> Term -> Prop) : Term -> Term -> Prop
  | refl (term : Term) : Reaches step term term
  | tail {source middle target : Term} :
      step source middle -> Reaches step middle target ->
        Reaches step source target

def RelationNormal (step : Term -> Term -> Prop) (term : Term) : Prop :=
  forall target, ¬ step term target

def Deterministic (step : Term -> Term -> Prop) : Prop :=
  forall {source left right}, step source left -> step source right ->
    left = right

/-- Two reached normal forms coincide only after determinism of the supplied
step relation is assumed explicitly.  Termination is a distinct issue and is
provided above for the chosen relation by the rank proof. -/
theorem deterministic_normal_forms_unique
    {step : Term -> Term -> Prop} (deterministic : Deterministic step)
    {source left right : Term}
    (leftReach : Reaches step source left)
    (rightReach : Reaches step source right)
    (leftNormal : RelationNormal step left)
    (rightNormal : RelationNormal step right) : left = right := by
  induction leftReach generalizing right with
  | refl source =>
      cases rightReach with
      | refl => rfl
      | tail first _ => exact False.elim (leftNormal _ first)
  | tail first rest ih =>
      cases rightReach with
      | refl => exact False.elim (rightNormal _ first)
      | tail otherFirst otherRest =>
          have sameMiddle := deterministic first otherFirst
          subst sameMiddle
          exact ih otherRest leftNormal rightNormal

/-! ## A nonvacuous finite priority derivation -/

inductive SampleTerm where
  | input
  | stem
  | output
  deriving DecidableEq, Repr

inductive SampleRule where
  | exposeStem
  | finishForm
  deriving DecidableEq, Repr

open SampleTerm SampleRule

def sampleSystem : PrioritySystem SampleTerm SampleRule where
  applies
    | .exposeStem, .input => true
    | .finishForm, .stem => true
    | _, _ => false
  result
    | .exposeStem, .input => .stem
    | .finishForm, .stem => .output
    | _, term => term
  priority
    | .exposeStem => 1
    | .finishForm => 2
  rank
    | .input => 2
    | .stem => 1
    | .output => 0
  rules := [.exposeStem, .finishForm]
  rulesComplete := by intro rule; cases rule <;> simp
  rulesNodup := by decide
  decreases := by
    intro rule term applies
    cases rule <;> cases term <;> simp_all
  choose
    | .input => some .exposeStem
    | .stem => some .finishForm
    | .output => none
  chooseSound := by
    intro term rule selected
    cases term <;> cases rule <;> simp_all
  chooseComplete := by
    intro term selected rule
    cases term <;> cases rule <;> simp_all
  chooseMaximal := by
    intro term rule selected alternative applicable
    cases term <;> cases rule <;> cases alternative <;> simp_all

theorem sample_priority_derivation_nonvacuous :
    Nonempty (PrioritySystem SampleTerm SampleRule) /\
      sampleSystem.next? .input = some .stem /\
      sampleSystem.next? .stem = some .output /\
      sampleSystem.normalize .input = .output /\
      sampleSystem.toFiniteRankedRewrite.Normal .output := by
  refine ⟨⟨sampleSystem⟩, rfl, rfl, rfl, ?_⟩
  intro rule
  cases rule <;> rfl

/-! ## A finite critical pair -/

inductive ForkTerm where
  | source
  | leftNormal
  | rightNormal
  deriving DecidableEq, Repr

inductive ForkRule where
  | turnLeft
  | turnRight
  deriving DecidableEq, Repr

open ForkTerm ForkRule

def criticalPairInventory : FiniteRankedRewrite ForkTerm ForkRule where
  applies
    | .turnLeft, .source => true
    | .turnRight, .source => true
    | _, _ => false
  result
    | .turnLeft, .source => .leftNormal
    | .turnRight, .source => .rightNormal
    | _, term => term
  priority := fun _ => 1
  rank
    | .source => 1
    | .leftNormal => 0
    | .rightNormal => 0
  rules := [.turnLeft, .turnRight]
  rulesComplete := by intro rule; cases rule <;> simp
  rulesNodup := by decide
  decreases := by
    intro rule term applies
    cases rule <;> cases term <;> simp_all

theorem raw_critical_pair_has_distinct_normal_forms :
    Nonempty (FiniteRankedRewrite ForkTerm ForkRule) /\
      criticalPairInventory.RawStep .source .leftNormal /\
      criticalPairInventory.RawStep .source .rightNormal /\
      criticalPairInventory.Normal .leftNormal /\
      criticalPairInventory.Normal .rightNormal /\
      .leftNormal ≠ (.rightNormal : ForkTerm) /\
      ¬ Deterministic criticalPairInventory.RawStep := by
  refine ⟨⟨criticalPairInventory⟩,
    ⟨.turnLeft, rfl, rfl⟩, ⟨.turnRight, rfl, rfl⟩,
    ?_, ?_, by decide, ?_⟩
  · intro rule
    cases rule <;> rfl
  · intro rule
    cases rule <;> rfl
  · intro deterministic
    have equal := deterministic
      (source := ForkTerm.source)
      (left := ForkTerm.leftNormal)
      (right := ForkTerm.rightNormal)
      ⟨.turnLeft, rfl, rfl⟩ ⟨.turnRight, rfl, rfl⟩
    exact (by decide : ForkTerm.leftNormal ≠ ForkTerm.rightNormal) equal

/-- Priority can resolve the critical pair, but that resolver is extra data;
the raw ranked inventory itself did not select this branch. -/
def leftBiasedResolution : PrioritySystem ForkTerm ForkRule where
  toFiniteRankedRewrite := criticalPairInventory
  choose
    | .source => some .turnLeft
    | _ => none
  chooseSound := by
    intro term rule selected
    cases term <;> cases rule <;> simp_all [criticalPairInventory]
  chooseComplete := by
    intro term selected rule
    cases term <;> cases rule <;> simp_all [criticalPairInventory]
  chooseMaximal := by
    intro term rule selected alternative applicable
    cases term <;> cases rule <;> cases alternative <;>
      simp_all [criticalPairInventory]

theorem explicit_resolution_selects_left :
    leftBiasedResolution.normalize .source = .leftNormal /\
      leftBiasedResolution.toFiniteRankedRewrite.Normal .leftNormal := by
  refine ⟨rfl, ?_⟩
  intro rule
  cases rule <;> rfl

/-! ## Typed connection to the staged-expression API -/

/-- Interpret the three derivation stages as existing Bhartṛhari stage/token
pairs.  The interpretation is external to the rewrite engine. -/
def asStagedToken : SampleTerm ->
    Bhartrhari.SampleStage × Bhartrhari.SampleToken
  | .input => (.base, .ordinaryName)
  | .stem => (.extended, .ordinaryName)
  | .output => (.extended, .avacyaName)

/-- The executable normal form maps to the already formalized successful
later-stage designation of the target. -/
theorem normalized_output_denotes_bhartrhari_target :
    let staged := asStagedToken (sampleSystem.normalize .input)
    Bhartrhari.sampleLanguage.SuccessfullyExpresses staged.1 staged.2
      (.entity .target) := by
  exact ⟨rfl, rfl⟩

end BuddhistComparativeLogic.PaniniDerivation
