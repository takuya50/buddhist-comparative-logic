/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Yogacara.VimsatikaModels

/-!
# A conditional Yogācāra synthesis

This module connects four claims often grouped under a Yogācāra reading:
appearance-level adequacy, the three natures, continuity by seeds, and
transformation of the basis.  The interfaces are deliberately weaker than a
historical or metaphysical identification of those claims.

The `Vijnapti` record remains observational: satisfying its four adequacy
conditions does not assert that external objects exist or are absent.  Its
generic object-indexed factorization uses tokens copied from observations and
therefore carries no mind-independence premise.  The three natures are three
analyses of one phenomenon rather than three disjoint kinds of entity.  A seed
trajectory records causal succession without postulating an unchanging seed.
Finally, transformation requires a stated cut after which release and absence
of affliction persist; it is not derived from bare continuity.
-/

namespace BuddhistComparativeLogic.YogacaraSynthesis

open BuddhistComparativeLogic.Vimsatika
open BuddhistComparativeLogic.VimsatikaModels

/-! ## Appearance adequacy leaves object indexing open -/

/-- Any adequate appearance account has an equally adequate factorization by
the neutral token construction from `BuddhistComparativeLogic.Buddhist.Yogacara.VimsatikaModels`.  This proves
only existential factorization of presentation and efficacy; interpreting the
tokens as external objects requires additional premises. -/
theorem adequate_appearance_has_matching_token_factorization
    {Subject : Type u} {Location : Type v} {Time : Type w}
    (model : Vijnapti Subject Location Time) (adequate : model.adequate) :
    ∃ account : ObjectIndexedAccount Subject Location Time
        (ObservationToken Subject Location Time),
      observationEquivalent model account.observations ∧
        account.observations.adequate := by
  refine ⟨factorizeObservations model,
    every_appearance_account_has_token_factorization model, ?_⟩
  exact (token_factorization_preserves_adequacy model).mp adequate

/-- The concrete adequate hell-guard observations factor through both `Unit`
and `Bool`.  The conclusion records equivalence with the original account,
mutual observational equivalence, and non-bijection of the two carriers. -/
theorem four_conditions_leave_object_indexing_open :
    naraka.adequate ∧
      observationEquivalent naraka narakaUnitIndexed.observations ∧
      observationEquivalent naraka narakaBoolIndexed.observations ∧
      narakaUnitIndexed.observations.adequate ∧
      narakaBoolIndexed.observations.adequate ∧
      observationEquivalent narakaUnitIndexed.observations
        narakaBoolIndexed.observations ∧
      ¬ ∃ f : Bool → Unit, isBijection f :=
  four_conditions_do_not_decide_between_models

/-! ## The three natures as analyses of one phenomenon -/

/-- A restrained three-nature interface.  `dependent` records conditioned
occurrence, `projectedDuality` records an imagined subject/object
superimposition, and `suchness` records the dependent occurrence precisely in
the absence of that projection. -/
structure Trisvabhava (Phenomenon : Type u) where
  dependent : Phenomenon → Prop
  projectedDuality : Phenomenon → Prop
  suchness : Phenomenon → Prop
  suchness_iff : ∀ x, suchness x ↔ dependent x ∧ ¬ projectedDuality x

namespace Trisvabhava

variable (A : Trisvabhava Phenomenon)

inductive Nature where
  | imagined
  | dependent
  | perfected
  deriving DecidableEq, Repr

/-- The three Sanskrit nature names are interpreted through the three fields
of the analysis. -/
def Holds : Nature → Phenomenon → Prop
  | .imagined => A.projectedDuality
  | .dependent => A.dependent
  | .perfected => A.suchness

theorem perfected_implies_dependent {x : Phenomenon}
    (h : A.Holds .perfected x) : A.Holds .dependent x := by
  exact (A.suchness_iff x).mp h |>.1

theorem perfected_excludes_imagined {x : Phenomenon}
    (h : A.Holds .perfected x) : ¬ A.Holds .imagined x := by
  exact (A.suchness_iff x).mp h |>.2

/-- An imagined projection is incompatible with the perfected analysis.
Conditioned occurrence is deliberately not needed for this exclusion. -/
theorem projected_is_not_perfected {x : Phenomenon}
    (projected : A.Holds .imagined x) : ¬ A.Holds .perfected x := by
  intro perfected
  exact A.perfected_excludes_imagined perfected projected

theorem not_perfected_without_dependence {x : Phenomenon}
    (notDependent : ¬ A.Holds .dependent x) :
    ¬ A.Holds .perfected x := by
  intro perfected
  exact notDependent (A.perfected_implies_dependent perfected)

end Trisvabhava

/-! A three-element model witnesses that these analyses do not form a
partition.  A confused occurrence is both dependent and projected; a clear
occurrence is dependent and perfected; a fiction is projected without being
a dependent occurrence in the modeled domain. -/

inductive SamplePhenomenon where
  | confused
  | clear
  | fiction
  deriving DecidableEq, Repr

open SamplePhenomenon

def sampleTrisvabhava : Trisvabhava SamplePhenomenon where
  dependent
    | .confused => True
    | .clear => True
    | .fiction => False
  projectedDuality
    | .confused => True
    | .clear => False
    | .fiction => True
  suchness
    | .confused => False
    | .clear => True
    | .fiction => False
  suchness_iff := by
    intro x
    cases x <;> simp

theorem dependent_and_imagined_can_coincide :
    sampleTrisvabhava.Holds .dependent .confused ∧
      sampleTrisvabhava.Holds .imagined .confused ∧
      ¬ sampleTrisvabhava.Holds .perfected .confused := by
  simp [Trisvabhava.Holds, sampleTrisvabhava]

theorem dependent_does_not_suffice_for_perfected :
    ¬ ∀ x, sampleTrisvabhava.Holds .dependent x →
      sampleTrisvabhava.Holds .perfected x := by
  intro h
  have perfected := h .confused (by
    simp [Trisvabhava.Holds, sampleTrisvabhava])
  simp [Trisvabhava.Holds, sampleTrisvabhava] at perfected

theorem the_three_natures_are_not_disjoint_entity_classes :
    (∃ x, sampleTrisvabhava.Holds .dependent x ∧
        sampleTrisvabhava.Holds .imagined x) ∧
      (∃ x, sampleTrisvabhava.Holds .dependent x ∧
        sampleTrisvabhava.Holds .perfected x) := by
  constructor
  · exact ⟨.confused, by
      simp [Trisvabhava.Holds, sampleTrisvabhava]⟩
  · exact ⟨.clear, by
      simp [Trisvabhava.Holds, sampleTrisvabhava]⟩

/-! ## Seed continuity without a permanent substrate -/

/-- A seed trajectory supplies a seed at every stage and an explicit local
development relation between consecutive stages.  It contains no identity or
substance field. -/
structure SeedTrajectory (Seed : Type u) where
  seedAt : Nat → Seed
  develops : Seed → Seed → Prop
  step : ∀ n, develops (seedAt n) (seedAt (n + 1))

/-- Exactly `length` development steps connect two seeds. -/
inductive EvolvesN (develops : Seed → Seed → Prop) :
    Nat → Seed → Seed → Prop where
  | refl (seed : Seed) : EvolvesN develops 0 seed seed
  | tail {length : Nat} {first last next : Seed} :
      EvolvesN develops length first last →
      develops last next →
      EvolvesN develops (length + 1) first next

namespace SeedTrajectory

variable (path : SeedTrajectory Seed)

/-- Local seed continuity composes to a lineage of every finite length. -/
theorem lineage (start length : Nat) :
    EvolvesN path.develops length (path.seedAt start)
      (path.seedAt (start + length)) := by
  induction length with
  | zero =>
      simpa using
        (EvolvesN.refl (develops := path.develops) (path.seedAt start))
  | succ length ih =>
      rw [Nat.add_succ]
      exact EvolvesN.tail ih (path.step (start + length))

/-- A property is hereditary when every seed development preserves it. -/
def Hereditary (property : Seed → Prop) : Prop :=
  ∀ {first next}, path.develops first next →
    property first → property next

theorem evolves_preserves
    {property : Seed → Prop} (hereditary : path.Hereditary property)
    {length : Nat} {first last : Seed}
    (evolves : EvolvesN path.develops length first last)
    (initial : property first) : property last := by
  induction evolves with
  | refl => exact initial
  | tail prior step ih => exact hereditary step (ih initial)

theorem hereditary_along_trajectory
    {property : Seed → Prop} (hereditary : path.Hereditary property)
    (initial : property (path.seedAt start)) :
    property (path.seedAt (start + length)) :=
  path.evolves_preserves hereditary (path.lineage start length) initial

/-- Substantial persistence is a stronger, separately stated thesis: every
stage contains literally the initial seed. -/
def SubstantialPersistence : Prop :=
  ∀ n, path.seedAt n = path.seedAt 0

end SeedTrajectory

def settlingSeed : Nat → Bool
  | 0 => false
  | _ + 1 => true

def settlingDevelopment (first next : Bool) : Prop :=
  (first = false ∧ next = true) ∨
    (first = true ∧ next = true)

/-- A finite-state trajectory changes once and then settles. -/
def settlingTrajectory : SeedTrajectory Bool where
  seedAt := settlingSeed
  develops := settlingDevelopment
  step := by
    intro n
    cases n <;> simp [settlingSeed, settlingDevelopment]

theorem settling_has_finite_lineages (length : Nat) :
    EvolvesN settlingTrajectory.develops length
      (settlingTrajectory.seedAt 0)
      (settlingTrajectory.seedAt length) := by
  simpa using settlingTrajectory.lineage 0 length

/-- Causal continuity alone does not force numerical identity of the seed
through time. -/
theorem seed_continuity_does_not_require_an_unchanging_seed :
    (∀ n, settlingTrajectory.develops
        (settlingTrajectory.seedAt n) (settlingTrajectory.seedAt (n + 1))) ∧
      ¬ settlingTrajectory.SubstantialPersistence := by
  constructor
  · exact settlingTrajectory.step
  · intro persistent
    have h := persistent 1
    simp [settlingTrajectory, settlingSeed] at h

/-! ## Transformation of the basis -/

/-- `TransformationAt path afflicted released cut` says that every earlier
stage is afflicted and that from `cut` onward release holds while affliction
does not.  This is an explicit bridge principle, not a consequence of the
seed-transition relation. -/
def TransformationAt (path : SeedTrajectory Seed)
    (afflicted released : Seed → Prop) (cut : Nat) : Prop :=
  (∀ n, n < cut → afflicted (path.seedAt n)) ∧
    (∀ n, cut ≤ n →
      released (path.seedAt n) ∧ ¬ afflicted (path.seedAt n))

theorem transformation_holds_at_cut
    (transformed : TransformationAt path afflicted released cut) :
    released (path.seedAt cut) ∧ ¬ afflicted (path.seedAt cut) :=
  transformed.2 cut (Nat.le_refl cut)

/-- A noninitial transformation entails a real change in the modeled basis:
an afflicted initial seed cannot equal the unafflicted seed at the cut. -/
theorem transformation_changes_the_basis
    (positiveCut : 0 < cut)
    (transformed : TransformationAt path afflicted released cut) :
    path.seedAt 0 ≠ path.seedAt cut := by
  intro equal
  have initialAfflicted := transformed.1 0 positiveCut
  have cutUnafflicted := (transformation_holds_at_cut transformed).2
  rw [equal] at initialAfflicted
  exact cutUnafflicted initialAfflicted

def sampleAfflicted : Bool → Prop := fun seed => seed = false

def sampleReleased : Bool → Prop := fun seed => seed = true

theorem settling_transforms_at_one :
    TransformationAt settlingTrajectory sampleAfflicted sampleReleased 1 := by
  constructor
  · intro n hn
    have hn0 : n = 0 := by omega
    subst n
    simp [sampleAfflicted, settlingTrajectory, settlingSeed]
  · intro n hn
    cases n with
    | zero => omega
    | succ n =>
        simp [sampleReleased, sampleAfflicted, settlingTrajectory,
          settlingSeed]

theorem settling_transformation_changes_seed :
    settlingTrajectory.seedAt 0 ≠ settlingTrajectory.seedAt 1 :=
  transformation_changes_the_basis (by decide) settling_transforms_at_one

/-- Released dependent occurrence realizes the perfected analysis once
release is explicitly connected to absence of projected duality. -/
theorem transformation_realizes_perfected_at_cut
    (analysis : Trisvabhava Seed)
    (transformed : TransformationAt path afflicted released cut)
    (dependentAt : analysis.dependent (path.seedAt cut))
    (releaseEndsProjection : ∀ seed,
      released seed → ¬ analysis.projectedDuality seed) :
    analysis.suchness (path.seedAt cut) := by
  apply (analysis.suchness_iff (path.seedAt cut)).mpr
  refine ⟨dependentAt, ?_⟩
  exact releaseEndsProjection _ (transformation_holds_at_cut transformed).1

def seedTrisvabhava : Trisvabhava Bool where
  dependent _ := True
  projectedDuality seed := seed = false
  suchness seed := seed = true
  suchness_iff := by
    intro seed
    cases seed <;> simp

theorem settling_transformation_realizes_perfected :
    seedTrisvabhava.suchness (settlingTrajectory.seedAt 1) := by
  apply transformation_realizes_perfected_at_cut seedTrisvabhava
    settling_transforms_at_one
  · trivial
  · intro seed released projected
    exact (by decide : true ≠ false) (released.symm.trans projected)

/-! A constant afflicted stream is continuous but never transformed.  This
finite countermodel keeps the transition and transformation assumptions
logically separate. -/

def afflictedConstantTrajectory : SeedTrajectory Bool where
  seedAt _ := false
  develops := (· = ·)
  step := fun _ => rfl

theorem continuity_alone_does_not_supply_transformation :
    (∀ n, afflictedConstantTrajectory.develops
        (afflictedConstantTrajectory.seedAt n)
        (afflictedConstantTrajectory.seedAt (n + 1))) ∧
      (∀ n, seedTrisvabhava.dependent
        (afflictedConstantTrajectory.seedAt n)) ∧
      ¬ ∃ cut, TransformationAt afflictedConstantTrajectory
        sampleAfflicted sampleReleased cut := by
  refine ⟨afflictedConstantTrajectory.step, fun _ => trivial, ?_⟩
  · rintro ⟨cut, transformed⟩
    have released := (transformation_holds_at_cut transformed).1
    simp [afflictedConstantTrajectory, sampleReleased] at released

end BuddhistComparativeLogic.YogacaraSynthesis
