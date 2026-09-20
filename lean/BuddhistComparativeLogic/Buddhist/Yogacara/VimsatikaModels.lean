/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Yogacara.Vimsatika

/-!
# Appearance models and object-indexed factorizations

The four adequacy conditions in `BuddhistComparativeLogic.Buddhist.Yogacara.Vimsatika` mention only appearance
and efficacy.  This module factors those two predicates through an indexed
carrier and compares the resulting accounts through their observable fields.
The type `ObjectIndexedAccount` denotes only this relational interface: it
does not encode mind-independence, persistence, individuation, or even
nonemptiness of the carrier.  Consequently the generic construction below is
a factorization through observation tokens, not a proof that external objects
exist.  Concrete `Unit`- and `Bool`-indexed accounts show only that the same
observations leave the carrier cardinality underdetermined at this interface.
-/

namespace BuddhistComparativeLogic.VimsatikaModels

open BuddhistComparativeLogic.Vimsatika

/-- A neutral object-indexed presentation/effect interface.  The `Object`
parameter is an index carrier; further premises are required to interpret its
elements as mind-independent or persistent objects. -/
structure ObjectIndexedAccount (Subject : Type u) (Location : Type v)
    (Time : Type w) (Object : Type z) where
  presents : Subject → Object → Location → Time → Prop
  acts : Subject → Object → Location → Time → Prop

namespace ObjectIndexedAccount

variable {Subject : Type u} {Location : Type v} {Time : Type w}
  {Object : Type z}

def observations (model : ObjectIndexedAccount Subject Location Time Object) :
    Vijnapti Subject Location Time where
  appears s p t := ∃ object, model.presents s object p t
  effective s p t := ∃ object, model.acts s object p t

/-- Duplicating every object changes the object domain while preserving all
generated observations. -/
def duplicate (model : ObjectIndexedAccount Subject Location Time Object) :
    ObjectIndexedAccount Subject Location Time (Object × Bool) where
  presents s object p t := model.presents s object.1 p t
  acts s object p t := model.acts s object.1 p t

end ObjectIndexedAccount

variable {Subject : Type u} {Location : Type v} {Time : Type w}
  {Object : Type z}

/-- Accounts are observationally equivalent when their appearance and
efficacy predicates agree extensionally. -/
def observationEquivalent
    (left right : Vijnapti Subject Location Time) : Prop :=
  left.appears = right.appears ∧ left.effective = right.effective

theorem observationEquivalent_refl
    (model : Vijnapti Subject Location Time) :
    observationEquivalent model model :=
  ⟨rfl, rfl⟩

theorem observationEquivalent_symm
    {left right : Vijnapti Subject Location Time}
    (h : observationEquivalent left right) :
    observationEquivalent right left :=
  ⟨h.1.symm, h.2.symm⟩

theorem observationEquivalent_trans
    {first second third : Vijnapti Subject Location Time}
    (h₁ : observationEquivalent first second)
    (h₂ : observationEquivalent second third) :
    observationEquivalent first third :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem eq_of_observationEquivalent
    {left right : Vijnapti Subject Location Time}
    (h : observationEquivalent left right) : left = right := by
  cases left with
  | mk leftAppearance leftEffect =>
    cases right with
    | mk rightAppearance rightEffect =>
      change leftAppearance = rightAppearance ∧
        leftEffect = rightEffect at h
      rcases h with ⟨rfl, rfl⟩
      rfl

/-- All four Viṃśatikā adequacy conditions are invariant under the observable
comparison relation. -/
theorem adequacy_is_observation_invariant
    {left right : Vijnapti Subject Location Time}
    (h : observationEquivalent left right) :
    left.adequate ↔ right.adequate := by
  rw [eq_of_observationEquivalent h]

theorem duplicate_is_observation_equivalent
    (model : ObjectIndexedAccount Subject Location Time Object) :
    observationEquivalent model.observations model.duplicate.observations := by
  constructor
  · funext s p t
    apply propext
    constructor
    · rintro ⟨object, hobject⟩
      exact ⟨(object, false), hobject⟩
    · rintro ⟨object, hobject⟩
      exact ⟨object.1, hobject⟩
  · funext s p t
    apply propext
    constructor
    · rintro ⟨object, hobject⟩
      exact ⟨(object, false), hobject⟩
    · rintro ⟨object, hobject⟩
      exact ⟨object.1, hobject⟩

/-! ## Observation-token factorization of any appearance account -/

/-- Tokens generated directly from observable tuples.  Their name records the
object-index position they occupy in `ObjectIndexedAccount`; it carries no
mind-independence claim. -/
inductive ObservationToken (Subject : Type u) (Location : Type v) (Time : Type w)
  | appearance : Subject → Location → Time →
      ObservationToken Subject Location Time
  | efficacy : Subject → Location → Time → ObservationToken Subject Location Time

/-- Factor an appearance account through tokens copied from its observable
tuples. -/
def factorizeObservations (model : Vijnapti Subject Location Time) :
    ObjectIndexedAccount Subject Location Time
      (ObservationToken Subject Location Time) where
  presents s object p t :=
    match object with
    | .appearance s' p' t' =>
        s = s' ∧ p = p' ∧ t = t' ∧ model.appears s p t
    | .efficacy _ _ _ => False
  acts s object p t :=
    match object with
    | .appearance _ _ _ => False
    | .efficacy s' p' t' =>
        s = s' ∧ p = p' ∧ t = t' ∧ model.effective s p t

/-- The token factorization exactly reproduces both observable predicates of
an arbitrary appearance account.  It supplies no premise beyond that
existential factorization. -/
theorem every_appearance_account_has_token_factorization
    (model : Vijnapti Subject Location Time) :
    observationEquivalent model (factorizeObservations model).observations := by
  constructor
  · funext s p t
    apply propext
    constructor
    · intro h
      exact ⟨.appearance s p t, rfl, rfl, rfl, h⟩
    · rintro ⟨object, hobject⟩
      cases object with
      | appearance s' p' t' => exact hobject.2.2.2
      | efficacy s' p' t' => exact False.elim hobject
  · funext s p t
    apply propext
    constructor
    · intro h
      exact ⟨.efficacy s p t, rfl, rfl, rfl, h⟩
    · rintro ⟨object, hobject⟩
      cases object with
      | appearance s' p' t' => exact False.elim hobject
      | efficacy s' p' t' => exact hobject.2.2.2

/-- Adequacy is preserved because it is stated entirely in the two reproduced
observable predicates. -/
theorem token_factorization_preserves_adequacy
    (model : Vijnapti Subject Location Time) :
    model.adequate ↔ (factorizeObservations model).observations.adequate :=
  adequacy_is_observation_invariant
    (every_appearance_account_has_token_factorization model)

/-! ## Concrete carrier non-uniqueness for the shared naraka appearances -/

open Person Place Moment

def narakaUnitIndexed : ObjectIndexedAccount Person Place Moment Unit where
  presents _ _ p t := p = .here ∧ t = .now
  acts _ _ p t := p = .here ∧ t = .now

def narakaBoolIndexed : ObjectIndexedAccount Person Place Moment Bool where
  presents _ _ p t := p = .here ∧ t = .now
  acts _ _ p t := p = .here ∧ t = .now

theorem naraka_unit_indexed_equivalent :
    observationEquivalent naraka narakaUnitIndexed.observations := by
  constructor
  · funext s p t
    apply propext
    simp [naraka, narakaApp, ObjectIndexedAccount.observations, narakaUnitIndexed]
  · funext s p t
    apply propext
    simp [naraka, narakaApp, ObjectIndexedAccount.observations, narakaUnitIndexed]

theorem naraka_bool_indexed_equivalent :
    observationEquivalent naraka narakaBoolIndexed.observations := by
  constructor
  · funext s p t
    apply propext
    simp [naraka, narakaApp, ObjectIndexedAccount.observations, narakaBoolIndexed]
  · funext s p t
    apply propext
    simp [naraka, narakaApp, ObjectIndexedAccount.observations, narakaBoolIndexed]

def isBijection (f : α → β) : Prop :=
  Function.Injective f ∧ Function.Surjective f

theorem no_bijection_bool_unit :
    ¬ ∃ f : Bool → Unit, isBijection f := by
  rintro ⟨f, hf⟩
  have heq : f false = f true := Subsingleton.elim _ _
  have hfalseTrue : false = true := hf.1 heq
  exact (by decide : false ≠ true) hfalseTrue

/-- The same adequate observations factor through `Unit` and `Bool` carriers,
which cannot be put in bijection.  This is a result about object-index
cardinality at the stated interface, not about metaphysical externality. -/
theorem object_index_cardinality_is_observationally_underdetermined :
    observationEquivalent naraka narakaUnitIndexed.observations ∧
      observationEquivalent naraka narakaBoolIndexed.observations ∧
      narakaUnitIndexed.observations.adequate ∧
      narakaBoolIndexed.observations.adequate ∧
      ¬ ∃ f : Bool → Unit, isBijection f := by
  refine ⟨naraka_unit_indexed_equivalent, naraka_bool_indexed_equivalent,
    (adequacy_is_observation_invariant naraka_unit_indexed_equivalent).mp
      naraka_meets_all_four,
    (adequacy_is_observation_invariant naraka_bool_indexed_equivalent).mp
      naraka_meets_all_four,
    no_bijection_bool_unit⟩

/-- The full comparison certificate includes adequacy, equivalence of the
appearance account with both object-indexed accounts, equivalence of those
accounts with each other, and non-bijection of their carriers. -/
theorem four_conditions_do_not_decide_between_models :
    naraka.adequate ∧
      observationEquivalent naraka narakaUnitIndexed.observations ∧
      observationEquivalent naraka narakaBoolIndexed.observations ∧
      narakaUnitIndexed.observations.adequate ∧
      narakaBoolIndexed.observations.adequate ∧
      observationEquivalent narakaUnitIndexed.observations
        narakaBoolIndexed.observations ∧
      ¬ ∃ f : Bool → Unit, isBijection f := by
  have h₁ := naraka_unit_indexed_equivalent
  have h₂ := naraka_bool_indexed_equivalent
  exact ⟨naraka_meets_all_four, h₁, h₂,
    (adequacy_is_observation_invariant h₁).mp naraka_meets_all_four,
    (adequacy_is_observation_invariant h₂).mp naraka_meets_all_four,
    observationEquivalent_trans (observationEquivalent_symm h₁) h₂,
    no_bijection_bool_unit⟩

end BuddhistComparativeLogic.VimsatikaModels
