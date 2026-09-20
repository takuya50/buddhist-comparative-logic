/- SPDX-License-Identifier: Apache-2.0 -/

import Std

/-!
# MMK II: the gone, the not-gone, and the being-gone-over

This semantic port partitions a strict linear order around a current place,
proves that the present locus is a singleton and therefore is not itself a
traversed region, and keeps density as an explicit premise.  It models one
formal boundary in MMK II; it is not a complete translation of the chapter.
-/

namespace BuddhistComparativeLogic.Gamana

abbrev PredSet (α : Type u) := α → Prop

structure StrictLinearOrder (P : Type u) where
  lt : P → P → Prop
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z
  trichotomy : ∀ x y, lt x y ∨ x = y ∨ lt y x

def gata (o : StrictLinearOrder P) (c : P) : PredSet P := fun x => o.lt x c

def agata (o : StrictLinearOrder P) (c : P) : PredSet P := fun x => o.lt c x

def gamyamana (o : StrictLinearOrder P) (c : P) : PredSet P :=
  fun x => ¬ o.lt x c ∧ ¬ o.lt c x

theorem threefold_division_partitions (o : StrictLinearOrder P) (c x : P) :
    (gata o c x ∨ gamyamana o c x ∨ agata o c x) ∧
      ¬ (gata o c x ∧ gamyamana o c x) ∧
      ¬ (gata o c x ∧ agata o c x) ∧
      ¬ (gamyamana o c x ∧ agata o c x) := by
  have tri := o.trichotomy x c
  rcases tri with h | h | h
  · exact ⟨Or.inl h, fun q => q.2.1 q.1,
      fun q => o.irrefl _ (o.trans q.1 q.2), fun q => q.1.1 h⟩
  · subst x
    exact ⟨Or.inr (Or.inl ⟨o.irrefl _, o.irrefl _⟩),
      fun q => q.2.1 q.1, fun q => o.irrefl _ q.1,
      fun q => q.1.2 q.2⟩
  · exact ⟨Or.inr (Or.inr h), fun q => q.2.2 h,
      fun q => o.irrefl _ (o.trans q.2 q.1), fun q => q.1.2 q.2⟩

theorem gamyamana_is_a_point (o : StrictLinearOrder P) (c x : P) :
    gamyamana o c x ↔ x = c := by
  constructor
  · intro h
    rcases o.trichotomy x c with hlt | heq | hgt
    · exact False.elim (h.1 hlt)
    · exact heq
    · exact False.elim (h.2 hgt)
  · rintro rfl
    exact ⟨o.irrefl _, o.irrefl _⟩

def traverses (R : PredSet P) : Prop :=
  ∃ a, R a ∧ ∃ b, R b ∧ a ≠ b

theorem no_traversal_of_a_point (c : P) :
    ¬ traverses (fun x => x = c) := by
  rintro ⟨a, rfl, b, rfl, h⟩
  exact h rfl

theorem no_motion_in_gamyamana (o : StrictLinearOrder P) (c : P) :
    ¬ traverses (gamyamana o c) := by
  rintro ⟨a, ha, b, hb, hab⟩
  have hac := (gamyamana_is_a_point o c a).mp ha
  have hbc := (gamyamana_is_a_point o c b).mp hb
  exact hab (hac.trans hbc.symm)

theorem gone_and_not_gone_can_be_traversed (o : StrictLinearOrder P)
    {a b c : P} (hab : o.lt a b) (hbc : o.lt b c) :
    traverses (gata o c) := by
  refine ⟨a, o.trans hab hbc, b, hbc, ?_⟩
  intro heq
  subst b
  exact o.irrefl _ hab

theorem motion_is_not_a_property_of_a_place (x : P) :
    ¬ traverses (fun y => y = x) :=
  no_traversal_of_a_point x

theorem no_first_untraversed (o : StrictLinearOrder P)
    (density : ∀ x y : P, o.lt x y → ∃ z, o.lt x z ∧ o.lt z y)
    {c b : P} (hcb : o.lt c b) :
    ∃ b', agata o c b' ∧ o.lt b' b := by
  obtain ⟨z, hcz, hzb⟩ := density c b hcb
  exact ⟨z, hcz, hzb⟩

theorem goer_goes_is_empty
    {A : Type u} (goer moves : A → Prop)
    (same : ∀ x, goer x ↔ moves x) (x : A) :
    (goer x ∧ moves x) ↔ moves x := by
  constructor
  · exact fun h => h.2
  · intro hm
    exact ⟨(same x).mpr hm, hm⟩

theorem goer_goes_doubles
    {A : Type u} (goer moves : A → Prop) (count : A → Nat)
    [DecidablePred goer] [DecidablePred moves]
    (same : ∀ x, goer x ↔ moves x)
    (counting : ∀ x,
      count x = (if goer x then 1 else 0) + (if moves x then 1 else 0))
    {x : A} (hm : moves x) : count x = 2 := by
  have hg : goer x := (same x).mpr hm
  simp [counting, hg, hm]

end BuddhistComparativeLogic.Gamana
