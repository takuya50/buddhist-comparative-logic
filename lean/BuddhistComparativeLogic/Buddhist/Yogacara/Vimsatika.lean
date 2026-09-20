/- SPDX-License-Identifier: Apache-2.0 -/

import Std

/-!
# Vasubandhu's Viṃśatikā

The first part supplies appearance-only models for the four adequacy
conditions.  The second states the partless-atom dilemma using predicate
sets, so it needs no external set library.
-/

namespace BuddhistComparativeLogic.Vimsatika

structure Vijnapti (S : Type u) (P : Type v) (T : Type w) where
  appears : S → P → T → Prop
  effective : S → P → T → Prop

namespace Vijnapti

variable {S : Type u} {P : Type v} {T : Type w} (m : Vijnapti S P T)

def desaniyama : Prop :=
  ∀ s t, (∃ p, m.appears s p t) → ∃ p', ¬ m.appears s p' t

def kalaniyama : Prop :=
  ∀ s p, (∃ t, m.appears s p t) → ∃ t', ¬ m.appears s p t'

def samtanaAniyama : Prop :=
  ∃ s s' p t, s ≠ s' ∧ m.appears s p t ∧ m.appears s' p t

def krtyakriya : Prop :=
  ∀ s p t, m.appears s p t → m.effective s p t

def adequate : Prop :=
  m.desaniyama ∧ m.kalaniyama ∧ m.samtanaAniyama ∧ m.krtyakriya

end Vijnapti

inductive Person where
  | alpha | beta | gamma
  deriving DecidableEq, Repr

inductive Place where
  | here | there
  deriving DecidableEq, Repr

inductive Moment where
  | now | later
  deriving DecidableEq, Repr

open Person Place Moment

def dreamApp (s : Person) (p : Place) (t : Moment) : Prop :=
  s = .alpha ∧ p = .here ∧ t = .now

def narakaApp (_ : Person) (p : Place) (t : Moment) : Prop :=
  p = .here ∧ t = .now

def dream : Vijnapti Person Place Moment where
  appears := dreamApp
  effective := dreamApp

def naraka : Vijnapti Person Place Moment where
  appears := narakaApp
  effective := narakaApp

theorem dream_meets_three :
    dream.desaniyama ∧ dream.kalaniyama ∧ dream.krtyakriya := by
  constructor
  · intro s t _
    exact ⟨.there, by simp [dream, dreamApp]⟩
  constructor
  · intro s p _
    exact ⟨.later, by simp [dream, dreamApp]⟩
  · intro s p t h
    exact h

theorem dream_lacks_intersubjectivity : ¬ dream.samtanaAniyama := by
  rintro ⟨s, s', p, t, hne, hs, hs'⟩
  have hsa : s = .alpha := hs.1
  have hsa' : s' = .alpha := hs'.1
  exact hne (hsa.trans hsa'.symm)

theorem dream_not_adequate : ¬ dream.adequate := by
  intro h
  exact dream_lacks_intersubjectivity h.2.2.1

theorem naraka_meets_all_four : naraka.adequate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t _
    exact ⟨.there, by simp [naraka, narakaApp]⟩
  · intro s p _
    exact ⟨.later, by simp [naraka, narakaApp]⟩
  · exact ⟨.alpha, .beta, .here, .now, by decide,
      by simp [naraka, narakaApp], by simp [naraka, narakaApp]⟩
  · intro s p t h
    exact h

theorem vijnaptimatra_is_consistent_with_the_four_conditions :
    ∃ A E : Person → Place → Moment → Prop,
      (Vijnapti.mk A E).adequate :=
  ⟨narakaApp, narakaApp, naraka_meets_all_four⟩

/-! ## The atomism dilemma -/

abbrev PredSet (α : Type u) := α → Prop

def partlessContact (pos : A → P) (contact : A → A → Prop) : Prop :=
  ∀ x y, contact x y → pos x = pos y

def hasExtension (pos : A → P) (S : PredSet A) : Prop :=
  ∃ x, S x ∧ ∃ y, S y ∧ pos x ≠ pos y

def clustered (contact : A → A → Prop) (c : A) (S : PredSet A) : Prop :=
  ∀ x, S x → contact c x

theorem six_directions_collapse
    (pl : partlessContact pos contact) (cl : clustered contact c S) :
    ∀ x, S x → pos x = pos c := by
  intro x hx
  exact (pl c x (cl x hx)).symm

theorem atomism_dilemma
    (pl : partlessContact pos contact)
    (cl : clustered contact c S) :
    ¬ hasExtension pos S := by
  rintro ⟨x, hx, y, hy, hxy⟩
  have hxc := six_directions_collapse pl cl x hx
  have hyc := six_directions_collapse pl cl y hy
  exact hxy (hxc.trans hyc.symm)

theorem extension_needs_parts
    (cl : clustered contact c S) (ext : hasExtension pos S) :
    ¬ partlessContact pos contact := by
  intro pl
  exact atomism_dilemma pl cl ext

def twoAtoms : Bool → Place
  | true => .here
  | false => .there

theorem dilemma_horns_are_both_realized :
    partlessContact (fun _ : Bool => Place.here) (fun _ _ => True) ∧
      ¬ partlessContact twoAtoms (fun _ _ => True) ∧
      hasExtension twoAtoms (fun _ => True) := by
  constructor
  · intro x y _
    rfl
  constructor
  · intro h
    have heq := h true false trivial
    cases heq
  · exact ⟨true, trivial, false, trivial, by decide⟩

end BuddhistComparativeLogic.Vimsatika
