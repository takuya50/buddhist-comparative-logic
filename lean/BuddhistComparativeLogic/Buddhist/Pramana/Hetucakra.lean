/- SPDX-License-Identifier: Apache-2.0 -/

import Std

/-!
# Dignāga's wheel of reasons

A bare Lean port of `isabelle/Buddhist/Pramana/Dignaga_Hetucakra.thy`.  The object-language predicates are
`Prop`-valued; this makes explicit a distinction that Isabelle/HOL's `bool`
type leaves implicit.
-/

namespace BuddhistComparativeLogic.Hetucakra

inductive Extent where
  | all | none | some
  deriving DecidableEq, Repr

inductive Verdict where
  | valid | contradictory | inconclusive
  deriving DecidableEq, Repr

open Extent Verdict

def hetucakra : Extent → Extent → Verdict
  | .all,  .none => .valid
  | .some, .none => .valid
  | .none, .all  => .contradictory
  | .none, .some => .contradictory
  | _, _ => .inconclusive

def wheel : List (Extent × Extent) :=
  [.all, .none, .some].flatMap fun s =>
    [.all, .none, .some].map fun v => (s, v)

theorem wheel_nine : wheel.length = 9 := by decide

theorem wheel_distinct : wheel.Pairwise (· ≠ ·) := by decide

theorem wheel_verdicts :
    wheel.map (fun p => hetucakra p.1 p.2) =
      [.inconclusive, .valid, .inconclusive,
       .contradictory, .inconclusive, .contradictory,
       .inconclusive, .valid, .inconclusive] := by
  decide

theorem valid_iff (s v : Extent) :
    hetucakra s v = .valid ↔ v = .none ∧ s ≠ .none := by
  cases s <;> cases v <;> decide

theorem contradictory_iff (s v : Extent) :
    hetucakra s v = .contradictory ↔ s = .none ∧ v ≠ .none := by
  cases s <;> cases v <;> decide

/-! ## The three marks -/

structure Anumana (L : Type u) where
  paksa : L
  sadhya : L → Prop
  reason : L → Prop

namespace Anumana

variable {L : Type u} (a : Anumana L)

abbrev PredSet (L : Type u) := L → Prop

def sapaksa : PredSet L := fun x => x ≠ a.paksa ∧ a.sadhya x

def vipaksa : PredSet L := fun x => x ≠ a.paksa ∧ ¬ a.sadhya x

noncomputable def extentOf (S : PredSet L) : Extent := by
  classical
  exact if (∃ x, S x ∧ a.reason x) then
      if (∀ x, S x → a.reason x) then .all else .some
    else .none

noncomputable def wheelVerdict : Verdict :=
  hetucakra (a.extentOf a.sapaksa) (a.extentOf a.vipaksa)

def paksadharmata : Prop := a.reason a.paksa

def anvaya : Prop := ∃ x, a.sapaksa x ∧ a.reason x

def vyatireka : Prop := ∀ x, a.vipaksa x → ¬ a.reason x

def trairupya : Prop := a.paksadharmata ∧ a.anvaya ∧ a.vyatireka

theorem extent_none_iff (S : PredSet L) :
    a.extentOf S = .none ↔ ∀ x, S x → ¬ a.reason x := by
  classical
  constructor
  · intro heq x hx hr
    have hex : ∃ y, S y ∧ a.reason y := ⟨x, hx, hr⟩
    unfold extentOf at heq
    rw [if_pos hex] at heq
    by_cases hAll : ∀ y, S y → a.reason y
    · rw [if_pos hAll] at heq
      cases heq
    · rw [if_neg hAll] at heq
      cases heq
  · intro hall
    have hnex : ¬ ∃ x, S x ∧ a.reason x := by
      rintro ⟨x, hx, hr⟩
      exact hall x hx hr
    simp [extentOf, hnex]

theorem extent_not_none_iff (S : PredSet L) :
    a.extentOf S ≠ .none ↔ ∃ x, S x ∧ a.reason x := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ x, S x ∧ a.reason x
    · exact hex
    · apply False.elim
      apply h
      rw [a.extent_none_iff]
      intro x hx hreason
      exact hex ⟨x, hx, hreason⟩
  · rintro ⟨x, hx, hr⟩ heq
    have hall := (extent_none_iff a S).mp heq
    exact hall x hx hr

theorem wheel_valid_iff :
    a.wheelVerdict = .valid ↔ a.anvaya ∧ a.vyatireka := by
  classical
  rw [wheelVerdict, valid_iff, extent_none_iff, extent_not_none_iff]
  exact and_comm

theorem wheel_contradictory_iff :
    a.wheelVerdict = .contradictory ↔
      (∀ x, a.sapaksa x → ¬ a.reason x) ∧
      (∃ x, a.vipaksa x ∧ a.reason x) := by
  classical
  simp only [wheelVerdict, contradictory_iff, a.extent_none_iff,
    a.extent_not_none_iff]

theorem vyatireka_gives_vyapti_off_paksa
    (h : a.vyatireka) :
    ∀ x, x ≠ a.paksa → a.reason x → a.sadhya x := by
  intro x hx hH
  apply Classical.byContradiction
  intro hS
  exact (show ∀ y, a.vipaksa y → ¬ a.reason y from h) x ⟨hx, hS⟩ hH

theorem contradictory_indicates_absence
    (h : a.wheelVerdict = .contradictory) :
    ∀ x, x ≠ a.paksa → a.reason x → ¬ a.sadhya x := by
  have hs := (a.wheel_contradictory_iff.mp h).1
  intro x hx hH hS
  exact hs x ⟨hx, hS⟩ hH

theorem sound_under_uniformity
    (marks : a.trairupya)
    (uniformity :
      (∀ x, x ≠ a.paksa → a.reason x → a.sadhya x) →
        a.reason a.paksa → a.sadhya a.paksa) :
    a.sadhya a.paksa := by
  exact uniformity (a.vyatireka_gives_vyapti_off_paksa marks.2.2) marks.1

end Anumana

/-! ## Finite examples -/

inductive Locus where
  | mountain | kitchen | lake
  deriving DecidableEq, Repr

open Locus

def smoke : Anumana Locus where
  paksa := .mountain
  sadhya := fun x => x ≠ .lake
  reason := fun x => x ≠ .lake

theorem smoke_valid : smoke.wheelVerdict = .valid := by
  rw [smoke.wheel_valid_iff]
  constructor
  · exact ⟨.kitchen, ⟨by simp [smoke], by simp [smoke]⟩,
      by simp [smoke]⟩
  · intro x hx hH
    change x ≠ .mountain ∧ ¬ x ≠ .lake at hx
    change x ≠ .lake at hH
    exact hx.2 hH

def nofire : Anumana Locus where
  paksa := .mountain
  sadhya := fun x => x = .kitchen
  reason := fun x => x ≠ .lake

theorem no_deductive_soundness :
    nofire.trairupya ∧ nofire.wheelVerdict = .valid ∧
      ¬ nofire.sadhya .mountain := by
  have hanv : nofire.anvaya :=
    ⟨.kitchen, ⟨by decide, rfl⟩, by simp [nofire]⟩
  have hvya : nofire.vyatireka := by
    intro x hx
    rcases hx with ⟨_, hnot⟩
    cases x <;> simp_all [nofire]
  exact ⟨⟨by simp [Anumana.paksadharmata, nofire], hanv, hvya⟩,
    nofire.wheel_valid_iff.mpr ⟨hanv, hvya⟩, by simp [nofire]⟩

inductive Thing where
  | sound | space | pot
  deriving DecidableEq, Repr

def audible : Anumana Thing where
  paksa := .sound
  sadhya := fun x => x = .space
  reason := fun x => x = .sound

theorem audible_inconclusive : audible.wheelVerdict = .inconclusive := by
  classical
  have hs : audible.extentOf audible.sapaksa = .none := by
    rw [Anumana.extent_none_iff]
    intro x hx hr
    exact hx.1 hr
  have hv : audible.extentOf audible.vipaksa = .none := by
    rw [Anumana.extent_none_iff]
    intro x hx hr
    exact hx.1 hr
  simp [Anumana.wheelVerdict, hs, hv, hetucakra]

end BuddhistComparativeLogic.Hetucakra
