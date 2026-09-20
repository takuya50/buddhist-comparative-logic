/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation

/-!
# Generic many-valued propositional logic

Lean counterpart of `isabelle/Core/ManyValuedLogic.thy`.  The carrier and its designated
values are explicit data, mirroring an Isabelle locale without committing
the rest of the development to a global type-class instance.
-/

namespace BuddhistComparativeLogic

open Fm

/-- Evaluate a formula with explicitly supplied truth operations. -/
def mvEval (neg : V → V) (mconj mdisj : V → V → V)
    (v : α → V) : Fm α → V
  | .atom a => v a
  | .neg A => neg (mvEval neg mconj mdisj v A)
  | .conj A B => mconj (mvEval neg mconj mdisj v A)
      (mvEval neg mconj mdisj v B)
  | .disj A B => mdisj (mvEval neg mconj mdisj v A)
      (mvEval neg mconj mdisj v B)

/-- The data and two non-triviality conditions of Isabelle's `mv_logic`.

`designated` is represented as a predicate, so this module needs neither
`Set` nor Mathlib.  Keeping a logic explicit is important: FDE5 has two
different designation policies on the same carrier.
-/
structure MVLogic (V : Type u) where
  designated : V → Prop
  neg : V → V
  mconj : V → V → V
  mdisj : V → V → V
  designated_nonempty : ∃ x, designated x
  designated_proper : ∃ x, ¬ designated x

namespace MVLogic

variable (L : MVLogic V)

/-- A theory is a predicate on formulas, i.e. a set without a library
dependency. -/
abbrev Theory (α : Type) := Fm α → Prop

def eval (v : α → V) (A : Fm α) : V :=
  mvEval L.neg L.mconj L.mdisj v A

def sat (v : α → V) (A : Fm α) : Prop :=
  L.designated (L.eval v A)

def entails (Γ : Theory α) (A : Fm α) : Prop :=
  ∀ v, (∀ B, Γ B → L.sat v B) → L.sat v A

def imp (_L : MVLogic V) (A B : Fm α) : Fm α :=
  Fm.disj (Fm.neg A) B

def iffFm (L : MVLogic V) (A B : Fm α) : Fm α :=
  Fm.conj (L.imp A B) (L.imp B A)

theorem eval_iff_fm (v : α → V) (A B : Fm α) :
    L.eval v (L.iffFm A B) =
      L.mconj (L.eval v (L.imp A B)) (L.eval v (L.imp B A)) := by
  rfl

def valid (A : Fm α) : Prop :=
  L.entails (fun _ => False) A

theorem entails_refl {Γ : Theory α} {A : Fm α} (hA : Γ A) :
    L.entails Γ A := by
  intro v hΓ
  exact hΓ A hA

theorem entails_mono {Γ Δ : Theory α} {A : Fm α}
    (hsub : ∀ {B}, Γ B → Δ B) (h : L.entails Γ A) :
    L.entails Δ A := by
  intro v hΔ
  exact h v (fun B hB => hΔ B (hsub hB))

theorem entails_cut {Γ : Theory α} {A B : Fm α}
    (hA : L.entails Γ A)
    (hB : L.entails (fun X => X = A ∨ Γ X) B) :
    L.entails Γ B := by
  intro v hΓ
  apply hB v
  intro X hX
  cases hX with
  | inl hEq =>
      cases hEq
      exact hA v hΓ
  | inr hXΓ => exact hΓ X hXΓ

theorem valid_iff_all_sat {A : Fm α} :
    L.valid A ↔ ∀ v, L.sat v A := by
  constructor
  · intro h v
    exact h v (fun _ hFalse => False.elim hFalse)
  · intro h v _
    exact h v

end MVLogic

/-! ## Concrete records used by the locale-style ports

The truth operations themselves live in `BuddhistComparativeLogic.Core.Foundation`.  These records
package them with designation and its non-triviality witnesses.  In
particular `mvFDE5` and `mvFDE5D` deliberately share a carrier and differ
only on whether the ineffable value is designated.
-/

def mvClassical : MVLogic Bool where
  designated b := b = true
  neg := Bool.not
  mconj := Bool.and
  mdisj := Bool.or
  designated_nonempty := ⟨true, rfl⟩
  designated_proper := ⟨false, by decide⟩

def mvFDE : MVLogic TV4 where
  designated x := tr x = true
  neg := neg4
  mconj := conj4
  mdisj := disj4
  designated_nonempty := ⟨TV4.T, rfl⟩
  designated_proper := ⟨TV4.N, by decide⟩

def mvFDE5 : MVLogic TV5 where
  designated x := des5 x = true
  neg := neg5
  mconj := conj5
  mdisj := disj5
  designated_nonempty := ⟨TV5.fin TV4.T, rfl⟩
  designated_proper := ⟨TV5.E, by decide⟩

def mvFDE5D : MVLogic TV5 where
  designated x := des5D x = true
  neg := neg5
  mconj := conj5
  mdisj := disj5
  designated_nonempty := ⟨TV5.E, rfl⟩
  designated_proper := ⟨TV5.fin TV4.N, by decide⟩

end BuddhistComparativeLogic
