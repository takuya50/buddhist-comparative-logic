/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.MVLogic
import Lean.Elab.Tactic.Omega

/-!
# Jizang's fourfold two truths

Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_Jizang.thy`.  The formulas grow at every tier,
while their values stabilize after the first application of excluded
middle in classical, FDE, and FDE5 semantics.
-/

namespace BuddhistComparativeLogic

open Fm TV4 TV5

def jzConv (A : Fm α) : Nat → Fm α
  | 0 => A
  | n + 1 => disj (jzConv A n) (neg (jzConv A n))

def jzUlt (A : Fm α) (n : Nat) : Fm α := neg (jzConv A n)

theorem jz_conv_Suc_as_pair (A : Fm α) (n : Nat) :
    jzConv A (n + 1) = disj (jzConv A n) (jzUlt A n) := rfl

def fmSize : Fm α → Nat
  | .atom _ => 1
  | .neg x => fmSize x + 1
  | .conj x y => fmSize x + fmSize y + 1
  | .disj x y => fmSize x + fmSize y + 1

theorem jz_conv_size (A : Fm α) (n : Nat) :
    fmSize (jzConv A n) < fmSize (jzConv A (n + 1)) := by
  simp only [jzConv, fmSize]
  omega

theorem jz_conv_size_mono (A : Fm α) {n m : Nat} (h : n < m) :
    fmSize (jzConv A n) < fmSize (jzConv A m) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases heq : n = m
      · subst n
        exact jz_conv_size A m
      · have hnm : n < m := by omega
        exact Nat.lt_trans (ih hnm) (jz_conv_size A m)

theorem jz_tiers_distinct (A : Fm α) {n m : Nat} (h : n ≠ m) :
    jzUlt A n ≠ jzUlt A m := by
  intro heq
  have hc : jzConv A n = jzConv A m := Fm.neg.inj heq
  have hs := congrArg fmSize hc
  by_cases hnm : n < m
  · exact (Nat.ne_of_lt (jz_conv_size_mono A hnm)) hs
  · have hmn : m < n := by omega
    exact (Nat.ne_of_lt (jz_conv_size_mono A hmn)) hs.symm

abbrev ev2 (v : α → Bool) (A : Fm α) : Bool :=
  mvEval Bool.not Bool.and Bool.or v A

abbrev ev4 (v : α → TV4) (A : Fm α) : TV4 :=
  mvEval neg4 conj4 disj4 v A

abbrev ev5 (v : α → TV5) (A : Fm α) : TV5 :=
  mvEval neg5 conj5 disj5 v A

theorem cl_sat_ev2 (v : α → Bool) (X : Fm α) :
    mvClassical.sat v X ↔ ev2 v X = true := Iff.rfl

theorem fde_sat_ev4 (v : α → TV4) (X : Fm α) :
    mvFDE.sat v X ↔ tr (ev4 v X) = true := Iff.rfl

theorem fde5_sat_ev5 (v : α → TV5) (X : Fm α) :
    mvFDE5.sat v X ↔ des5 (ev5 v X) = true := Iff.rfl

theorem jz_cl_conv_valid (A : Fm α) (n : Nat) :
    mvClassical.valid (jzConv A (n + 1)) := by
  rw [MVLogic.valid_iff_all_sat]
  intro v
  change Bool.or (ev2 v (jzConv A n)) (Bool.not (ev2 v (jzConv A n))) = true
  cases ev2 v (jzConv A n) <;> rfl

theorem jz_cl_ult_unsat (v : α → Bool) (A : Fm α) (n : Nat) :
    ¬ mvClassical.sat v (jzUlt A (n + 1)) := by
  change ¬ Bool.not
    (Bool.or (ev2 v (jzConv A n)) (Bool.not (ev2 v (jzConv A n)))) = true
  cases ev2 v (jzConv A n) <;> decide

def lem4 (x : TV4) : TV4 := disj4 x (neg4 x)

def lem5 (x : TV5) : TV5 := disj5 x (neg5 x)

theorem lem4_T : lem4 T = T := rfl
theorem lem4_F : lem4 F = T := rfl
theorem lem4_B : lem4 B = B := rfl
theorem lem4_N : lem4 N = N := rfl

theorem lem4_idem (x : TV4) : lem4 (lem4 x) = lem4 x := by
  cases x <;> rfl

theorem lem5_fin (x : TV4) : lem5 (TV5.fin x) = TV5.fin (lem4 x) := rfl

theorem lem5_E : lem5 TV5.E = TV5.E := rfl

theorem lem5_idem (x : TV5) : lem5 (lem5 x) = lem5 x := by
  cases x with
  | fin y => cases y <;> rfl
  | E => rfl

theorem ev4_conv_Suc (v : α → TV4) (A : Fm α) (n : Nat) :
    ev4 v (jzConv A (n + 1)) = lem4 (ev4 v (jzConv A n)) := rfl

theorem ev5_conv_Suc (v : α → TV5) (A : Fm α) (n : Nat) :
    ev5 v (jzConv A (n + 1)) = lem5 (ev5 v (jzConv A n)) := rfl

theorem jz_fde_stabilizes (v : α → TV4) (A : Fm α) (n : Nat) :
    ev4 v (jzConv A (n + 1)) = lem4 (ev4 v A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ev4_conv_Suc, ih, lem4_idem]

theorem jz_fde5_stabilizes (v : α → TV5) (A : Fm α) (n : Nat) :
    ev5 v (jzConv A (n + 1)) = lem5 (ev5 v A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ev5_conv_Suc, ih, lem5_idem]

theorem jz_fde_ult_stabilizes (v : α → TV4) (A : Fm α) (n : Nat) :
    ev4 v (jzUlt A (n + 1)) = neg4 (lem4 (ev4 v A)) := by
  change neg4 (ev4 v (jzConv A (n + 1))) = _
  rw [jz_fde_stabilizes]

theorem jz_fde5_ult_stabilizes (v : α → TV5) (A : Fm α) (n : Nat) :
    ev5 v (jzUlt A (n + 1)) = neg5 (lem5 (ev5 v A)) := by
  change neg5 (ev5 v (jzConv A (n + 1))) = _
  rw [jz_fde5_stabilizes]

theorem jz_fde_fixed_points (v : α → TV4) (a : α) (n : Nat) :
    ((v a = T ∨ v a = F) →
      ev4 v (jzConv (atom a) (n + 1)) = T ∧
        ev4 v (jzUlt (atom a) (n + 1)) = F) ∧
    (v a = B → ev4 v (jzConv (atom a) (n + 1)) = B ∧
      ev4 v (jzUlt (atom a) (n + 1)) = B) ∧
    (v a = N → ev4 v (jzConv (atom a) (n + 1)) = N ∧
      ev4 v (jzUlt (atom a) (n + 1)) = N) := by
  constructor
  · intro h
    rcases h with h | h
    · constructor
      · rw [jz_fde_stabilizes]
        change lem4 (v a) = T
        rw [h]
        rfl
      · rw [jz_fde_ult_stabilizes]
        change neg4 (lem4 (v a)) = F
        rw [h]
        rfl
    · constructor
      · rw [jz_fde_stabilizes]
        change lem4 (v a) = T
        rw [h]
        rfl
      · rw [jz_fde_ult_stabilizes]
        change neg4 (lem4 (v a)) = F
        rw [h]
        rfl
  · constructor
    · intro h
      constructor
      · rw [jz_fde_stabilizes]
        change lem4 (v a) = B
        rw [h]
        rfl
      · rw [jz_fde_ult_stabilizes]
        change neg4 (lem4 (v a)) = B
        rw [h]
        rfl
    · intro h
      constructor
      · rw [jz_fde_stabilizes]
        change lem4 (v a) = N
        rw [h]
        rfl
      · rw [jz_fde_ult_stabilizes]
        change neg4 (lem4 (v a)) = N
        rw [h]
        rfl

theorem jz_fde5_ineffable_fixed_point (v : α → TV5) (a : α) (n : Nat)
    (h : v a = TV5.E) :
    ev5 v (jzConv (atom a) (n + 1)) = TV5.E ∧
      ev5 v (jzUlt (atom a) (n + 1)) = TV5.E := by
  constructor
  · rw [jz_fde5_stabilizes]
    change lem5 (v a) = TV5.E
    rw [h]
    rfl
  · rw [jz_fde5_ult_stabilizes]
    change neg5 (lem5 (v a)) = TV5.E
    rw [h]
    rfl

theorem jz_tiers_same_designation_fde
    (v : α → TV4) (A : Fm α) (n m : Nat) :
    mvFDE.sat v (jzUlt A (n + 1)) ↔ mvFDE.sat v (jzUlt A (m + 1)) := by
  change tr (ev4 v (jzUlt A (n + 1))) = true ↔
    tr (ev4 v (jzUlt A (m + 1))) = true
  rw [jz_fde_ult_stabilizes, jz_fde_ult_stabilizes]

theorem jz_tiers_same_designation_fde5
    (v : α → TV5) (A : Fm α) (n m : Nat) :
    mvFDE5.sat v (jzUlt A (n + 1)) ↔ mvFDE5.sat v (jzUlt A (m + 1)) := by
  change des5 (ev5 v (jzUlt A (n + 1))) = true ↔
    des5 (ev5 v (jzUlt A (m + 1))) = true
  rw [jz_fde5_ult_stabilizes, jz_fde5_ult_stabilizes]

def jzNeither (v : α → TV4) (A : Fm α) (n : Nat) : Prop :=
  ¬ mvFDE.sat v (jzConv A n) ∧ ¬ mvFDE.sat v (jzUlt A n)

theorem jz_neither_stabilizes (v : α → TV4) (A : Fm α) (n : Nat) :
    jzNeither v A (n + 1) ↔ ev4 v A = N := by
  rw [jzNeither]
  change
    (¬ tr (ev4 v (jzConv A (n + 1))) = true ∧
      ¬ tr (ev4 v (jzUlt A (n + 1))) = true) ↔ ev4 v A = N
  rw [jz_fde_stabilizes, jz_fde_ult_stabilizes]
  cases ev4 v A <;> decide

theorem jizang_ladder_is_not_truth_functional
    (u : α → Bool) (v : α → TV4) (w : α → TV5)
    (A : Fm α) {n m : Nat} (h : n ≠ m) :
    jzUlt A (n + 1) ≠ jzUlt A (m + 1) ∧
    ev4 v (jzUlt A (n + 1)) = ev4 v (jzUlt A (m + 1)) ∧
    ev5 w (jzUlt A (n + 1)) = ev5 w (jzUlt A (m + 1)) ∧
    ev2 u (jzUlt A (n + 1)) = ev2 u (jzUlt A (m + 1)) := by
  constructor
  · apply jz_tiers_distinct A
    omega
  · constructor
    · rw [jz_fde_ult_stabilizes, jz_fde_ult_stabilizes]
    · constructor
      · rw [jz_fde5_ult_stabilizes, jz_fde5_ult_stabilizes]
      · change Bool.not
          (Bool.or (ev2 u (jzConv A n)) (Bool.not (ev2 u (jzConv A n)))) =
          Bool.not
          (Bool.or (ev2 u (jzConv A m)) (Bool.not (ev2 u (jzConv A m))))
        cases ev2 u (jzConv A n) <;>
          cases ev2 u (jzConv A m) <;> rfl

end BuddhistComparativeLogic
