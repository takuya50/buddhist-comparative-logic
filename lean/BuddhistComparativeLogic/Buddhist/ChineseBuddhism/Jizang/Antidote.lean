/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang

/-!
# Attachment-gated iteration of Jizang's tiers

The central antidote dynamics, with an exact stopping criterion and an infinite-ascent
counterexample added in Lean. The operation on formulas remains stipulated.
Neither reduction of attachment nor silence follows merely from gating.
-/

namespace BuddhistComparativeLogic.Antidote

abbrev Tier (α : Type u) := Fm α × Fm α

def tstep (t : Tier α) : Tier α :=
  (.disj t.1 t.2, .neg (.disj t.1 t.2))

theorem fm_size_positive (A : Fm α) : 0 < fmSize A := by
  cases A <;> simp only [fmSize] <;> omega

theorem tstep_grows (t : Tier α) : fmSize t.1 < fmSize (tstep t).1 := by
  simp only [tstep, fmSize]
  omega

theorem tstep_ne (t : Tier α) : tstep t ≠ t := by
  intro h
  have hg := tstep_grows t
  rw [h] at hg
  exact Nat.lt_irrefl _ hg

/-- A decidable gate makes the iteration executable; the gate says where
attachment occurs, without yet explaining what attachment consists in. -/
def run (grasped : Tier α → Bool) (t : Tier α) : Nat → Tier α
  | 0 => t
  | n + 1 => if grasped (run grasped t n) then
      tstep (run grasped t n) else run grasped t n

theorem no_grasping_no_ascent (t : Tier α) (n : Nat) :
    run (fun _ => false) t n = t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, Bool.false_eq_true, ↓reduceIte, ih]

theorem ascent_stops_where_grasping_stops (g : Tier α → Bool) (t : Tier α)
    (n k : Nat) (h : g (run g t n) = false) :
    run g t (n + k) = run g t n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (if g (run g t (n + k)) then tstep (run g t (n + k))
        else run g t (n + k)) = run g t n
      rw [ih, h]
      rfl

theorem stops_iff_not_grasped (g : Tier α → Bool) (t : Tier α) (n : Nat) :
    run g t (n + 1) = run g t n ↔ g (run g t n) = false := by
  cases h : g (run g t n) with
  | false => simp [run, h]
  | true => simp [run, h, tstep_ne]

theorem run_is_jizang (A : Fm α) (n : Nat) :
    run (fun _ => true) (A, .neg A) n = (jzConv A n, jzUlt A n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [run, ↓reduceIte, ih]
      rfl

/-- Gating alone does not imply eventual cessation. -/
theorem perpetual_grasping_never_stops (t : Tier α) (n : Nat) :
    run (fun _ => true) t (n + 1) ≠ run (fun _ => true) t n := by
  exact tstep_ne _

def openingGrasp [DecidableEq α] (t : Tier α) (s : Tier α) : Bool := decide (s = t)

theorem one_grasp_one_tier [DecidableEq α] (t : Tier α) (n : Nat) :
    run (openingGrasp t) t (n + 1) = tstep t := by
  have hfirst : run (openingGrasp t) t 1 = tstep t := by
    simp [run, openingGrasp]
  have hstop : openingGrasp t (run (openingGrasp t) t 1) = false := by
    simp [hfirst, openingGrasp, tstep_ne]
  have h := ascent_stops_where_grasping_stops (openingGrasp t) t 1 n hstop
  simpa only [Nat.add_comm 1 n, hfirst] using h

/-- Agreement on the visited states is enough; no global equality of gates
is required. Unvisited attitudes do not affect this trajectory. -/
theorem run_eq_of_agree_on_trajectory (g h : Tier α → Bool) (t : Tier α)
    (agree : ∀ n, g (run g t n) = h (run g t n)) (n : Nat) :
    run g t n = run h t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [run, ← ih, agree n]

/-- Formula growth in the gated model does not undo the existing FDE
truth-value collapse. This is about evaluations, not equality of formulas. -/
theorem ascent_still_collapses_in_fde (v : α → TV4) (A : Fm α) (n m : Nat) :
    ev4 v (run (fun _ => true) (A, .neg A) (n + 1)).2 =
      ev4 v (run (fun _ => true) (A, .neg A) (m + 1)).2 := by
  rw [run_is_jizang, run_is_jizang]
  exact (jz_fde_ult_stabilizes v A n).trans (jz_fde_ult_stabilizes v A m).symm

end BuddhistComparativeLogic.Antidote
