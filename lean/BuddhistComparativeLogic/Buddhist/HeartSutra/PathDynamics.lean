/- SPDX-License-Identifier: Apache-2.0 -/

import Lean.Elab.Tactic.Omega

/-!
# A conditional, quantitative path model

Lean-only extension. Insight, grasping, fear and suffering are independent
observations on a state. The natural numbers are abstract ranks, not measured
psychological quantities. Update laws are explicit modeling hypotheses;
they are not consequences of the sutra or empirical evidence for it.

Persistent insight and unit contraction of grasping give a finite bound.
Fear and suffering may lag by one step each. The four hypotheses are audited
with countermodels, so the bound is not attributed to insight alone.
-/

namespace BuddhistComparativeLogic.PathDynamics

structure Process (S : Type u) where
  step : S → S
  insight : S → Prop
  grasp : S → Nat
  fear : S → Nat
  suffering : S → Nat

namespace Process

variable (P : Process S)

def run (s : S) : Nat → S
  | 0 => s
  | n + 1 => P.step (run s n)

def InsightPersists : Prop := ∀ s, P.insight s → P.insight (P.step s)
def GraspContracts : Prop :=
  ∀ s, P.insight s → P.grasp (P.step s) ≤ P.grasp s - 1
def FearTracks : Prop := ∀ s, P.insight s → P.fear (P.step s) ≤ P.grasp s
def SufferingTracks : Prop :=
  ∀ s, P.insight s → P.suffering (P.step s) ≤ P.fear s

structure Laws : Prop where
  persists : P.InsightPersists
  contracts : P.GraspContracts
  fear_tracks : P.FearTracks
  suffering_tracks : P.SufferingTracks

theorem run_of_fixed {s : S} (h : P.step s = s) (n : Nat) : P.run s n = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, h]

theorem insight_run (h : P.InsightPersists) {s : S} (hs : P.insight s) (n : Nat) :
    P.insight (P.run s n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact h _ ih

theorem grasp_bound (hp : P.InsightPersists) (hc : P.GraspContracts)
    {s : S} (hs : P.insight s) (n : Nat) :
    P.grasp (P.run s n) ≤ P.grasp s - n := by
  induction n with
  | zero => simp only [run, Nat.sub_zero, Nat.le_refl]
  | succ n ih =>
      have hd := hc (P.run s n) (P.insight_run hp hs n)
      change P.grasp (P.step (P.run s n)) ≤ P.grasp s - (n + 1)
      omega

theorem fear_bound (h : P.Laws) {s : S} (hs : P.insight s) (n : Nat) :
    P.fear (P.run s (n + 1)) ≤ P.grasp s - n := by
  exact Nat.le_trans (h.fear_tracks _ (P.insight_run h.persists hs n))
    (P.grasp_bound h.persists h.contracts hs n)

theorem suffering_bound (h : P.Laws) {s : S} (hs : P.insight s) (n : Nat) :
    P.suffering (P.run s (n + 2)) ≤ P.grasp s - n := by
  exact Nat.le_trans (h.suffering_tracks _ (P.insight_run h.persists hs (n + 1)))
    (P.fear_bound h hs n)

/-- All three ranks vanish permanently by initial grasping rank plus two.
No equivalence between the three observations was assumed. -/
theorem eventual_release (h : P.Laws) {s : S} (hs : P.insight s)
    (n : Nat) (hn : P.grasp s + 2 ≤ n) :
    P.grasp (P.run s n) = 0 ∧ P.fear (P.run s n) = 0 ∧
      P.suffering (P.run s n) = 0 := by
  have hg := P.grasp_bound h.persists h.contracts hs n
  have hf := P.fear_bound h hs (n - 1)
  have hd := P.suffering_bound h hs (n - 2)
  have h1 : n - 1 + 1 = n := by omega
  have h2 : n - 2 + 2 = n := by omega
  rw [h1] at hf
  rw [h2] at hd
  omega

end Process

open Process

/-- All combinations of the four coordinates are allowed. -/
structure State where
  insight : Bool
  grasp : Nat
  fear : Nat
  suffering : Nat
  deriving DecidableEq, Repr

def delayed : Process State where
  step s := if s.insight then
    ⟨true, s.grasp - 1, s.grasp, s.fear⟩ else s
  insight s := s.insight = true
  grasp := State.grasp
  fear := State.fear
  suffering := State.suffering

theorem delayed_laws : delayed.Laws := by
  constructor <;> intro s hs <;>
    simp_all [delayed]

theorem observations_independent (b : Bool) (g f d : Nat) :
    ∃ s, s.insight = b ∧ delayed.grasp s = g ∧ delayed.fear s = f ∧
      delayed.suffering s = d := ⟨⟨b, g, f, d⟩, rfl, rfl, rfl, rfl⟩

def start : State := ⟨true, 2, 3, 4⟩

/-- Insight need not eliminate any rank immediately, even with all laws. -/
theorem insight_with_suffering :
    delayed.insight start ∧ delayed.grasp start = 2 ∧
      delayed.fear start = 3 ∧ delayed.suffering start = 4 := ⟨rfl, rfl, rfl, rfl⟩

/-- A checked witness attaining the +2 bound; in particular, +1 cannot be
a universal bound for the same class of processes. -/
theorem two_step_lag_is_attained :
    delayed.suffering (delayed.run start (delayed.grasp start + 1)) = 1 ∧
    delayed.suffering (delayed.run start (delayed.grasp start + 2)) = 0 := by decide

/-- Even all four conditional laws say nothing about a state lacking
insight. The premise of eventual_release is indispensable as well. -/
theorem initial_insight_needed :
    delayed.Laws ∧ ¬ delayed.insight (⟨false, 1, 1, 1⟩ : State) ∧
    (∀ n, delayed.suffering (delayed.run ⟨false, 1, 1, 1⟩ n) = 1) := by
  refine ⟨delayed_laws, Bool.noConfusion, ?_⟩
  intro n
  rw [delayed.run_of_fixed (s := ⟨false, 1, 1, 1⟩) rfl n]
  rfl

/-! Each omitted update condition has a nonconvergent model satisfying the
other three. These establish necessity for a universal guarantee over this
class, not necessity along every individual successful trajectory. -/

def stalled : Process Unit where
  step := id
  insight _ := True
  grasp _ := 1
  fear _ := 1
  suffering _ := 1

theorem contraction_needed :
    stalled.InsightPersists ∧ stalled.FearTracks ∧ stalled.SufferingTracks ∧
    ¬ stalled.GraspContracts ∧ stalled.insight () ∧
    (∀ n, stalled.suffering (stalled.run () n) = 1) := by
  exact ⟨fun _ _ => trivial, fun _ _ => Nat.le_refl _,
    fun _ _ => Nat.le_refl _, fun h => by have := h () trivial; contradiction,
    trivial, fun _ => rfl⟩

def fearPersists : Process Unit where
  step := id
  insight _ := True
  grasp _ := 0
  fear _ := 1
  suffering _ := 1

theorem fear_bridge_needed :
    fearPersists.InsightPersists ∧ fearPersists.GraspContracts ∧
    fearPersists.SufferingTracks ∧ ¬ fearPersists.FearTracks ∧
    fearPersists.insight () ∧
    (∀ n, fearPersists.suffering (fearPersists.run () n) = 1) := by
  exact ⟨fun _ _ => trivial, fun _ _ => Nat.le_refl _,
    fun _ _ => Nat.le_refl _, fun h => by have := h () trivial; contradiction,
    trivial, fun _ => rfl⟩

def sufferingPersists : Process Unit where
  step := id
  insight _ := True
  grasp _ := 0
  fear _ := 0
  suffering _ := 1

theorem suffering_bridge_needed :
    sufferingPersists.InsightPersists ∧ sufferingPersists.GraspContracts ∧
    sufferingPersists.FearTracks ∧ ¬ sufferingPersists.SufferingTracks ∧
    sufferingPersists.insight () ∧
    (∀ n, sufferingPersists.suffering (sufferingPersists.run () n) = 1) := by
  exact ⟨fun _ _ => trivial, fun _ _ => Nat.le_refl _,
    fun _ _ => Nat.le_refl _, fun h => by have := h () trivial; contradiction,
    trivial, fun _ => rfl⟩

def insightLost : Process Bool where
  step _ := true
  insight s := s = false
  grasp s := if s then 0 else 1
  fear _ := 1
  suffering _ := 1

theorem persistence_needed :
    insightLost.GraspContracts ∧ insightLost.FearTracks ∧
    insightLost.SufferingTracks ∧ ¬ insightLost.InsightPersists ∧
    insightLost.insight false ∧
    (∀ n, insightLost.suffering (insightLost.run false n) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, fun _ => rfl⟩
  · intro s hs
    cases hs
    decide
  · intro s hs
    cases hs
    decide
  · exact fun _ _ => Nat.le_refl _
  · intro h
    have bad : true = false := h false rfl
    cases bad

end BuddhistComparativeLogic.PathDynamics
