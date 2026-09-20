/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.BeliefRevision
import BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang.Antidote
import Lean.Elab.Tactic.Omega

/-!
# A cognitive semantics for the Jizang antidote gate

The earlier attachment-gated iteration left its Boolean gate uninterpreted.
Here a tier is grasped exactly when support for treating it as intrinsically
true exceeds the admitted counterevidence.  This gives an exact cognitive
stopping criterion, while leaving the Jizang formula operation unchanged.

Uniform revision is also executable: each round adds one counterevidence unit
without changing support.  It contracts every tier's residual grasping and
closes a selected gate after its initial residual rank many rounds.
-/

namespace BuddhistComparativeLogic.CognitiveAntidote

open Antidote

/-- A non-truth-functional attitude toward every tier.  Two tiers with equal
FDE values may still receive different cognitive scores. -/
structure TierBelief (α : Type u) where
  ownSupport : Tier α → Nat
  emptinessEvidence : Tier α → Nat

namespace TierBelief

variable (B : TierBelief α)

def grasp (t : Tier α) : Nat := B.ownSupport t - B.emptinessEvidence t

def AcceptsIntrinsicTruth (t : Tier α) : Prop :=
  B.emptinessEvidence t < B.ownSupport t

/-- The previously abstract gate receives a cognitive interpretation. -/
def gate (t : Tier α) : Bool := decide (0 < B.grasp t)

theorem grasp_positive_iff_accepts (t : Tier α) :
    0 < B.grasp t ↔ B.AcceptsIntrinsicTruth t := by
  unfold grasp AcceptsIntrinsicTruth
  omega

theorem gate_true_iff_accepts (t : Tier α) :
    B.gate t = true ↔ B.AcceptsIntrinsicTruth t := by
  simp [gate, B.grasp_positive_iff_accepts]

theorem gate_false_iff_evidence_sufficient (t : Tier α) :
    B.gate t = false ↔ B.ownSupport t ≤ B.emptinessEvidence t := by
  unfold gate grasp
  simp only [decide_eq_false_iff_not]
  omega

/-- Add `n` admitted counterevidence units to every currently represented
tier while preserving its positive support. -/
def revise (n : Nat) : TierBelief α where
  ownSupport := B.ownSupport
  emptinessEvidence t := B.emptinessEvidence t + n

theorem grasp_after_revision (t : Tier α) (n : Nat) :
    (B.revise n).grasp t = B.grasp t - n := by
  unfold revise grasp
  rw [Nat.sub_sub]

theorem revision_add (m n : Nat) :
    (B.revise m).revise n = B.revise (m + n) := by
  cases B
  simp [revise, Nat.add_assoc]

/-- A single rational revision discharges the contraction premise pointwise;
there is no primitive grasp-contraction field in `TierBelief`. -/
theorem one_revision_contracts (t : Tier α) :
    (B.revise 1).grasp t ≤ B.grasp t - 1 := by
  rw [B.grasp_after_revision]
  exact Nat.le_refl _

theorem revision_closes_gate (t : Tier α) (n : Nat)
    (enough : B.ownSupport t ≤ B.emptinessEvidence t + n) :
    (B.revise n).gate t = false := by
  rw [(B.revise n).gate_false_iff_evidence_sufficient]
  exact enough

/-- The exact initial positive balance is always enough additional evidence
to close that tier's gate, including the already-closed case. -/
theorem residual_evidence_closes_gate (t : Tier α) :
    (B.revise (B.grasp t)).gate t = false := by
  apply B.revision_closes_gate
  unfold grasp
  omega

/-- The existing stop theorem becomes: the ascent stops exactly where admitted
counterevidence meets or exceeds own-being support. -/
theorem antidote_stops_iff_evidence_sufficient (t : Tier α) (n : Nat) :
    Antidote.run B.gate t (n + 1) = Antidote.run B.gate t n ↔
      B.ownSupport (Antidote.run B.gate t n) ≤
        B.emptinessEvidence (Antidote.run B.gate t n) := by
  rw [Antidote.stops_iff_not_grasped]
  exact B.gate_false_iff_evidence_sufficient _

/-- If a revision has already neutralized the opening tier, the first
antidote transition is stationary. -/
theorem sufficient_revision_stops_at_opening (t : Tier α) (n : Nat)
    (enough : B.ownSupport t ≤ B.emptinessEvidence t + n) :
    Antidote.run (B.revise n).gate t 1 = t := by
  have hGate : (B.revise n).gate t = false :=
    B.revision_closes_gate t n enough
  simp [Antidote.run, hGate]

theorem residual_revision_stops_at_opening (t : Tier α) :
    Antidote.run (B.revise (B.grasp t)).gate t 1 = t := by
  apply B.sufficient_revision_stops_at_opening
  unfold grasp
  omega

/-! ## Recovering and revising the existing one-tier example -/

/-- One unit of unsupported intrinsic commitment only at the opening tier. -/
def openingBelief [DecidableEq α] (t : Tier α) : TierBelief α where
  ownSupport u := if u = t then 1 else 0
  emptinessEvidence _ := 0

theorem opening_gate_eq [DecidableEq α] (t : Tier α) :
    (openingBelief t).gate = Antidote.openingGrasp t := by
  funext u
  by_cases h : u = t <;>
    simp [openingBelief, gate, grasp, Antidote.openingGrasp, h]

/-- Thus the old `openingGrasp` gate is a concrete one-point belief profile,
and its one-tier ascent theorem is inherited unchanged. -/
theorem opening_belief_one_tier [DecidableEq α] (t : Tier α) (n : Nat) :
    Antidote.run (openingBelief t).gate t (n + 1) = Antidote.tstep t := by
  rw [opening_gate_eq]
  exact Antidote.one_grasp_one_tier t n

/-- Assimilating one counterevidence unit neutralizes that entire opening
profile, so every gated iteration remains at its initial tier. -/
theorem revised_opening_belief_stops [DecidableEq α]
    (t : Tier α) (n : Nat) :
    Antidote.run ((openingBelief t).revise 1).gate t n = t := by
  have hGate : ((openingBelief t).revise 1).gate = fun _ => false := by
    funext u
    apply (openingBelief t).revision_closes_gate
    by_cases h : u = t <;> simp [openingBelief, h]
  rw [hGate]
  exact Antidote.no_grasping_no_ascent t n

end TierBelief

end BuddhistComparativeLogic.CognitiveAntidote
