/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang.CognitiveAntidote
import BuddhistComparativeLogic.Core.FDECalculus

/-!
# Deriving the form of Jizang's tier antidote

The cognitive model explains when a remedy is applied.  This module first
models the two members of a tier as the current attachment focus.  The
conventional part of an adequate response must be a least common consequence
of that focus, while the ultimate part must be interderivable with its
negation.  The FDE derivation rules then select `Antidote.tstep` up to
derivability, rather than assuming its two syntax-tree fields outright.

A final canonical-form specification selects the existing syntax tree exactly.
Finite counterexamples show that its two normalization conditions are
independent.
-/

namespace BuddhistComparativeLogic.AntidoteSelection

open Fm Antidote

open BuddhistComparativeLogic.FDECalculus

/-! ## Attachment-driven selection up to derivability -/

/-- The live propositional focus of a tier consists of its conventional and
ultimate assertions.  This is a non-truth-functional attitude: it records
which assertions are being held, independently of their FDE values. -/
def InAttachmentFocus (t : Tier α) (X : Fm α) : Prop :=
  X = t.1 ∨ X = t.2

/-- A formula is a common consequence of everything in the current focus. -/
def CoversAttachmentFocus (t : Tier α) (X : Fm α) : Prop :=
  ∀ Y, InAttachmentFocus t Y → Deriv Y X

/-- `X` is a least common consequence of the focus.  The second field rules
out an arbitrary weakening: every other common consequence follows from X. -/
structure LeastFocusConsequence (t : Tier α) (X : Fm α) : Prop where
  covers : CoversAttachmentFocus t X
  least : ∀ Z, CoversAttachmentFocus t Z → Deriv X Z

/-- Adequacy conditions stated at the level of inference rather than syntax.
The response gathers the whole attachment focus and then reverses that
gathering at the ultimate standpoint. -/
structure AttachmentResponse (t response : Tier α) : Prop where
  conventional : LeastFocusConsequence t response.1
  ultimateForward : Deriv response.2 (.neg response.1)
  ultimateBackward : Deriv (.neg response.1) response.2

theorem disjunction_covers_focus (t : Tier α) :
    CoversAttachmentFocus t (.disj t.1 t.2) := by
  intro X hX
  rcases hX with rfl | rfl
  · exact .disjI1 _ _
  · exact .disjI2 _ _

theorem disjunction_is_least_focus_consequence (t : Tier α) :
    LeastFocusConsequence t (.disj t.1 t.2) := by
  refine ⟨disjunction_covers_focus t, ?_⟩
  intro Z hZ
  exact .disjE (hZ t.1 (Or.inl rfl)) (hZ t.2 (Or.inr rfl))

theorem tstep_is_attachment_response (t : Tier α) :
    AttachmentResponse t (tstep t) := by
  exact ⟨disjunction_is_least_focus_consequence t, .ax _, .ax _⟩

/-- Leastness derives the conventional half of every adequate response up to
mutual derivability with the disjunction used by `tstep`. -/
theorem adequate_conventional_iff_tstep
    {t response : Tier α} (h : AttachmentResponse t response) :
    Deriv response.1 (tstep t).1 ∧ Deriv (tstep t).1 response.1 := by
  constructor
  · exact h.conventional.least _ (disjunction_covers_focus t)
  · exact .disjE
      (h.conventional.covers t.1 (Or.inl rfl))
      (h.conventional.covers t.2 (Or.inr rfl))

/-- The reversal condition and contraposition derive the ultimate half too.
Thus the attachment account determines the remedy modulo the proof theory;
the later canonical specification merely chooses one concrete syntax tree. -/
theorem attachment_account_selects_tstep_up_to_derivability
    {t response : Tier α} (h : AttachmentResponse t response) :
    (Deriv response.1 (tstep t).1 ∧ Deriv (tstep t).1 response.1) ∧
      (Deriv response.2 (tstep t).2 ∧ Deriv (tstep t).2 response.2) := by
  have hc := adequate_conventional_iff_tstep h
  constructor
  · exact hc
  · constructor
    · exact .cut h.ultimateForward (deriv_contraposition hc.2)
    · exact .cut (deriv_contraposition hc.1) h.ultimateBackward

/-- When the cognitive gate is open, both members of the tier are active
attachment targets, so the derived response applies to the state selected by
the belief model. -/
def CognitivelyFocused (belief : CognitiveAntidote.TierBelief α)
    (t : Tier α) (X : Fm α) : Prop :=
  belief.AcceptsIntrinsicTruth t ∧ InAttachmentFocus t X

theorem open_gate_focuses_both
    (belief : CognitiveAntidote.TierBelief α) (t : Tier α)
    (openGate : belief.gate t = true) :
    CognitivelyFocused belief t t.1 ∧ CognitivelyFocused belief t t.2 := by
  have accepts := (belief.gate_true_iff_accepts t).mp openGate
  exact ⟨⟨accepts, Or.inl rfl⟩, ⟨accepts, Or.inr rfl⟩⟩

/-! ## Canonical syntax-tree representative -/

def GathersPrevious (remedy : Tier α → Tier α) : Prop :=
  ∀ t, (remedy t).1 = .disj t.1 t.2

def UltimateDeniesGathering (remedy : Tier α → Tier α) : Prop :=
  ∀ t, (remedy t).2 = .neg (remedy t).1

structure ContentSpecification (remedy : Tier α → Tier α) : Prop where
  gathers : GathersPrevious remedy
  denies : UltimateDeniesGathering remedy

theorem tstep_content_specification :
    ContentSpecification (@tstep α) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem content_specification_unique
    {remedy : Tier α → Tier α} (h : ContentSpecification remedy) :
    remedy = tstep := by
  funext t
  apply Prod.ext
  · exact h.gathers t
  · rw [h.denies t, h.gathers t]
    rfl

theorem selected_remedy_is_tstep (remedy : Tier α → Tier α) :
    ContentSpecification remedy ↔ remedy = tstep := by
  constructor
  · exact content_specification_unique
  · rintro rfl
    exact tstep_content_specification

def gatherOnly (t : Tier α) : Tier α :=
  (.disj t.1 t.2, t.2)

def denyFirst (t : Tier α) : Tier α :=
  (t.1, .neg t.1)

theorem gathering_does_not_force_ultimate_denial :
    GathersPrevious (@gatherOnly Bool) ∧
      ¬ UltimateDeniesGathering (@gatherOnly Bool) := by
  constructor
  · intro t
    rfl
  · intro h
    have bad := h (.atom true, .atom false)
    simp [gatherOnly] at bad

theorem ultimate_denial_does_not_force_gathering :
    UltimateDeniesGathering (@denyFirst Bool) ∧
      ¬ GathersPrevious (@denyFirst Bool) := by
  constructor
  · intro t
    rfl
  · intro h
    have bad := h (.atom true, .atom false)
    simp [denyFirst] at bad

def runWith (remedy : Tier α → Tier α) (gate : Tier α → Bool)
    (t : Tier α) : Nat → Tier α
  | 0 => t
  | n + 1 => if gate (runWith remedy gate t n) then
      remedy (runWith remedy gate t n) else runWith remedy gate t n

/-- Once both content conditions and a cognitive gate are supplied, the
generated trajectory is definitionally the existing antidote trajectory. -/
theorem specified_gated_run
    (remedy : Tier α → Tier α) (spec : ContentSpecification remedy)
    (belief : CognitiveAntidote.TierBelief α) (t : Tier α) (n : Nat) :
    runWith remedy belief.gate t n = Antidote.run belief.gate t n := by
  have selected : remedy = tstep := content_specification_unique spec
  subst remedy
  induction n with
  | zero => rfl
  | succ n ih => simp only [runWith, Antidote.run, ih]

end BuddhistComparativeLogic.AntidoteSelection
