/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.PathDynamics
import Lean.Elab.Tactic.Omega

/-!
# Evidence-sensitive belief revision

This Lean-only model separates support for own-being from counterevidence for
emptiness.  Grasping is the positive balance of the former over the latter.
Consequently, contraction is derived from three explicit update conditions:
support does not increase, admitted counterevidence is retained, and one new
unit is assimilated while the own-being belief is still accepted.

The natural-number scores are ordinal bookkeeping devices.  The theorems say
what follows from the stated update policy; they do not claim that people in
fact revise beliefs this way.  Countermodels record backfire, ignored evidence,
and relapse after forgetting.
-/

namespace BuddhistComparativeLogic.BeliefRevision

open PathDynamics

/-- A cognitive process keeps the two sides of an own-being judgment
separate.  Fear and suffering remain independent observations. -/
structure EvidenceProcess (S : Type u) where
  step : S → S
  insight : S → Prop
  ownSupport : S → Nat
  emptinessEvidence : S → Nat
  fear : S → Nat
  suffering : S → Nat

namespace EvidenceProcess

variable (E : EvidenceProcess S)

/-- Residual commitment to own-being after admitted counterevidence. -/
def grasp (s : S) : Nat := E.ownSupport s - E.emptinessEvidence s

/-- The qualitative belief accepted by a positive grasping balance. -/
def AcceptsOwnBeing (s : S) : Prop :=
  E.emptinessEvidence s < E.ownSupport s

theorem grasp_positive_iff_accepts (s : S) :
    0 < E.grasp s ↔ E.AcceptsOwnBeing s := by
  unfold grasp AcceptsOwnBeing
  omega

theorem no_grasp_iff_evidence_sufficient (s : S) :
    E.grasp s = 0 ↔ E.ownSupport s ≤ E.emptinessEvidence s := by
  unfold grasp
  omega

/-- Forgetting is excluded while insight is active. -/
def EvidenceRetained : Prop :=
  ∀ s, E.insight s →
    E.emptinessEvidence s ≤ E.emptinessEvidence (E.step s)

/-- Insight does not license manufacturing further support for own-being. -/
def SupportDisciplined : Prop :=
  ∀ s, E.insight s → E.ownSupport (E.step s) ≤ E.ownSupport s

/-- While the own-being belief remains positive, an insight step admits at
least one additional unit of counterevidence. -/
def ActiveAssimilation : Prop :=
  ∀ s, E.insight s → 0 < E.grasp s →
    E.emptinessEvidence s + 1 ≤ E.emptinessEvidence (E.step s)

/-- Conditions on the two belief coordinates, with no primitive contraction
assumption. -/
structure RationalRevision : Prop where
  support_disciplined : E.SupportDisciplined
  evidence_retained : E.EvidenceRetained
  active_assimilation : E.ActiveAssimilation

/-- Forgetting or renewed support is allowed outside insight episodes. -/
def InsightPersists : Prop :=
  ∀ s, E.insight s → E.insight (E.step s)

def FearFollowsGrasp : Prop :=
  ∀ s, E.insight s → E.fear (E.step s) ≤ E.grasp s

def SufferingFollowsFear : Prop :=
  ∀ s, E.insight s → E.suffering (E.step s) ≤ E.fear s

/-- Erase the explanatory belief coordinates and expose the observations
expected by the earlier quantitative path model. -/
def toPath : PathDynamics.Process S where
  step := E.step
  insight := E.insight
  grasp := E.grasp
  fear := E.fear
  suffering := E.suffering

/-- Unit contraction is now a consequence of rational revision.  The zero
case uses retention to prevent a settled belief from reopening during an
insight step. -/
theorem rational_revision_contracts (h : E.RationalRevision) :
    E.toPath.GraspContracts := by
  intro s hs
  change E.ownSupport (E.step s) - E.emptinessEvidence (E.step s) ≤
    (E.ownSupport s - E.emptinessEvidence s) - 1
  have hSupport := h.support_disciplined s hs
  have hRetained := h.evidence_retained s hs
  by_cases hPositive : 0 < E.grasp s
  · have hAssimilated := h.active_assimilation s hs hPositive
    unfold grasp at hPositive
    omega
  · unfold grasp at hPositive
    omega

/-- These premises imply the old path laws, but do not contain an assumed
`GraspContracts` field. -/
structure ReleaseConditions : Prop where
  rational : E.RationalRevision
  insight_persists : E.InsightPersists
  fear_follows : E.FearFollowsGrasp
  suffering_follows : E.SufferingFollowsFear

theorem path_laws_of_revision (h : E.ReleaseConditions) : E.toPath.Laws where
  persists := h.insight_persists
  contracts := E.rational_revision_contracts h.rational
  fear_tracks := h.fear_follows
  suffering_tracks := h.suffering_follows

/-- The finite release theorem is inherited after discharging its contraction
premise from belief revision. -/
theorem eventual_release_from_revision (h : E.ReleaseConditions)
    {s : S} (hs : E.insight s) (n : Nat) (hn : E.grasp s + 2 ≤ n) :
    E.grasp (E.toPath.run s n) = 0 ∧
      E.fear (E.toPath.run s n) = 0 ∧
      E.suffering (E.toPath.run s n) = 0 := by
  exact E.toPath.eventual_release (E.path_laws_of_revision h) hs n hn

end EvidenceProcess

open EvidenceProcess

/-! ## An executable calibrated updater -/

structure State where
  insight : Bool
  ownSupport : Nat
  emptinessEvidence : Nat
  fear : Nat
  suffering : Nat
  deriving DecidableEq, Repr

/-- During insight, support is frozen, one counterevidence unit is integrated,
and fear and suffering follow with one-step lags. -/
def calibrated : EvidenceProcess State where
  step s := if s.insight then
    ⟨true, s.ownSupport, s.emptinessEvidence + 1,
      s.ownSupport - s.emptinessEvidence, s.fear⟩
    else s
  insight s := s.insight = true
  ownSupport := State.ownSupport
  emptinessEvidence := State.emptinessEvidence
  fear := State.fear
  suffering := State.suffering

theorem calibrated_conditions : calibrated.ReleaseConditions := by
  refine
    { rational := ?_
      insight_persists := ?_
      fear_follows := ?_
      suffering_follows := ?_ }
  · constructor
    · intro s hs
      change s.insight = true at hs
      simp [calibrated, hs]
    · intro s hs
      change s.insight = true at hs
      simp [calibrated, hs]
    · intro s hs _
      change s.insight = true at hs
      simp [calibrated, hs]
  · intro s hs
    change s.insight = true at hs
    simp [calibrated, hs]
  · intro s hs
    change s.insight = true at hs
    simp [calibrated, grasp, hs]
  · intro s hs
    change s.insight = true at hs
    simp [calibrated, hs]

def calibratedStart : State := ⟨true, 4, 1, 4, 5⟩

/-- Initial net grasping is three, so the existing two observation lags give
the checked bound five. -/
theorem calibrated_releases_by_five :
    calibrated.grasp (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.fear (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.suffering (calibrated.toPath.run calibratedStart 5) = 0 := by
  exact calibrated.eventual_release_from_revision calibrated_conditions
    (s := calibratedStart) (n := 5) rfl (by decide)

/-! ## Countermodels and relapse -/

/-- Insight is reported, but no admitted evidence changes. -/
def ignored : EvidenceProcess Unit where
  step := id
  insight _ := True
  ownSupport _ := 1
  emptinessEvidence _ := 0
  fear _ := 1
  suffering _ := 1

theorem observation_without_assimilation :
    ignored.SupportDisciplined ∧ ignored.EvidenceRetained ∧
      ¬ ignored.ActiveAssimilation ∧ ¬ ignored.toPath.GraspContracts ∧
      ignored.insight () ∧
      (∀ n, ignored.suffering (ignored.toPath.run () n) = 1) := by
  refine ⟨fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, ?_, ?_,
    trivial, ?_⟩
  · intro h
    have bad := h () trivial (by decide)
    contradiction
  · intro h
    have bad := h () trivial
    contradiction
  · intro n
    rw [ignored.toPath.run_of_fixed (s := ()) rfl n]
    rfl

/-- A backfire updater admits one unit of counterevidence but creates two
units of new own-being support. -/
def backfire : EvidenceProcess Nat where
  step n := n + 1
  insight _ := True
  ownSupport n := 2 * n + 1
  emptinessEvidence n := n
  fear _ := 0
  suffering _ := 0

theorem backfire_assimilates : backfire.ActiveAssimilation := by
  intro n _ _
  simp [backfire]

theorem evidence_growth_without_support_discipline :
    backfire.EvidenceRetained ∧ backfire.ActiveAssimilation ∧
      ¬ backfire.SupportDisciplined ∧
      ¬ backfire.toPath.GraspContracts ∧
      backfire.grasp 0 = 1 ∧ backfire.grasp (backfire.step 0) = 2 := by
  refine ⟨?_, backfire_assimilates, ?_, ?_, rfl, rfl⟩
  · intro n _
    simp [backfire]
  · intro h
    have bad := h 0 trivial
    contradiction
  · intro h
    have bad := h 0 trivial
    contradiction

/-- State `false` has insight and a positive own-being balance.  One rational
step integrates the evidence, but the next non-insight step forgets it. -/
def relapse : EvidenceProcess Bool where
  step b := !b
  insight b := b = false
  ownSupport _ := 1
  emptinessEvidence b := if b then 1 else 0
  fear _ := 0
  suffering _ := 0

theorem relapse_rational_during_insight : relapse.RationalRevision := by
  constructor
  · intro b hb
    cases b <;> simp_all [relapse]
  · intro b hb
    cases b <;> simp_all [relapse]
  · intro b hb _
    cases b <;> simp_all [relapse, grasp]

theorem relapse_loses_insight : ¬ relapse.InsightPersists := by
  intro h
  have bad := h false rfl
  contradiction

/-- Rational revision conditional on insight permits relapse when insight and
evidence retention do not persist: grasping reaches zero, then returns. -/
theorem rational_revision_can_relapse :
    relapse.RationalRevision ∧ ¬ relapse.InsightPersists ∧
      relapse.insight false ∧
      relapse.grasp (relapse.toPath.run false 1) = 0 ∧
      relapse.grasp (relapse.toPath.run false 2) = 1 := by
  exact ⟨relapse_rational_during_insight, relapse_loses_insight, rfl, rfl, rfl⟩

end BuddhistComparativeLogic.BeliefRevision
