/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Anumana
import BuddhistComparativeLogic.Buddhist.Pramana.Dharmakirti
import BuddhistComparativeLogic.Buddhist.HeartSutra.AssumptionAudit

/-!
# Explicit pervasion in the emptiness inference

Connect the existing Madhyamaka inference to Dharmakirti.Model, keeping
exactly its subject, reason and thesis. A second adapter starts from the
weaker independent-predicate model: its pervasion is precisely the exclusion
law, so the bridge is visible rather than hidden in universal emptiness.
-/

namespace BuddhistComparativeLogic.EmptinessInference

def ofMadhyamaka (M : Madhyamaka V) (x : Dharma) : Dharmakirti.Model Dharma where
  toAnumana := (Anumana.MadhyamakaInference.ofMadhyamaka M).inference x
  vyapti := ∀ y, M.logic.designated (M.arisen y) → M.toEmptiness.emptyOf y
  vyapti_iff := Iff.rfl

theorem madhyamaka_pervasion (M : Madhyamaka V) (x : Dharma) :
    (ofMadhyamaka M x).vyapti :=
  fun y _ => M.toEmptiness.sarva_dharma_sunya y

/-- This adapter inherits already established universal emptiness; it is
not a new independent argument for that premise. -/
theorem sunyata_via_dharmakirti (M : Madhyamaka V) (x : Dharma) :
    (ofMadhyamaka M x).sadhya x :=
  (ofMadhyamaka M x).vyapti_sound (madhyamaka_pervasion M x) (M.mmk_24_19 x)

theorem preserves_dignaga_verdict (M : Madhyamaka V) (x : Dharma) :
    (ofMadhyamaka M x).toAnumana.wheelVerdict = .valid :=
  Anumana.sunyata_anumana_valid M x

def ofDependence (M : AssumptionAudit.Dependence D) (x : D) :
    Dharmakirti.Model D where
  paksa := x
  sadhya := M.emptyOf
  reason := M.arisen
  vyapti := M.Exclusion
  vyapti_iff := by
    constructor
    · exact fun h y hy => M.empty_of_arisen h hy
    · intro h y z hz
      exact h y ⟨z, hz⟩

/-- No universal arising or agreed comparison example is required for this
deduction: subject arising plus the explicit pervasion suffices. -/
theorem empty_via_explicit_pervasion (M : AssumptionAudit.Dependence D)
    (x : D) (bridge : M.Exclusion) (arising : M.arisen x) :
    (ofDependence M x).sadhya x :=
  (ofDependence M x).vyapti_sound bridge arising

/-- The inference adapter cannot manufacture the missing pervasion. -/
theorem arisen_without_pervasion_or_thesis :
    (ofDependence AssumptionAudit.dependentOwn false).toAnumana.paksadharmata ∧
    ¬ (ofDependence AssumptionAudit.dependentOwn false).vyapti ∧
    ¬ (ofDependence AssumptionAudit.dependentOwn false).sadhya false := by
  refine ⟨AssumptionAudit.universal_arising_without_exclusion.1 false, ?_,
    AssumptionAudit.universal_arising_without_exclusion.2⟩
  intro h
  exact AssumptionAudit.universal_arising_without_exclusion.2
    (AssumptionAudit.dependentOwn.all_empty h
      AssumptionAudit.universal_arising_without_exclusion.1 false)

end BuddhistComparativeLogic.EmptinessInference
