/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Hetucakra
import BuddhistComparativeLogic.Buddhist.Madhyamaka.MMK

/-!
# Emptiness as an inference

`isabelle/Buddhist/HeartSutra/HeartSutra_Anumana.thy` combines the Madhyamaka assumptions with Dignāga's wheel.
This module retains an explicit reusable interface, then supplies an adapter
from the actual `Madhyamaka` development.  In that adapter universal emptiness
and arising are derived from the model, while a distinct comparison dharma is
constructed from the concrete `Dharma` datatype.
-/

namespace BuddhistComparativeLogic.Anumana

open BuddhistComparativeLogic.Hetucakra

structure MadhyamakaInference (Dharma : Type u) where
  emptyOf : Dharma → Prop
  arisen : Dharma → Prop
  allEmpty : ∀ d, emptyOf d
  allArisen : ∀ d, arisen d
  another : ∀ x : Dharma, ∃ y : Dharma, y ≠ x

namespace MadhyamakaInference

variable {Dharma : Type u} (m : MadhyamakaInference Dharma)

def inference (x : Dharma) : Hetucakra.Anumana Dharma where
  paksa := x
  sadhya := m.emptyOf
  reason := m.arisen

theorem H_all (d : Dharma) : (m.inference d).reason d := m.allArisen d

theorem vipaksa_empty {x y : Dharma} :
    ¬ (m.inference x).vipaksa y := by
  intro h
  exact h.2 (m.allEmpty y)

theorem sapaksa_all {x y : Dharma} (hne : y ≠ x) :
    (m.inference x).sapaksa y :=
  ⟨hne, m.allEmpty y⟩

theorem sunyata_anumana_valid (x : Dharma) :
    (m.inference x).wheelVerdict = .valid := by
  apply (m.inference x).wheel_valid_iff.mpr
  obtain ⟨y, hy⟩ := m.another x
  constructor
  · exact ⟨y, m.sapaksa_all hy, m.allArisen y⟩
  · intro y hv hreason
    exact m.vipaksa_empty hv

theorem uniformity_trivial (x : Dharma) :
    (∀ y, y ≠ x → m.arisen y → m.emptyOf y) →
      m.arisen x → m.emptyOf x := by
  intro _ _
  exact m.allEmpty x

end MadhyamakaInference

/-! ## Adapter from the actual Madhyamaka development -/

theorem another_dharma (x : BuddhistComparativeLogic.Dharma) :
    ∃ y : BuddhistComparativeLogic.Dharma, y ≠ x := by
  by_cases hx : x = BuddhistComparativeLogic.Dharma.jnana
  · refine ⟨BuddhistComparativeLogic.Dharma.prapti, ?_⟩
    intro h
    have bad : BuddhistComparativeLogic.Dharma.prapti = BuddhistComparativeLogic.Dharma.jnana :=
      h.trans hx
    cases bad
  · exact ⟨BuddhistComparativeLogic.Dharma.jnana, fun h => hx h.symm⟩

def MadhyamakaInference.ofMadhyamaka (M : BuddhistComparativeLogic.Madhyamaka V) :
    MadhyamakaInference BuddhistComparativeLogic.Dharma where
  emptyOf := M.toEmptiness.emptyOf
  arisen := fun d => M.logic.designated (M.arisen d)
  allEmpty := M.toEmptiness.sarva_dharma_sunya
  allArisen := M.mmk_24_19
  another := another_dharma

/-- The direct counterpart of the theorem inside Isabelle's `madhyamaka`
locale.  The caller supplies only the Madhyamaka model and subject; the
distinct comparison dharma is constructed by `another_dharma`. -/
theorem sunyata_anumana_valid (M : BuddhistComparativeLogic.Madhyamaka V)
    (x : BuddhistComparativeLogic.Dharma) :
    ((MadhyamakaInference.ofMadhyamaka M).inference x).wheelVerdict =
      .valid :=
  MadhyamakaInference.sunyata_anumana_valid
    (MadhyamakaInference.ofMadhyamaka M) x

/-! ## The agreed-example dispute -/

inductive Adharma where
  | samskrta | maya | asamskrta
  deriving DecidableEq, Repr

open Adharma

def bhavaviveka : Hetucakra.Anumana Adharma where
  paksa := .samskrta
  sadhya := fun d => d ≠ .asamskrta
  reason := fun d => d ≠ .asamskrta

theorem bhavaviveka_valid : bhavaviveka.wheelVerdict = .valid := by
  apply bhavaviveka.wheel_valid_iff.mpr
  constructor
  · exact ⟨.maya, ⟨by decide, by simp [bhavaviveka]⟩,
      by simp [bhavaviveka]⟩
  · intro x hx hr
    exact hx.2 hr

def noExample : Hetucakra.Anumana Adharma where
  paksa := .samskrta
  sadhya := fun d => d = .samskrta
  reason := fun d => d ≠ .asamskrta

theorem no_agreed_example_contradictory :
    noExample.wheelVerdict = .contradictory := by
  apply noExample.wheel_contradictory_iff.mpr
  constructor
  · intro x hx hr
    rcases hx with ⟨hne, hs⟩
    exact hne hs
  · exact ⟨.maya, ⟨by decide, by simp [noExample]⟩,
      by simp [noExample]⟩

end BuddhistComparativeLogic.Anumana
