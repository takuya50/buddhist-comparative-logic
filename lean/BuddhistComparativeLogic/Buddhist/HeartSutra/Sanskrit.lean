/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.TwoTruths

/-!
# Sanskrit HS06--HS07 and the illusion reading

Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Sanskrit.thy`.  It adds Attwood's `mayopama`
reading and isolates the conventional-appearance premise needed for the
converse "emptiness is form".
-/

namespace BuddhistComparativeLogic

open TV4 Dharma

namespace Emptiness

variable (E : Emptiness V)

def RMaya (x : Dharma) : Prop :=
  E.logic.designated (E.appears x) ∧ ¬ E.logic.designated (E.sv x)

theorem R_maya_iff (x : Dharma) :
    E.RMaya x ↔ ¬ E.logic.designated (E.sv x) := by
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨E.samvrti x, h⟩

end Emptiness

theorem cl_sv_False (E : Emptiness Bool)
    (hDes : ∀ b, E.logic.designated b ↔ b = true)
    (hNeg : ∀ b, E.logic.neg b = Bool.not b) (x : Dharma) :
    E.sv x = false := by
  have hEmpty := E.sarva_dharma_sunya x
  have hTrue := (hDes _).mp hEmpty
  rw [Emptiness.sunya, hNeg] at hTrue
  cases h : E.sv x
  · rfl
  · exfalso
    rw [h] at hTrue
    exact Bool.noConfusion hTrue

theorem cl_maya (E : Emptiness Bool)
    (hDes : ∀ b, E.logic.designated b ↔ b = true)
    (hNeg : ∀ b, E.logic.neg b = Bool.not b) (x : Dharma) :
    E.RMaya x := by
  constructor
  · exact E.samvrti x
  · rw [cl_sv_False E hDes hNeg x]
    intro h
    have := (hDes false).mp h
    contradiction

theorem cl_four_readings_coincide (E : Emptiness Bool)
    (hDes : ∀ b, E.logic.designated b ↔ b = true)
    (hNeg : ∀ b, E.logic.neg b = Bool.not b)
    (hConj : ∀ a b, E.logic.mconj a b = Bool.and a b)
    (x : Dharma) :
    E.RMaya x ∧ E.RIdentity x ∧ E.RMutual x ∧ E.RNotsep x := by
  have hc := cl_readings_coincide E hDes hNeg hConj x
  have hm := E.hs07_R_mutual x
  exact ⟨cl_maya E hDes hNeg x, hc.1.mpr hm, hm, hc.2.mp hm⟩

theorem sv_BF (E : Emptiness TV4)
    (hDes : ∀ z, E.logic.designated z ↔ tr z = true)
    (hNeg : ∀ z, E.logic.neg z = neg4 z) (x : Dharma) :
    E.sv x = B ∨ E.sv x = F := by
  have hEmpty := E.sarva_dharma_sunya x
  have hTrue := (hDes _).mp hEmpty
  rw [Emptiness.sunya, hNeg] at hTrue
  cases h : E.sv x <;> simp_all [neg4, mk, tr, fa]

theorem fde_maya_iff_sv_F (E : Emptiness TV4)
    (hDes : ∀ z, E.logic.designated z ↔ tr z = true)
    (hNeg : ∀ z, E.logic.neg z = neg4 z) (x : Dharma) :
    E.RMaya x ↔ E.sv x = F := by
  have hsv := sv_BF E hDes hNeg x
  rw [E.R_maya_iff]
  rcases hsv with hsv | hsv <;>
    simp [hDes, hsv, tr]

theorem fde_maya_consistent_coincide (E : Emptiness TV4)
    (hDes : ∀ z, E.logic.designated z ↔ tr z = true)
    (hNeg : ∀ z, E.logic.neg z = neg4 z)
    (hConj : ∀ a b, E.logic.mconj a b = conj4 a b)
    (x : Dharma) (hMaya : E.RMaya x) (hAppears : E.appears x = T) :
    E.RIdentity x ∧ E.RMutual x ∧ E.RNotsep x := by
  have hsv : E.sv x = F := (fde_maya_iff_sv_F E hDes hNeg x).mp hMaya
  constructor
  · rw [Emptiness.RIdentity, Emptiness.sunya, hAppears, hsv, hNeg]
    rfl
  · constructor
    · exact E.hs07_R_mutual x
    · rw [Emptiness.RNotsep, Emptiness.sunya, hAppears, hsv]
      simp only [hDes, hNeg, hConj]
      decide

def mayaGlut : Emptiness TV4 where
  logic := mvFDE
  sv _ := F
  appears _ := B
  dep _ _ := True
  mmk_24_18 _ := rfl
  pratitya _ := ⟨jnana, trivial⟩
  samvrti _ := rfl
  nidana_dep _ := trivial

theorem fde_emptiness_nonvacuous : Nonempty (Emptiness TV4) :=
  ⟨fdeGlutEmptiness⟩

theorem fde_maya_not_notsep (x : Dharma) :
    mayaGlut.RMaya x ∧ ¬ mayaGlut.RNotsep x := by
  simp [Emptiness.RMaya, Emptiness.RNotsep, Emptiness.sunya,
    mayaGlut, mvFDE, neg4, conj4, mk, tr, fa]

structure EmptinessNoSamvrti (V : Type u) (Term : Type v) where
  logic : MVLogic V
  sv : Term → V
  appears : Term → V
  empty_all : ∀ x, logic.designated (logic.neg (sv x))

namespace EmptinessNoSamvrti

variable (E : EmptinessNoSamvrti V Term)

def shikiSokuKu : Prop :=
  ∀ x, E.logic.designated (E.appears x) →
    E.logic.designated (E.logic.neg (E.sv x))

def kuSokuZeShiki : Prop :=
  ∀ x, E.logic.designated (E.logic.neg (E.sv x)) →
    E.logic.designated (E.appears x)

theorem shiki_soku_ku_holds : E.shikiSokuKu := by
  intro x _
  exact E.empty_all x

theorem ku_soku_ze_shiki_iff_samvrti :
    E.kuSokuZeShiki ↔ ∀ x, E.logic.designated (E.appears x) := by
  constructor
  · intro h x
    exact h x (E.empty_all x)
  · intro h x _
    exact h x

end EmptinessNoSamvrti

def rabbitHornModel : EmptinessNoSamvrti Bool Bool where
  logic := mvClassical
  sv _ := false
  appears x := x
  empty_all _ := rfl

theorem rabbit_horn :
    rabbitHornModel.shikiSokuKu ∧ ¬ rabbitHornModel.kuSokuZeShiki := by
  constructor
  · exact rabbitHornModel.shiki_soku_ku_holds
  · intro h
    have hf := h false
    exact Bool.noConfusion (hf rfl)

end BuddhistComparativeLogic
