/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.Emptiness

/-!
# MMK 15:2 and 24:18--19

Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_MMK24.thy`.  Own-being is defined as the negation
of dependent arising; universal dependent arising and involutive negation
then derive the emptiness premise used by `Emptiness`.
-/

namespace BuddhistComparativeLogic

open TV4 TV5 Dharma

/-- Explicit-record counterpart of Isabelle's `madhyamaka` locale. -/
structure Madhyamaka (V : Type u) where
  logic : MVLogic V
  arisen : Dharma → V
  appears : Dharma → V
  dep : Dharma → Dharma → Prop
  neg_invol : ∀ w, logic.neg (logic.neg w) = w
  mmk_24_19 : ∀ x, logic.designated (arisen x)
  arisen_dep : ∀ {x}, logic.designated (arisen x) → ∃ y, dep y x
  samvrti_m : ∀ x, logic.designated (appears x)
  nidana_dep_m : ∀ {n m}, nidanaNext n = some m → dep (ni n) (ni m)

namespace Madhyamaka

variable (M : Madhyamaka V)

def svabhava (x : Dharma) : V := M.logic.neg (M.arisen x)

theorem mmk_24_18_derived (x : Dharma) :
    M.logic.designated (M.logic.neg (M.svabhava x)) := by
  rw [svabhava, M.neg_invol]
  exact M.mmk_24_19 x

theorem pratitya_derived (x : Dharma) : ∃ y, M.dep y x :=
  M.arisen_dep (M.mmk_24_19 x)

/-- The derived emptiness model, corresponding to Isabelle's sublocale. -/
def toEmptiness : Emptiness V where
  logic := M.logic
  sv := M.svabhava
  appears := M.appears
  dep := M.dep
  mmk_24_18 := fun {_} _ => M.mmk_24_18_derived _
  pratitya := M.pratitya_derived
  samvrti := M.samvrti_m
  nidana_dep := M.nidana_dep_m

def prajnapti (x : Dharma) : Prop :=
  M.logic.designated (M.appears x) ∧ M.toEmptiness.emptyOf x

def eternalism (x : Dharma) : Prop :=
  M.logic.designated (M.svabhava x)

def nihilism (x : Dharma) : Prop :=
  ¬ M.logic.designated (M.appears x)

def madhyama (x : Dharma) : Prop :=
  ¬ M.eternalism x ∧ ¬ M.nihilism x

theorem mmk_24_18_prajnapti (x : Dharma) : M.prajnapti x :=
  ⟨M.samvrti_m x, M.toEmptiness.sarva_dharma_sunya x⟩

theorem no_nihilism (x : Dharma) : ¬ M.nihilism x := by
  intro h
  exact h (M.samvrti_m x)

theorem madhyama_iff_no_eternalism (x : Dharma) :
    M.madhyama x ↔ ¬ M.logic.designated (M.svabhava x) := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, M.no_nihilism x⟩

end Madhyamaka

theorem neg4_invol (x : TV4) : neg4 (neg4 x) = x := by
  cases x <;> rfl

theorem neg5_invol (x : TV5) : neg5 (neg5 x) = x := by
  cases x with
  | fin y => rw [neg5, neg5, neg4_invol]
  | E => rfl

def madhyamakaClassical : Madhyamaka Bool where
  logic := mvClassical
  arisen _ := true
  appears _ := true
  dep _ _ := True
  neg_invol b := by cases b <;> rfl
  mmk_24_19 _ := rfl
  arisen_dep _ := ⟨jnana, trivial⟩
  samvrti_m _ := rfl
  nidana_dep_m _ := trivial

def madhyamakaFDE : Madhyamaka TV4 where
  logic := mvFDE
  arisen _ := T
  appears _ := T
  dep _ _ := True
  neg_invol := neg4_invol
  mmk_24_19 _ := rfl
  arisen_dep _ := ⟨jnana, trivial⟩
  samvrti_m _ := rfl
  nidana_dep_m _ := trivial

def madhyamakaFDEGlut : Madhyamaka TV4 where
  logic := mvFDE
  arisen _ := B
  appears _ := T
  dep _ _ := True
  neg_invol := neg4_invol
  mmk_24_19 _ := rfl
  arisen_dep _ := ⟨jnana, trivial⟩
  samvrti_m _ := rfl
  nidana_dep_m _ := trivial

theorem cl_madhyama (M : Madhyamaka Bool)
    (hDes : ∀ b, M.logic.designated b ↔ b = true)
    (hNeg : ∀ b, M.logic.neg b = Bool.not b) (x : Dharma) :
    M.madhyama x := by
  rw [M.madhyama_iff_no_eternalism]
  have har : M.arisen x = true := (hDes _).mp (M.mmk_24_19 x)
  rw [Madhyamaka.svabhava, hNeg, har]
  intro hFalse
  have := (hDes false).mp hFalse
  contradiction

theorem fde_arisen_TB (M : Madhyamaka TV4)
    (hDes : ∀ z, M.logic.designated z ↔ tr z = true)
    (x : Dharma) : M.arisen x = T ∨ M.arisen x = B := by
  have h := (hDes _).mp (M.mmk_24_19 x)
  cases ha : M.arisen x <;> simp_all [tr]

theorem fde_madhyama_iff_consistent (M : Madhyamaka TV4)
    (hDes : ∀ z, M.logic.designated z ↔ tr z = true)
    (hNeg : ∀ z, M.logic.neg z = neg4 z) (x : Dharma) :
    M.madhyama x ↔ M.arisen x = T := by
  have har := fde_arisen_TB M hDes x
  rw [M.madhyama_iff_no_eternalism]
  rcases har with har | har <;>
    simp [Madhyamaka.svabhava, hDes, hNeg, har, neg4, mk, tr, fa]

theorem madhyamaka_consistent_cl : Nonempty (Madhyamaka Bool) :=
  ⟨madhyamakaClassical⟩

theorem madhyamaka_consistent_fde : Nonempty (Madhyamaka TV4) :=
  ⟨madhyamakaFDE⟩

theorem cl_madhyamaka_nonvacuous : Nonempty (Madhyamaka Bool) :=
  madhyamaka_consistent_cl

theorem fde_madhyamaka_nonvacuous : Nonempty (Madhyamaka TV4) :=
  madhyamaka_consistent_fde

theorem fde_glut_defeats_middle_way (x : Dharma) :
    ¬ madhyamakaFDEGlut.madhyama x := by
  simp [Madhyamaka.madhyama, Madhyamaka.eternalism,
    Madhyamaka.svabhava, madhyamakaFDEGlut, mvFDE, neg4, mk, tr, fa]

end BuddhistComparativeLogic
