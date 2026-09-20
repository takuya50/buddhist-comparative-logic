/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.TwoTruths
import BuddhistComparativeLogic.Core.Connexive

/-!
# The Diamond Sutra's logic of sokuhi

Lean counterpart of `isabelle/Buddhist/DiamondSutra/DiamondSutra_Sokuhi.thy`: single-level classical, FDE, FDE5,
and connexive readings are compared with a locally consistent two-truths
reading.
-/

namespace BuddhistComparativeLogic

open TV4 TV5 Satya2

inductive SokuhiTerm where
  | prajnaparamita | paramanu | lokadhatu | laksana32
  | prathamaParamita | ksantiParamita | sarvadharma | ksetravyuha
  | rupakaya | laksanaSampat | sattva | kusaladharma
  | prthagjana | pindagraha | dharmalaksana | atmadrsti
  deriving DecidableEq, Repr

open SokuhiTerm

def sokuhiSections : List (SokuhiTerm × Nat) :=
  [(prajnaparamita, 13), (paramanu, 13), (lokadhatu, 13), (laksana32, 13),
   (prathamaParamita, 14), (ksantiParamita, 14), (sarvadharma, 17),
   (ksetravyuha, 17), (rupakaya, 20), (laksanaSampat, 20), (sattva, 21),
   (kusaladharma, 23), (prthagjana, 25), (pindagraha, 30),
   (dharmalaksana, 31), (atmadrsti, 31)]

theorem sokuhi_sections_shape :
    sokuhiSections.length = 16 ∧ (sokuhiSections.map Prod.fst).Nodup := by
  decide

namespace MVLogic

def setsu (L : MVLogic V) (v : α → V) (a : α) : Prop :=
  L.designated (v a)

def hi (L : MVLogic V) (v : α → V) (a : α) : Prop :=
  L.designated (L.neg (v a))

end MVLogic

theorem sokuhi_classical_unsat (v : α → Bool) (a : α) :
    ¬ (mvClassical.setsu v a ∧ mvClassical.hi v a) := by
  change ¬ (v a = true ∧ Bool.not (v a) = true)
  cases v a <;> decide

theorem sokuhi_fde_iff_glut (v : α → TV4) (a : α) :
    mvFDE.setsu v a ∧ mvFDE.hi v a ↔ v a = B := by
  change tr (v a) = true ∧ tr (neg4 (v a)) = true ↔ v a = B
  cases v a <;> decide

theorem sokuhi_fde5_iff_glut (v : α → TV5) (a : α) :
    mvFDE5.setsu v a ∧ mvFDE5.hi v a ↔ v a = TV5.fin B := by
  change des5 (v a) = true ∧ des5 (neg5 (v a)) = true ↔
    v a = TV5.fin B
  cases h : v a with
  | fin x => cases x <;> decide
  | E => decide

theorem sokuhi_connexive_iff (v : α → TV4) (a : α) :
    CFm.sat CFm.cimp4 v (.neg (.imp (.atom a) (.atom a))) = true ↔
      v a ≠ T := by
  cases h : v a <;>
    simp [CFm.sat, CFm.eval, CFm.cimp4, CFm.boolImp, h,
      neg4, mk, tr, fa]

theorem sokuhi_connexive_forces_glut (v : α → TV4) (a : α) :
    CFm.sat CFm.cimp4 v (.atom a) = true ∧
      CFm.sat CFm.cimp4 v (.neg (.imp (.atom a) (.atom a))) = true ↔
      v a = B := by
  cases h : v a <;>
    simp [CFm.sat, CFm.eval, CFm.cimp4, CFm.boolImp, h,
      neg4, mk, tr, fa]

structure SokuhiTwoTruths (Term : Type u) where
  named : Term → TV4
  own : Term → TV4
  setsu_c : ∀ x, mvFDE.designated (named x)
  hi_u : ∀ x, mvFDE.designated (neg4 (own x))
  conv_consistent : ∀ x, ¬ mvFDE.designated (neg4 (named x))
  ult_consistent : ∀ x, ¬ mvFDE.designated (own x)

namespace SokuhiTwoTruths

variable (S : SokuhiTwoTruths Term)

def zemyo (x : Term) : Prop :=
  mvFDE.designated (S.named x) ∧ mvFDE.designated (neg4 (S.own x))

theorem named_T (x : Term) : S.named x = T := by
  have hp := S.setsu_c x
  have hn := S.conv_consistent x
  change tr (S.named x) = true at hp
  change ¬ tr (neg4 (S.named x)) = true at hn
  cases h : S.named x with
  | T => rfl
  | B =>
      exfalso
      apply hn
      rw [h]
      rfl
  | N =>
      exfalso
      rw [h] at hp
      exact Bool.noConfusion hp
  | F =>
      exfalso
      rw [h] at hp
      exact Bool.noConfusion hp

theorem own_F (x : Term) : S.own x = F := by
  have hp := S.hi_u x
  have hn := S.ult_consistent x
  change tr (neg4 (S.own x)) = true at hp
  change ¬ tr (S.own x) = true at hn
  cases h : S.own x with
  | T =>
      exfalso
      apply hn
      rw [h]
      rfl
  | B =>
      exfalso
      apply hn
      rw [h]
      rfl
  | N =>
      exfalso
      rw [h] at hp
      exact Bool.noConfusion hp
  | F => rfl

theorem sokuhi_bivalent (x : Term) :
    (S.named x = T ∨ S.named x = F) ∧
      (S.own x = T ∨ S.own x = F) := by
  rw [S.named_T x, S.own_F x]
  exact ⟨Or.inl rfl, Or.inr rfl⟩

theorem sokuhi_no_contradiction (x : Term) :
    S.named x ≠ B ∧ S.own x ≠ B := by
  rw [S.named_T x, S.own_F x]
  decide

theorem zemyo_holds (x : Term) : S.zemyo x := by
  rw [zemyo, S.named_T x, S.own_F x]
  exact ⟨rfl, rfl⟩

end SokuhiTwoTruths

def TwoTruthsFDE.toSokuhi (T : TwoTruthsFDE) : SokuhiTwoTruths Dharma where
  named := T.val samvrti
  own := T.svAt paramartha
  setsu_c := T.conv_appears
  hi_u := T.ult_empty
  conv_consistent := T.conv_consistent
  ult_consistent := T.ult_consistent

def zemyoOf (named own : Term → TV4) (x : Term) : Prop :=
  mvFDE.designated (named x) ∧ mvFDE.designated (neg4 (own x))

theorem zemyo_needs_hi (x : Term) :
    mvFDE.setsu (fun _ : Term => T) x ∧
      ¬ zemyoOf (fun _ => T) (fun _ => T) x := by
  change tr T = true ∧ ¬ (tr T = true ∧ tr (neg4 T) = true)
  decide

theorem zemyo_iff_setsu_and_hi (named own : Term → TV4) (x : Term) :
    zemyoOf named own x ↔ mvFDE.setsu named x ∧ mvFDE.hi own x :=
  Iff.rfl

end BuddhistComparativeLogic
