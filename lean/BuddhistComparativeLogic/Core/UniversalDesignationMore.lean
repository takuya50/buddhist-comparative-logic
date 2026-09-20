/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.MVExample
import BuddhistComparativeLogic.Core.UniversalDesignationFDE

/-!
# Universal designation over K3 and LP

This module completes the two three-valued cases of universal plurivalent
designation.  Positive universal K3 consequence collapses to ordinary K3.
Positive universal LP consequence instead collapses to FDE: a nonempty LP
value set containing both classical values behaves as an FDE gap.  The generic
variable-inclusion theorem then gives the unrestricted consequence relations.
-/

namespace BuddhistComparativeLogic

open Fm TV4 Atom

/-! ## The K3 base -/

instance : Inhabited K3 := ⟨.u⟩

theorem exists_k3_iff (P : K3 → Prop) :
    (∃ x, P x) ↔ P .t ∨ P .u ∨ P .f := by
  constructor
  · rintro ⟨x, hx⟩
    cases x <;> simp_all
  · intro h
    rcases h with h | h | h
    · exact ⟨.t, h⟩
    · exact ⟨.u, h⟩
    · exact ⟨.f, h⟩

theorem k3_set_nonempty_iff (X : PSet K3) :
    pnonempty X ↔ X .t ∨ X .u ∨ X .f :=
  exists_k3_iff X

def k3ThetaBits (t u f : Bool) : K3 :=
  if u then .u
  else if t && f then .u
  else if t then .t
  else if f then .f
  else .u

noncomputable def k3Theta (X : PSet K3) : K3 :=
  k3ThetaBits (propBool (X .t)) (propBool (X .u)) (propBool (X .f))

theorem k3_designated_subset_iff (X : PSet K3) :
    psubset X K3.logic.designated ↔ ¬ X .u ∧ ¬ X .f := by
  constructor
  · intro h
    constructor
    · intro hu
      have := h .u hu
      exact K3.noConfusion this
    · intro hf
      have := h .f hf
      exact K3.noConfusion this
  · rintro ⟨hu, hf⟩ x hx
    cases x <;> simp_all [K3.logic]

theorem k3Theta_designated (X : PSet K3) (hX : pnonempty X) :
    psubset X K3.logic.designated ↔ K3.logic.designated (k3Theta X) := by
  classical
  rw [k3_designated_subset_iff]
  have hmem := (k3_set_nonempty_iff X).1 hX
  by_cases xt : X .t <;> by_cases xu : X .u <;> by_cases xf : X .f <;>
    simp_all [k3Theta, k3ThetaBits, propBool, K3.logic]

theorem img_k3_conj_mem (X Y : PSet K3)
    (hX : pnonempty X) (hY : pnonempty Y) :
    (pimage₂ K3.conj X Y .t ↔ X .t ∧ Y .t) ∧
    (pimage₂ K3.conj X Y .f ↔ X .f ∨ Y .f) ∧
    (pimage₂ K3.conj X Y .u ↔
      (X .u ∧ (Y .t ∨ Y .u)) ∨ (Y .u ∧ (X .t ∨ X .u))) := by
  have hx := (k3_set_nonempty_iff X).1 hX
  have hy := (k3_set_nonempty_iff Y).1 hY
  simp only [pimage₂, exists_k3_iff]
  simp [K3.conj]
  grind

theorem img_k3_disj_mem (X Y : PSet K3)
    (hX : pnonempty X) (hY : pnonempty Y) :
    (pimage₂ K3.disj X Y .f ↔ X .f ∧ Y .f) ∧
    (pimage₂ K3.disj X Y .t ↔ X .t ∨ Y .t) ∧
    (pimage₂ K3.disj X Y .u ↔
      (X .u ∧ (Y .f ∨ Y .u)) ∨ (Y .u ∧ (X .f ∨ X .u))) := by
  have hx := (k3_set_nonempty_iff X).1 hX
  have hy := (k3_set_nonempty_iff Y).1 hY
  simp only [pimage₂, exists_k3_iff]
  simp [K3.disj]
  grind

theorem img_k3_neg_mem (X : PSet K3) :
    (pimage K3.neg X .t ↔ X .f) ∧
    (pimage K3.neg X .f ↔ X .t) ∧
    (pimage K3.neg X .u ↔ X .u) := by
  simp only [pimage, exists_k3_iff]
  simp [K3.neg]

theorem k3ThetaBits_conj
    (tX uX fX tY uY fY : Bool)
    (hX : tX = true ∨ uX = true ∨ fX = true)
    (hY : tY = true ∨ uY = true ∨ fY = true) :
    k3ThetaBits (tX && tY)
      ((uX && (tY || uY)) || (uY && (tX || uX))) (fX || fY) =
      K3.conj (k3ThetaBits tX uX fX) (k3ThetaBits tY uY fY) := by
  cases tX <;> cases uX <;> cases fX <;>
    cases tY <;> cases uY <;> cases fY <;>
      simp_all [k3ThetaBits, K3.conj]

theorem k3ThetaBits_disj
    (tX uX fX tY uY fY : Bool)
    (hX : tX = true ∨ uX = true ∨ fX = true)
    (hY : tY = true ∨ uY = true ∨ fY = true) :
    k3ThetaBits (tX || tY)
      ((uX && (fY || uY)) || (uY && (fX || uX))) (fX && fY) =
      K3.disj (k3ThetaBits tX uX fX) (k3ThetaBits tY uY fY) := by
  cases tX <;> cases uX <;> cases fX <;>
    cases tY <;> cases uY <;> cases fY <;>
      simp_all [k3ThetaBits, K3.disj]

theorem k3ThetaBits_neg (t u f : Bool) :
    k3ThetaBits f u t = K3.neg (k3ThetaBits t u f) := by
  cases t <;> cases u <;> cases f <;>
    simp [k3ThetaBits, K3.neg]

theorem k3Theta_hom_conj (X Y : PSet K3)
    (hX : pnonempty X) (hY : pnonempty Y) :
    k3Theta (pimage₂ K3.conj X Y) = K3.conj (k3Theta X) (k3Theta Y) := by
  rcases img_k3_conj_mem X Y hX hY with ⟨hT, hF, hU⟩
  have hx := (k3_set_nonempty_iff X).1 hX
  have hy := (k3_set_nonempty_iff Y).1 hY
  unfold k3Theta
  rw [propBool_iff hT, propBool_iff hU, propBool_iff hF]
  simp only [propBool_and, propBool_or]
  have hxBits : propBool (X .t) = true ∨ propBool (X .u) = true ∨
      propBool (X .f) = true := by
    rcases hx with hx | hx | hx
    · exact Or.inl ((propBool_eq_true _).2 hx)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hx))
    · exact Or.inr (Or.inr ((propBool_eq_true _).2 hx))
  have hyBits : propBool (Y .t) = true ∨ propBool (Y .u) = true ∨
      propBool (Y .f) = true := by
    rcases hy with hy | hy | hy
    · exact Or.inl ((propBool_eq_true _).2 hy)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hy))
    · exact Or.inr (Or.inr ((propBool_eq_true _).2 hy))
  exact k3ThetaBits_conj _ _ _ _ _ _ hxBits hyBits

theorem k3Theta_hom_disj (X Y : PSet K3)
    (hX : pnonempty X) (hY : pnonempty Y) :
    k3Theta (pimage₂ K3.disj X Y) = K3.disj (k3Theta X) (k3Theta Y) := by
  rcases img_k3_disj_mem X Y hX hY with ⟨hF, hT, hU⟩
  have hx := (k3_set_nonempty_iff X).1 hX
  have hy := (k3_set_nonempty_iff Y).1 hY
  unfold k3Theta
  rw [propBool_iff hT, propBool_iff hU, propBool_iff hF]
  simp only [propBool_and, propBool_or]
  have hxBits : propBool (X .t) = true ∨ propBool (X .u) = true ∨
      propBool (X .f) = true := by
    rcases hx with hx | hx | hx
    · exact Or.inl ((propBool_eq_true _).2 hx)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hx))
    · exact Or.inr (Or.inr ((propBool_eq_true _).2 hx))
  have hyBits : propBool (Y .t) = true ∨ propBool (Y .u) = true ∨
      propBool (Y .f) = true := by
    rcases hy with hy | hy | hy
    · exact Or.inl ((propBool_eq_true _).2 hy)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hy))
    · exact Or.inr (Or.inr ((propBool_eq_true _).2 hy))
  exact k3ThetaBits_disj _ _ _ _ _ _ hxBits hyBits

theorem k3Theta_hom_neg (X : PSet K3) :
    k3Theta (pimage K3.neg X) = K3.neg (k3Theta X) := by
  rcases img_k3_neg_mem X with ⟨hT, hF, hU⟩
  unfold k3Theta
  rw [propBool_iff hT, propBool_iff hU, propBool_iff hF]
  exact k3ThetaBits_neg _ _ _

theorem k3Theta_hom_eval (Vn : α → PSet K3) (A : Fm α)
    (hV : ∀ a, pnonempty (Vn a)) :
    k3Theta (peval K3.neg K3.conj K3.disj Vn A) =
      mvEval K3.neg K3.conj K3.disj (fun a => k3Theta (Vn a)) A := by
  induction A with
  | atom _ => rfl
  | neg A ih =>
      rw [peval, mvEval, k3Theta_hom_neg, ih]
  | conj A C ihA ihC =>
      have hA := peval_nonempty K3.neg K3.conj K3.disj Vn A hV
      have hC := peval_nonempty K3.neg K3.conj K3.disj Vn C hV
      rw [peval, mvEval, k3Theta_hom_conj _ _ hA hC, ihA, ihC]
  | disj A C ihA ihC =>
      have hA := peval_nonempty K3.neg K3.conj K3.disj Vn A hV
      have hC := peval_nonempty K3.neg K3.conj K3.disj Vn C hV
      rw [peval, mvEval, k3Theta_hom_disj _ _ hA hC, ihA, ihC]

theorem pos_up_k3_is_k3 (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails K3.logic Γ A ↔ K3.logic.entails Γ A := by
  constructor
  · intro h w hprem
    have hpos : ∀ a, pnonempty (psingleton (w a)) := by
      intro a
      exact ⟨w a, rfl⟩
    have hpremUp : ∀ C, Γ C →
        upsat K3.logic (fun a => psingleton (w a)) C := by
      intro C hC
      exact (upsat_sing_iff K3.logic w C).2 (hprem C hC)
    exact (upsat_sing_iff K3.logic w A).1
      (h (fun a => psingleton (w a)) hpos hpremUp)
  · intro h Vn hpos hprem
    have key (C : Fm α) :
        upsat K3.logic Vn C ↔
          K3.logic.sat (fun a => k3Theta (Vn a)) C := by
      have hne := peval_nonempty K3.neg K3.conj K3.disj Vn C hpos
      change psubset (peval K3.neg K3.conj K3.disj Vn C)
          K3.logic.designated ↔
        K3.logic.designated
          (mvEval K3.neg K3.conj K3.disj (fun a => k3Theta (Vn a)) C)
      rw [← k3Theta_hom_eval Vn C hpos]
      exact k3Theta_designated _ hne
    have hs := h (fun a => k3Theta (Vn a))
      (fun C hC => (key C).1 (hprem C hC))
    exact (key A).2 hs

theorem priest_open_question_k3 (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails K3.logic Γ A ↔
      K3.logic.entails (restrictToAtoms Γ A) A := by
  rw [upentails_variable_inclusion, pos_up_k3_is_k3]

/-! ## The LP base -/

inductive LP3 where
  | t | b | f
  deriving DecidableEq, Repr

namespace LP3

instance : Inhabited LP3 := ⟨.b⟩

def neg : LP3 → LP3
  | .t => .f
  | .b => .b
  | .f => .t

def conj : LP3 → LP3 → LP3
  | .f, _ => .f
  | _, .f => .f
  | .b, _ => .b
  | _, .b => .b
  | .t, .t => .t

def disj : LP3 → LP3 → LP3
  | .t, _ => .t
  | _, .t => .t
  | .b, _ => .b
  | _, .b => .b
  | .f, .f => .f

def logic : MVLogic LP3 where
  designated x := x = .t ∨ x = .b
  neg := neg
  mconj := conj
  mdisj := disj
  designated_nonempty := ⟨.t, Or.inl rfl⟩
  designated_proper := ⟨.f, by decide⟩

end LP3

theorem exists_lp3_iff (P : LP3 → Prop) :
    (∃ x, P x) ↔ P .t ∨ P .b ∨ P .f := by
  constructor
  · rintro ⟨x, hx⟩
    cases x <;> simp_all
  · intro h
    rcases h with h | h | h
    · exact ⟨.t, h⟩
    · exact ⟨.b, h⟩
    · exact ⟨.f, h⟩

theorem lp3_set_nonempty_iff (X : PSet LP3) :
    pnonempty X ↔ X .t ∨ X .b ∨ X .f :=
  exists_lp3_iff X

def lpThetaBits (t _b f : Bool) : TV4 :=
  if t && f then N
  else if t then T
  else if f then F
  else B

noncomputable def lpTheta (X : PSet LP3) : TV4 :=
  lpThetaBits (propBool (X .t)) (propBool (X .b)) (propBool (X .f))

theorem lp_designated_subset_iff (X : PSet LP3) :
    psubset X LP3.logic.designated ↔ ¬ X .f := by
  constructor
  · intro h hf
    have := h .f hf
    rcases this with h | h <;> exact LP3.noConfusion h
  · intro hf x hx
    cases x <;> simp_all [LP3.logic]

theorem lpTheta_designated (X : PSet LP3) (hX : pnonempty X) :
    psubset X LP3.logic.designated ↔ mvFDE.designated (lpTheta X) := by
  classical
  rw [lp_designated_subset_iff]
  have hmem := (lp3_set_nonempty_iff X).1 hX
  by_cases xt : X .t <;> by_cases xb : X .b <;> by_cases xf : X .f <;>
    simp_all [lpTheta, lpThetaBits, propBool, mvFDE, tr]

theorem img_lp_conj_mem (X Y : PSet LP3)
    (hX : pnonempty X) (hY : pnonempty Y) :
    (pimage₂ LP3.conj X Y .t ↔ X .t ∧ Y .t) ∧
    (pimage₂ LP3.conj X Y .f ↔ X .f ∨ Y .f) ∧
    (pimage₂ LP3.conj X Y .b ↔
      (X .b ∧ (Y .t ∨ Y .b)) ∨ (Y .b ∧ (X .t ∨ X .b))) := by
  have hx := (lp3_set_nonempty_iff X).1 hX
  have hy := (lp3_set_nonempty_iff Y).1 hY
  simp only [pimage₂, exists_lp3_iff]
  simp [LP3.conj]
  grind

theorem img_lp_disj_mem (X Y : PSet LP3)
    (hX : pnonempty X) (hY : pnonempty Y) :
    (pimage₂ LP3.disj X Y .f ↔ X .f ∧ Y .f) ∧
    (pimage₂ LP3.disj X Y .t ↔ X .t ∨ Y .t) ∧
    (pimage₂ LP3.disj X Y .b ↔
      (X .b ∧ (Y .f ∨ Y .b)) ∨ (Y .b ∧ (X .f ∨ X .b))) := by
  have hx := (lp3_set_nonempty_iff X).1 hX
  have hy := (lp3_set_nonempty_iff Y).1 hY
  simp only [pimage₂, exists_lp3_iff]
  simp [LP3.disj]
  grind

theorem img_lp_neg_mem (X : PSet LP3) :
    (pimage LP3.neg X .t ↔ X .f) ∧
    (pimage LP3.neg X .f ↔ X .t) ∧
    (pimage LP3.neg X .b ↔ X .b) := by
  simp only [pimage, exists_lp3_iff]
  simp [LP3.neg]

theorem lpThetaBits_conj
    (tX bX fX tY bY fY : Bool)
    (hX : tX = true ∨ bX = true ∨ fX = true)
    (hY : tY = true ∨ bY = true ∨ fY = true) :
    lpThetaBits (tX && tY)
      ((bX && (tY || bY)) || (bY && (tX || bX))) (fX || fY) =
      conj4 (lpThetaBits tX bX fX) (lpThetaBits tY bY fY) := by
  cases tX <;> cases bX <;> cases fX <;>
    cases tY <;> cases bY <;> cases fY <;>
      simp_all [lpThetaBits, conj4, BuddhistComparativeLogic.mk, tr, fa]

theorem lpThetaBits_disj
    (tX bX fX tY bY fY : Bool)
    (hX : tX = true ∨ bX = true ∨ fX = true)
    (hY : tY = true ∨ bY = true ∨ fY = true) :
    lpThetaBits (tX || tY)
      ((bX && (fY || bY)) || (bY && (fX || bX))) (fX && fY) =
      disj4 (lpThetaBits tX bX fX) (lpThetaBits tY bY fY) := by
  cases tX <;> cases bX <;> cases fX <;>
    cases tY <;> cases bY <;> cases fY <;>
      simp_all [lpThetaBits, disj4, BuddhistComparativeLogic.mk, tr, fa]

theorem lpThetaBits_neg (t b f : Bool) :
    lpThetaBits f b t = neg4 (lpThetaBits t b f) := by
  cases t <;> cases b <;> cases f <;>
    simp [lpThetaBits, neg4, BuddhistComparativeLogic.mk, tr, fa]

theorem lpTheta_hom_conj (X Y : PSet LP3)
    (hX : pnonempty X) (hY : pnonempty Y) :
    lpTheta (pimage₂ LP3.conj X Y) = conj4 (lpTheta X) (lpTheta Y) := by
  rcases img_lp_conj_mem X Y hX hY with ⟨hT, hF, hB⟩
  have hx := (lp3_set_nonempty_iff X).1 hX
  have hy := (lp3_set_nonempty_iff Y).1 hY
  unfold lpTheta
  rw [propBool_iff hT, propBool_iff hB, propBool_iff hF]
  simp only [propBool_and, propBool_or]
  have hxBits : propBool (X .t) = true ∨ propBool (X .b) = true ∨
      propBool (X .f) = true := by
    rcases hx with hx | hx | hx
    · exact Or.inl ((propBool_eq_true _).2 hx)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hx))
    · exact Or.inr (Or.inr ((propBool_eq_true _).2 hx))
  have hyBits : propBool (Y .t) = true ∨ propBool (Y .b) = true ∨
      propBool (Y .f) = true := by
    rcases hy with hy | hy | hy
    · exact Or.inl ((propBool_eq_true _).2 hy)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hy))
    · exact Or.inr (Or.inr ((propBool_eq_true _).2 hy))
  exact lpThetaBits_conj _ _ _ _ _ _ hxBits hyBits

theorem lpTheta_hom_disj (X Y : PSet LP3)
    (hX : pnonempty X) (hY : pnonempty Y) :
    lpTheta (pimage₂ LP3.disj X Y) = disj4 (lpTheta X) (lpTheta Y) := by
  rcases img_lp_disj_mem X Y hX hY with ⟨hF, hT, hB⟩
  have hx := (lp3_set_nonempty_iff X).1 hX
  have hy := (lp3_set_nonempty_iff Y).1 hY
  unfold lpTheta
  rw [propBool_iff hT, propBool_iff hB, propBool_iff hF]
  simp only [propBool_and, propBool_or]
  have hxBits : propBool (X .t) = true ∨ propBool (X .b) = true ∨
      propBool (X .f) = true := by
    rcases hx with hx | hx | hx
    · exact Or.inl ((propBool_eq_true _).2 hx)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hx))
    · exact Or.inr (Or.inr ((propBool_eq_true _).2 hx))
  have hyBits : propBool (Y .t) = true ∨ propBool (Y .b) = true ∨
      propBool (Y .f) = true := by
    rcases hy with hy | hy | hy
    · exact Or.inl ((propBool_eq_true _).2 hy)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hy))
    · exact Or.inr (Or.inr ((propBool_eq_true _).2 hy))
  exact lpThetaBits_disj _ _ _ _ _ _ hxBits hyBits

theorem lpTheta_hom_neg (X : PSet LP3) :
    lpTheta (pimage LP3.neg X) = neg4 (lpTheta X) := by
  rcases img_lp_neg_mem X with ⟨hT, hF, hB⟩
  unfold lpTheta
  rw [propBool_iff hT, propBool_iff hB, propBool_iff hF]
  exact lpThetaBits_neg _ _ _

theorem lpTheta_hom_eval (Vn : α → PSet LP3) (A : Fm α)
    (hV : ∀ a, pnonempty (Vn a)) :
    lpTheta (peval LP3.neg LP3.conj LP3.disj Vn A) =
      mvEval neg4 conj4 disj4 (fun a => lpTheta (Vn a)) A := by
  induction A with
  | atom _ => rfl
  | neg A ih =>
      rw [peval, mvEval, lpTheta_hom_neg, ih]
  | conj A C ihA ihC =>
      have hA := peval_nonempty LP3.neg LP3.conj LP3.disj Vn A hV
      have hC := peval_nonempty LP3.neg LP3.conj LP3.disj Vn C hV
      rw [peval, mvEval, lpTheta_hom_conj _ _ hA hC, ihA, ihC]
  | disj A C ihA ihC =>
      have hA := peval_nonempty LP3.neg LP3.conj LP3.disj Vn A hV
      have hC := peval_nonempty LP3.neg LP3.conj LP3.disj Vn C hV
      rw [peval, mvEval, lpTheta_hom_disj _ _ hA hC, ihA, ihC]

def lpLift : TV4 → PSet LP3
  | T => psingleton .t
  | B => psingleton .b
  | N => fun x => x = .t ∨ x = .f
  | F => psingleton .f

theorem lpLift_nonempty (x : TV4) : pnonempty (lpLift x) := by
  cases x
  · exact ⟨.t, rfl⟩
  · exact ⟨.b, rfl⟩
  · exact ⟨.t, Or.inl rfl⟩
  · exact ⟨.f, rfl⟩

theorem lpTheta_lpLift (x : TV4) : lpTheta (lpLift x) = x := by
  classical
  cases x <;>
    simp [lpTheta, lpThetaBits, lpLift, psingleton, propBool]

theorem lp_upsat_iff (Vn : α → PSet LP3) (A : Fm α)
    (hV : ∀ a, pnonempty (Vn a)) :
    upsat LP3.logic Vn A ↔
      mvFDE.sat (fun a => lpTheta (Vn a)) A := by
  have hne := peval_nonempty LP3.neg LP3.conj LP3.disj Vn A hV
  change psubset (peval LP3.neg LP3.conj LP3.disj Vn A)
      LP3.logic.designated ↔
    mvFDE.designated (mvEval neg4 conj4 disj4 (fun a => lpTheta (Vn a)) A)
  rw [← lpTheta_hom_eval Vn A hV]
  exact lpTheta_designated _ hne

theorem pos_up_lp_is_fde (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails LP3.logic Γ A ↔ mvFDE.entails Γ A := by
  constructor
  · intro h w hprem
    let Vn : α → PSet LP3 := fun a => lpLift (w a)
    have hpos : ∀ a, pnonempty (Vn a) := by
      intro a
      exact lpLift_nonempty (w a)
    have hinv : (fun a => lpTheta (Vn a)) = w := by
      funext a
      exact lpTheta_lpLift (w a)
    have hpremUp : ∀ C, Γ C → upsat LP3.logic Vn C := by
      intro C hC
      apply (lp_upsat_iff Vn C hpos).2
      rw [hinv]
      exact hprem C hC
    have hout := h Vn hpos hpremUp
    have hfde := (lp_upsat_iff Vn A hpos).1 hout
    rwa [hinv] at hfde
  · intro h Vn hpos hprem
    apply (lp_upsat_iff Vn A hpos).2
    exact h (fun a => lpTheta (Vn a))
      (fun C hC => (lp_upsat_iff Vn C hpos).1 (hprem C hC))

theorem priest_open_question_lp (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails LP3.logic Γ A ↔
      mvFDE.entails (restrictToAtoms Γ A) A := by
  rw [upentails_variable_inclusion, pos_up_lp_is_fde]

theorem lp_excluded_middle_valid :
    LP3.logic.valid (disj (atom p) (neg (atom p))) := by
  rw [MVLogic.valid_iff_all_sat]
  intro v
  cases hv : v p <;>
    simp [MVLogic.sat, MVLogic.eval, mvEval, LP3.logic, LP3.neg, LP3.disj, hv]

theorem lp_universal_excluded_middle_fails :
    ¬ upentails LP3.logic emptyTheory (disj (atom p) (neg (atom p))) := by
  rw [priest_open_question_lp]
  intro h
  have hout := h (fun _ => N) (fun _ hFalse => False.elim hFalse.1)
  change tr (disj4 N (neg4 N)) = true at hout
  simp [neg4, disj4, BuddhistComparativeLogic.mk, tr, fa] at hout

end BuddhistComparativeLogic
