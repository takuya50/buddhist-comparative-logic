/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.UniversalDesignation

/-!
# Universal designation over FDE

Lean counterpart of `isabelle/Core/UniversalDesignationFDE.thy`.  The first half is
uniform in the chosen many-valued base: unrestricted universal designation
reduces to positive plurivalence after retaining only premises whose atoms
occur in the conclusion.  The second half verifies Priest's `theta` map for
FDE and thereby reduces positive plurivalent FDE back to ordinary FDE.

Predicate sets (`PSet`) replace Isabelle/HOL sets.  Several Isabelle theorem
bundles with four simultaneous conclusions are represented below as a single
conjunction of four propositions.
-/

namespace BuddhistComparativeLogic

open Fm TV4 Atom

/-! ## Generic facts about image lifting -/

theorem pnonempty_iff_ne_empty (S : PSet α) :
    pnonempty S ↔ S ≠ pempty := by
  classical
  constructor
  · rintro ⟨x, hx⟩ hEq
    rw [hEq] at hx
    exact hx
  · intro hne
    apply Classical.byContradiction
    intro hn
    apply hne
    apply pset_ext
    intro x
    constructor
    · intro hx
      exact False.elim (hn ⟨x, hx⟩)
    · intro hx
      exact False.elim hx

theorem peval_cong (neg : V → V) (mconj mdisj : V → V → V)
    (Vn Wn : α → PSet V) (A : Fm α)
    (h : ∀ a, atoms A a → Vn a = Wn a) :
    peval neg mconj mdisj Vn A = peval neg mconj mdisj Wn A := by
  induction A with
  | atom a => exact h a rfl
  | neg A ih =>
      rw [peval, peval, ih (fun a ha => h a ha)]
  | conj A C ihA ihC =>
      rw [peval, peval,
        ihA (fun a ha => h a (Or.inl ha)),
        ihC (fun a ha => h a (Or.inr ha))]
  | disj A C ihA ihC =>
      rw [peval, peval,
        ihA (fun a ha => h a (Or.inl ha)),
        ihC (fun a ha => h a (Or.inr ha))]

theorem peval_empty_infect_at (neg : V → V) (mconj mdisj : V → V → V)
    (Vn : α → PSet V) (A : Fm α) {a : α}
    (ha : atoms A a) (hv : Vn a = pempty) :
    peval neg mconj mdisj Vn A = pempty := by
  induction A with
  | atom b =>
      change a = b at ha
      cases ha
      exact hv
  | neg A ih =>
      rw [peval, ih ha, pimage_empty]
  | conj A C ihA ihC =>
      cases ha with
      | inl ha => rw [peval, ihA ha, pimage₂_empty_left]
      | inr ha => rw [peval, ihC ha, pimage₂_empty_right]
  | disj A C ihA ihC =>
      cases ha with
      | inl ha => rw [peval, ihA ha, pimage₂_empty_left]
      | inr ha => rw [peval, ihC ha, pimage₂_empty_right]

theorem peval_empty_infect (neg : V → V) (mconj mdisj : V → V → V)
    (Vn : α → PSet V) (A : Fm α)
    (h : ∃ a, atoms A a ∧ Vn a = pempty) :
    peval neg mconj mdisj Vn A = pempty := by
  rcases h with ⟨a, ha, hv⟩
  exact peval_empty_infect_at neg mconj mdisj Vn A ha hv

/-- The source theorem `peval_nonempty` is already provided by
`BuddhistComparativeLogic.Core.Plurivalent`; this atom-restricted form is convenient below. -/
theorem peval_nonempty_on (neg : V → V) (mconj mdisj : V → V → V)
    (Vn : α → PSet V) (A : Fm α)
    (hV : ∀ a, atoms A a → pnonempty (Vn a)) :
    pnonempty (peval neg mconj mdisj Vn A) := by
  induction A with
  | atom a => exact hV a rfl
  | neg A ih =>
      exact (pimage_nonempty_iff _ _).2
        (ih (fun a ha => hV a ha))
  | conj A C ihA ihC =>
      exact (pimage₂_nonempty_iff _ _ _).2
        ⟨ihA (fun a ha => hV a (Or.inl ha)),
         ihC (fun a ha => hV a (Or.inr ha))⟩
  | disj A C ihA ihC =>
      exact (pimage₂_nonempty_iff _ _ _).2
        ⟨ihA (fun a ha => hV a (Or.inl ha)),
         ihC (fun a ha => hV a (Or.inr ha))⟩

theorem peval_sing (neg : V → V) (mconj mdisj : V → V → V)
    (w : α → V) (A : Fm α) :
    peval neg mconj mdisj (fun a => psingleton (w a)) A =
      psingleton (mvEval neg mconj mdisj w A) :=
  peval_singleton neg mconj mdisj w A

theorem upsat_sing_iff (L : MVLogic V) (w : α → V) (A : Fm α) :
    upsat L (fun a => psingleton (w a)) A ↔ L.sat w A := by
  rw [upsat, peval_sing]
  simp [psubset, psingleton, MVLogic.sat, MVLogic.eval]

/-! ## The generic variable-inclusion reduction -/

def pos_upentails (L : MVLogic V) (Γ : MVLogic.Theory α) (A : Fm α) : Prop :=
  ∀ Vn, (∀ a, pnonempty (Vn a)) →
    (∀ C, Γ C → upsat L Vn C) → upsat L Vn A

theorem upentails_variable_inclusion (L : MVLogic V) [Inhabited V]
    (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails L Γ A ↔ pos_upentails L (restrictToAtoms Γ A) A := by
  classical
  constructor
  · intro h Vpos hpos hprem
    let Vn : α → PSet V := fun a => if atoms A a then Vpos a else pempty
    have agree (C : Fm α) (hsub : psubset (atoms C) (atoms A)) :
        peval L.neg L.mconj L.mdisj Vn C =
          peval L.neg L.mconj L.mdisj Vpos C := by
      apply peval_cong
      intro a ha
      simp [Vn, hsub a ha]
    have hpremAll : ∀ C, Γ C → upsat L Vn C := by
      intro C hC
      by_cases hsub : psubset (atoms C) (atoms A)
      · change psubset (peval L.neg L.mconj L.mdisj Vn C) L.designated
        rw [agree C hsub]
        exact hprem C ⟨hC, hsub⟩
      · apply upsat_empty
        apply peval_empty_infect
        have hex : ∃ a, atoms C a ∧ ¬ atoms A a := by
          apply Classical.byContradiction
          intro hn
          apply hsub
          intro a ha
          apply Classical.byContradiction
          intro hna
          exact hn ⟨a, ha, hna⟩
        rcases hex with ⟨a, ha, hna⟩
        exact ⟨a, ha, by simp [Vn, hna]⟩
    have hout := h Vn hpremAll
    change psubset (peval L.neg L.mconj L.mdisj Vn A) L.designated at hout
    rw [agree A (fun _ ha => ha)] at hout
    exact hout
  · intro h Vn hprem
    by_cases hinfect : ∃ a, atoms A a ∧ Vn a = pempty
    · apply upsat_empty
      exact peval_empty_infect L.neg L.mconj L.mdisj Vn A hinfect
    · let Vpos : α → PSet V := fun a =>
        if pnonempty (Vn a) then Vn a else psingleton default
      have hpos : ∀ a, pnonempty (Vpos a) := by
        intro a
        by_cases ha : pnonempty (Vn a)
        · simp [Vpos, ha]
        · exact ⟨default, by simp [Vpos, ha, psingleton]⟩
      have agree (C : Fm α) (hsub : psubset (atoms C) (atoms A)) :
          peval L.neg L.mconj L.mdisj Vpos C =
            peval L.neg L.mconj L.mdisj Vn C := by
        apply peval_cong
        intro a ha
        have hne : pnonempty (Vn a) := by
          apply Classical.byContradiction
          intro hn
          apply hinfect
          have hempty : Vn a = pempty := by
            apply Classical.byContradiction
            intro hne
            exact hn ((pnonempty_iff_ne_empty (Vn a)).2 hne)
          exact ⟨a, hsub a ha, hempty⟩
        simp [Vpos, hne]
      have hpremPos : ∀ C, restrictToAtoms Γ A C → upsat L Vpos C := by
        intro C hC
        change psubset (peval L.neg L.mconj L.mdisj Vpos C) L.designated
        rw [agree C hC.2]
        exact hprem C hC.1
      have hout := h Vpos hpos hpremPos
      change psubset (peval L.neg L.mconj L.mdisj Vpos A) L.designated at hout
      rw [agree A (fun _ ha => ha)] at hout
      exact hout

/-! ## Priest's `theta` map for the FDE base -/

theorem exists_tv4_iff (P : TV4 → Prop) :
    (∃ x, P x) ↔ P T ∨ P B ∨ P N ∨ P F := by
  constructor
  · rintro ⟨x, hx⟩
    cases x <;> simp_all
  · intro h
    rcases h with h | h | h | h
    · exact ⟨T, h⟩
    · exact ⟨B, h⟩
    · exact ⟨N, h⟩
    · exact ⟨F, h⟩

theorem forall_tv4_iff (P : TV4 → Prop) :
    (∀ x, P x) ↔ P T ∧ P B ∧ P N ∧ P F := by
  constructor
  · intro h
    exact ⟨h T, h B, h N, h F⟩
  · rintro ⟨hT, hB, hN, hF⟩ x
    cases x <;> assumption

def theta_bits (t _b n f : Bool) : TV4 :=
  if n then N else if t && f then N else if t then T else if f then F else B

noncomputable def theta (X : PSet TV4) : TV4 :=
  theta_bits (propBool (X T)) (propBool (X B))
    (propBool (X N)) (propBool (X F))

theorem tv4_set_nonempty_iff (X : PSet TV4) :
    pnonempty X ↔ X T ∨ X B ∨ X N ∨ X F :=
  exists_tv4_iff X

theorem propBool_iff {P Q : Prop} (h : P ↔ Q) :
    propBool P = propBool Q := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp_all [propBool]

theorem propBool_and (P Q : Prop) :
    propBool (P ∧ Q) = (propBool P && propBool Q) := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp_all [propBool]

theorem propBool_or (P Q : Prop) :
    propBool (P ∨ Q) = (propBool P || propBool Q) := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp_all [propBool]

theorem fde_designated_subset_iff (X : PSet TV4) :
    psubset X mvFDE.designated ↔ ¬ X N ∧ ¬ X F := by
  constructor
  · intro h
    constructor
    · intro hn
      have := h N hn
      exact Bool.noConfusion this
    · intro hf
      have := h F hf
      exact Bool.noConfusion this
  · rintro ⟨hn, hf⟩ x hx
    cases x <;> simp_all [mvFDE, tr]

theorem theta_designated (X : PSet TV4) (hX : pnonempty X) :
    psubset X mvFDE.designated ↔ mvFDE.designated (theta X) := by
  classical
  rw [fde_designated_subset_iff]
  have hmem := (tv4_set_nonempty_iff X).1 hX
  by_cases xt : X T <;> by_cases xb : X B <;>
    by_cases xn : X N <;> by_cases xf : X F <;>
      simp_all [theta, theta_bits, propBool, mvFDE, tr]

/-! The FDE tables, packaged as conjunctions because Lean declarations have
one conclusion rather than Isabelle's theorem bundles. -/

theorem conj4_eq (x y : TV4) :
    (conj4 x y = T ↔ x = T ∧ y = T) ∧
    (conj4 x y = F ↔ x = F ∨ y = F ∨ (x = B ∧ y = N) ∨
      (x = N ∧ y = B)) ∧
    (conj4 x y = B ↔ (x = B ∧ (y = T ∨ y = B)) ∨
      (y = B ∧ (x = T ∨ x = B))) ∧
    (conj4 x y = N ↔ (x = N ∧ (y = T ∨ y = N)) ∨
      (y = N ∧ (x = T ∨ x = N))) := by
  cases x <;> cases y <;> decide

theorem disj4_eq (x y : TV4) :
    (disj4 x y = F ↔ x = F ∧ y = F) ∧
    (disj4 x y = T ↔ x = T ∨ y = T ∨ (x = B ∧ y = N) ∨
      (x = N ∧ y = B)) ∧
    (disj4 x y = B ↔ (x = B ∧ (y = F ∨ y = B)) ∨
      (y = B ∧ (x = F ∨ x = B))) ∧
    (disj4 x y = N ↔ (x = N ∧ (y = F ∨ y = N)) ∨
      (y = N ∧ (x = F ∨ x = N))) := by
  cases x <;> cases y <;> decide

theorem neg4_eq (x : TV4) :
    (neg4 x = T ↔ x = F) ∧
    (neg4 x = F ↔ x = T) ∧
    (neg4 x = B ↔ x = B) ∧
    (neg4 x = N ↔ x = N) := by
  cases x <;> decide

theorem tv4_eq_flip (x y : TV4) :
    (T = conj4 x y ↔ conj4 x y = T) ∧
    (B = conj4 x y ↔ conj4 x y = B) ∧
    (N = conj4 x y ↔ conj4 x y = N) ∧
    (F = conj4 x y ↔ conj4 x y = F) ∧
    (T = disj4 x y ↔ disj4 x y = T) ∧
    (B = disj4 x y ↔ disj4 x y = B) ∧
    (N = disj4 x y ↔ disj4 x y = N) ∧
    (F = disj4 x y ↔ disj4 x y = F) ∧
    (T = neg4 x ↔ neg4 x = T) ∧
    (B = neg4 x ↔ neg4 x = B) ∧
    (N = neg4 x ↔ neg4 x = N) ∧
    (F = neg4 x ↔ neg4 x = F) := by
  simp [eq_comm]

theorem img_conj4_mem (X Y : PSet TV4)
    (hX : pnonempty X) (hY : pnonempty Y) :
    (pimage₂ conj4 X Y T ↔ X T ∧ Y T) ∧
    (pimage₂ conj4 X Y F ↔ X F ∨ Y F ∨ (X B ∧ Y N) ∨
      (X N ∧ Y B)) ∧
    (pimage₂ conj4 X Y B ↔ (X B ∧ (Y T ∨ Y B)) ∨
      (Y B ∧ (X T ∨ X B))) ∧
    (pimage₂ conj4 X Y N ↔ (X N ∧ (Y T ∨ Y N)) ∨
      (Y N ∧ (X T ∨ X N))) := by
  have hx := (tv4_set_nonempty_iff X).1 hX
  have hy := (tv4_set_nonempty_iff Y).1 hY
  simp only [pimage₂, exists_tv4_iff]
  simp [conj4, mk, tr, fa]
  grind

theorem img_disj4_mem (X Y : PSet TV4)
    (hX : pnonempty X) (hY : pnonempty Y) :
    (pimage₂ disj4 X Y F ↔ X F ∧ Y F) ∧
    (pimage₂ disj4 X Y T ↔ X T ∨ Y T ∨ (X B ∧ Y N) ∨
      (X N ∧ Y B)) ∧
    (pimage₂ disj4 X Y B ↔ (X B ∧ (Y F ∨ Y B)) ∨
      (Y B ∧ (X F ∨ X B))) ∧
    (pimage₂ disj4 X Y N ↔ (X N ∧ (Y F ∨ Y N)) ∨
      (Y N ∧ (X F ∨ X N))) := by
  have hx := (tv4_set_nonempty_iff X).1 hX
  have hy := (tv4_set_nonempty_iff Y).1 hY
  simp only [pimage₂, exists_tv4_iff]
  simp [disj4, mk, tr, fa]
  grind

theorem img_neg4_mem (X : PSet TV4) :
    (pimage neg4 X T ↔ X F) ∧
    (pimage neg4 X F ↔ X T) ∧
    (pimage neg4 X B ↔ X B) ∧
    (pimage neg4 X N ↔ X N) := by
  simp only [pimage, exists_tv4_iff]
  simp [neg4, mk, tr, fa]

theorem theta_bits_conj
    (tX bX nX fX tY bY nY fY : Bool)
    (hX : tX = true ∨ bX = true ∨ nX = true ∨ fX = true)
    (hY : tY = true ∨ bY = true ∨ nY = true ∨ fY = true) :
    theta_bits (tX && tY)
      ((bX && (tY || bY)) || (bY && (tX || bX)))
      ((nX && (tY || nY)) || (nY && (tX || nX)))
      (fX || fY || (bX && nY) || (nX && bY)) =
    conj4 (theta_bits tX bX nX fX) (theta_bits tY bY nY fY) := by
  cases tX <;> cases bX <;> cases nX <;> cases fX <;>
    cases tY <;> cases bY <;> cases nY <;> cases fY <;>
      simp_all [theta_bits, conj4, mk, tr, fa]

theorem theta_bits_disj
    (tX bX nX fX tY bY nY fY : Bool)
    (hX : tX = true ∨ bX = true ∨ nX = true ∨ fX = true)
    (hY : tY = true ∨ bY = true ∨ nY = true ∨ fY = true) :
    theta_bits (tX || tY || (bX && nY) || (nX && bY))
      ((bX && (fY || bY)) || (bY && (fX || bX)))
      ((nX && (fY || nY)) || (nY && (fX || nX)))
      (fX && fY) =
    disj4 (theta_bits tX bX nX fX) (theta_bits tY bY nY fY) := by
  cases tX <;> cases bX <;> cases nX <;> cases fX <;>
    cases tY <;> cases bY <;> cases nY <;> cases fY <;>
      simp_all [theta_bits, disj4, mk, tr, fa]

theorem theta_bits_neg (t b n f : Bool) :
    theta_bits f b n t = neg4 (theta_bits t b n f) := by
  cases t <;> cases b <;> cases n <;> cases f <;>
    simp [theta_bits, neg4, mk, tr, fa]

theorem theta_hom_conj (X Y : PSet TV4)
    (hX : pnonempty X) (hY : pnonempty Y) :
    theta (pimage₂ conj4 X Y) = conj4 (theta X) (theta Y) := by
  rcases img_conj4_mem X Y hX hY with ⟨hT, hF, hB, hN⟩
  have hx := (tv4_set_nonempty_iff X).1 hX
  have hy := (tv4_set_nonempty_iff Y).1 hY
  unfold theta
  rw [propBool_iff hT, propBool_iff hB, propBool_iff hN, propBool_iff hF]
  simp only [propBool_and, propBool_or]
  have hxBits : propBool (X T) = true ∨ propBool (X B) = true ∨
      propBool (X N) = true ∨ propBool (X F) = true := by
    rcases hx with hx | hx | hx | hx
    · exact Or.inl ((propBool_eq_true _).2 hx)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hx))
    · exact Or.inr (Or.inr (Or.inl ((propBool_eq_true _).2 hx)))
    · exact Or.inr (Or.inr (Or.inr ((propBool_eq_true _).2 hx)))
  have hyBits : propBool (Y T) = true ∨ propBool (Y B) = true ∨
      propBool (Y N) = true ∨ propBool (Y F) = true := by
    rcases hy with hy | hy | hy | hy
    · exact Or.inl ((propBool_eq_true _).2 hy)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hy))
    · exact Or.inr (Or.inr (Or.inl ((propBool_eq_true _).2 hy)))
    · exact Or.inr (Or.inr (Or.inr ((propBool_eq_true _).2 hy)))
  simpa [Bool.or_assoc] using
    theta_bits_conj
      (propBool (X T)) (propBool (X B)) (propBool (X N)) (propBool (X F))
      (propBool (Y T)) (propBool (Y B)) (propBool (Y N)) (propBool (Y F))
      hxBits hyBits

theorem theta_hom_disj (X Y : PSet TV4)
    (hX : pnonempty X) (hY : pnonempty Y) :
    theta (pimage₂ disj4 X Y) = disj4 (theta X) (theta Y) := by
  rcases img_disj4_mem X Y hX hY with ⟨hF, hT, hB, hN⟩
  have hx := (tv4_set_nonempty_iff X).1 hX
  have hy := (tv4_set_nonempty_iff Y).1 hY
  unfold theta
  rw [propBool_iff hT, propBool_iff hB, propBool_iff hN, propBool_iff hF]
  simp only [propBool_and, propBool_or]
  have hxBits : propBool (X T) = true ∨ propBool (X B) = true ∨
      propBool (X N) = true ∨ propBool (X F) = true := by
    rcases hx with hx | hx | hx | hx
    · exact Or.inl ((propBool_eq_true _).2 hx)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hx))
    · exact Or.inr (Or.inr (Or.inl ((propBool_eq_true _).2 hx)))
    · exact Or.inr (Or.inr (Or.inr ((propBool_eq_true _).2 hx)))
  have hyBits : propBool (Y T) = true ∨ propBool (Y B) = true ∨
      propBool (Y N) = true ∨ propBool (Y F) = true := by
    rcases hy with hy | hy | hy | hy
    · exact Or.inl ((propBool_eq_true _).2 hy)
    · exact Or.inr (Or.inl ((propBool_eq_true _).2 hy))
    · exact Or.inr (Or.inr (Or.inl ((propBool_eq_true _).2 hy)))
    · exact Or.inr (Or.inr (Or.inr ((propBool_eq_true _).2 hy)))
  simpa [Bool.or_assoc] using
    theta_bits_disj
      (propBool (X T)) (propBool (X B)) (propBool (X N)) (propBool (X F))
      (propBool (Y T)) (propBool (Y B)) (propBool (Y N)) (propBool (Y F))
      hxBits hyBits

theorem theta_hom_neg (X : PSet TV4) :
    theta (pimage neg4 X) = neg4 (theta X) := by
  rcases img_neg4_mem X with ⟨hT, hF, hB, hN⟩
  unfold theta
  rw [propBool_iff hT, propBool_iff hB, propBool_iff hN, propBool_iff hF]
  exact theta_bits_neg _ _ _ _

theorem theta_hom_eval (Vn : α → PSet TV4) (A : Fm α)
    (hV : ∀ a, pnonempty (Vn a)) :
    theta (peval neg4 conj4 disj4 Vn A) =
      mvEval neg4 conj4 disj4 (fun a => theta (Vn a)) A := by
  induction A with
  | atom _ => rfl
  | neg A ih =>
      rw [peval, mvEval, theta_hom_neg, ih]
  | conj A C ihA ihC =>
      have hA := peval_nonempty neg4 conj4 disj4 Vn A hV
      have hC := peval_nonempty neg4 conj4 disj4 Vn C hV
      rw [peval, mvEval, theta_hom_conj _ _ hA hC, ihA, ihC]
  | disj A C ihA ihC =>
      have hA := peval_nonempty neg4 conj4 disj4 Vn A hV
      have hC := peval_nonempty neg4 conj4 disj4 Vn C hV
      rw [peval, mvEval, theta_hom_disj _ _ hA hC, ihA, ihC]

/-! ## Positive universal FDE is ordinary FDE -/

theorem pos_up_fde_is_fde (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails mvFDE Γ A ↔ mvFDE.entails Γ A := by
  constructor
  · intro h w hprem
    have hpos : ∀ a, pnonempty (psingleton (w a)) := by
      intro a
      exact ⟨w a, rfl⟩
    have hpremUp : ∀ C, Γ C →
        upsat mvFDE (fun a => psingleton (w a)) C := by
      intro C hC
      exact (upsat_sing_iff mvFDE w C).2 (hprem C hC)
    exact (upsat_sing_iff mvFDE w A).1
      (h (fun a => psingleton (w a)) hpos hpremUp)
  · intro h Vn hpos hprem
    have key (C : Fm α) :
        upsat mvFDE Vn C ↔
          mvFDE.sat (fun a => theta (Vn a)) C := by
      have hne := peval_nonempty neg4 conj4 disj4 Vn C hpos
      change psubset (peval neg4 conj4 disj4 Vn C) mvFDE.designated ↔
        mvFDE.designated
          (mvEval neg4 conj4 disj4 (fun a => theta (Vn a)) C)
      rw [← theta_hom_eval Vn C hpos]
      exact theta_designated _ hne
    have hs := h (fun a => theta (Vn a))
      (fun C hC => (key C).1 (hprem C hC))
    exact (key A).2 hs

theorem priest_open_question_fde (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails mvFDE Γ A ↔ mvFDE.entails (restrictToAtoms Γ A) A := by
  rw [upentails_variable_inclusion, pos_up_fde_is_fde]

/-! The two examples from Priest's appendix. -/

theorem fde_up_conj_elim_fails :
    ¬ upentails mvFDE
      (singletonTheory (conj (atom p) (atom q))) (atom p) := by
  rw [priest_open_question_fde]
  intro h
  have hout : mvFDE.sat (fun _ => F) (atom p) := by
    apply h (fun _ => F)
    intro C hC
    rcases hC with ⟨hEq, hsub⟩
    cases hEq
    have hbad := hsub q (Or.inr rfl)
    exact False.elim (Atom.noConfusion hbad)
  change tr F = true at hout
  exact Bool.noConfusion hout

theorem fde_up_disj_intro :
    upentails mvFDE (singletonTheory (atom p))
      (disj (atom p) (atom q)) := by
  rw [priest_open_question_fde]
  intro w hprem
  have hp := hprem (atom p) ⟨rfl, fun _ ha => Or.inl ha⟩
  change tr (w p) = true at hp
  change tr (disj4 (w p) (w q)) = true
  cases hpv : w p <;> cases hqv : w q <;>
    simp_all [tr, disj4, mk, fa]

end BuddhistComparativeLogic
