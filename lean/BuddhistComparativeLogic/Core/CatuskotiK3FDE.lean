/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.UniversalDesignationMore

/-!
# Catuṣkoṭi, K3, and FDE

This module makes precise a limited algebraic comparison.  Strong Kleene K3
is the `T/N/F` (non-glut) submatrix of FDE.  The embedding preserves the
connectives, formula evaluation, designation, and the catuṣkoṭi classifier.
Consequently, K3 consequence is exactly FDE consequence restricted to
valuations with no `B` values.  Unrestricted FDE consequence is strictly
weaker, as the familiar contradiction countermodel shows.

The final section records a separate boundary for plurivalent semantics.
Classifying a set by existential designation (`pkoti_of`) and classifying it
by universal designation need not give the same corner.  This is a fact about
the selected quantifier over values, not a claim that either construction is
the historical meaning of the four alternatives.
-/

namespace BuddhistComparativeLogic

open Fm TV4 Koti

namespace CatuskotiK3FDE

/-! ## K3 as the non-glut FDE submatrix -/

/-- The canonical inclusion of strong Kleene values into FDE. -/
def k3Embed : K3 → TV4
  | .t => T
  | .u => N
  | .f => F

/-- A retraction used only after ruling out the FDE glut.  Its value at `B`
is deliberately arbitrary; every theorem using it states the no-glut premise.
-/
def k3Retract : TV4 → K3
  | T => .t
  | B => .u
  | N => .u
  | F => .f

theorem k3Embed_injective : Function.Injective k3Embed := by
  intro x y h
  cases x <;> cases y <;> simp_all [k3Embed]

@[simp] theorem k3Retract_embed (x : K3) :
    k3Retract (k3Embed x) = x := by
  cases x <;> rfl

theorem k3Embed_range_iff (y : TV4) :
    (∃ x, k3Embed x = y) ↔ y ≠ B := by
  constructor
  · rintro ⟨x, rfl⟩
    cases x <;> decide
  · intro h
    cases y with
    | T => exact ⟨.t, rfl⟩
    | B => exact False.elim (h rfl)
    | N => exact ⟨.u, rfl⟩
    | F => exact ⟨.f, rfl⟩

theorem k3Embed_retract_of_not_glut (y : TV4) (h : y ≠ B) :
    k3Embed (k3Retract y) = y := by
  cases y <;> simp_all [k3Embed, k3Retract]

@[simp] theorem k3Embed_neg (x : K3) :
    k3Embed (K3.neg x) = neg4 (k3Embed x) := by
  cases x <;> rfl

@[simp] theorem k3Embed_conj (x y : K3) :
    k3Embed (K3.conj x y) = conj4 (k3Embed x) (k3Embed y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem k3Embed_disj (x y : K3) :
    k3Embed (K3.disj x y) = disj4 (k3Embed x) (k3Embed y) := by
  cases x <;> cases y <;> rfl

/-- Formula evaluation commutes with the K3-to-FDE inclusion. -/
theorem eval_k3Embed (v : α → K3) (A : Fm α) :
    k3Embed (mvEval K3.neg K3.conj K3.disj v A) =
      mvEval neg4 conj4 disj4 (fun a => k3Embed (v a)) A := by
  induction A with
  | atom _ => rfl
  | neg A ih => simp [mvEval, ih]
  | conj A C ihA ihC => simp [mvEval, ihA, ihC]
  | disj A C ihA ihC => simp [mvEval, ihA, ihC]

theorem designated_k3Embed (x : K3) :
    K3.logic.designated x ↔ mvFDE.designated (k3Embed x) := by
  cases x <;> simp [K3.logic, mvFDE, k3Embed, tr]

theorem sat_k3Embed (v : α → K3) (A : Fm α) :
    K3.logic.sat v A ↔
      mvFDE.sat (fun a => k3Embed (v a)) A := by
  change K3.logic.designated (mvEval K3.neg K3.conj K3.disj v A) ↔
    mvFDE.designated
      (mvEval neg4 conj4 disj4 (fun a => k3Embed (v a)) A)
  rw [← eval_k3Embed]
  exact designated_k3Embed _

/-- FDE consequence after explicitly restricting every atomic value to the
non-glut submatrix. -/
def fdeEntailsNoGluts (Γ : MVLogic.Theory α) (A : Fm α) : Prop :=
  ∀ v : α → TV4, (∀ a, v a ≠ B) →
    (∀ C, Γ C → mvFDE.sat v C) → mvFDE.sat v A

theorem sat_retract_of_no_gluts (v : α → TV4)
    (hng : ∀ a, v a ≠ B) (A : Fm α) :
    K3.logic.sat (fun a => k3Retract (v a)) A ↔ mvFDE.sat v A := by
  have hv : (fun a => k3Embed (k3Retract (v a))) = v := by
    funext a
    exact k3Embed_retract_of_not_glut (v a) (hng a)
  simpa only [hv] using sat_k3Embed (fun a => k3Retract (v a)) A

/-- Exact scope theorem: K3 consequence is FDE consequence over precisely
the valuations that omit the glut value. -/
theorem k3_entails_iff_fde_no_gluts (Γ : MVLogic.Theory α) (A : Fm α) :
    K3.logic.entails Γ A ↔ fdeEntailsNoGluts Γ A := by
  constructor
  · intro h v hng hprem
    have bridge (C : Fm α) :
        K3.logic.sat (fun a => k3Retract (v a)) C ↔ mvFDE.sat v C :=
      sat_retract_of_no_gluts v hng C
    exact (bridge A).1
      (h (fun a => k3Retract (v a))
        (fun C hC => (bridge C).2 (hprem C hC)))
  · intro h w hprem
    let v : α → TV4 := fun a => k3Embed (w a)
    have hng : ∀ a, v a ≠ B := by
      intro a
      cases hwa : w a <;> simp [v, k3Embed, hwa]
    have bridge (C : Fm α) : K3.logic.sat w C ↔ mvFDE.sat v C := by
      exact sat_k3Embed w C
    exact (bridge A).2
      (h v hng (fun C hC => (bridge C).1 (hprem C hC)))

theorem fde_entails_implies_k3_entails
    {Γ : MVLogic.Theory α} {A : Fm α}
    (h : mvFDE.entails Γ A) : K3.logic.entails Γ A := by
  rw [k3_entails_iff_fde_no_gluts]
  intro v _ hprem
  exact h v hprem

/-- A finite separating case for the reverse consequence direction.  K3 has
no valuation satisfying both `p` and `¬p`; FDE has the glut `B`, from which an
unrelated gap-valued `q` does not follow. -/
theorem explosion_strictly_separates_k3_from_fde :
    K3.logic.entails K3.contradictionPremises (.atom Atom.q) ∧
      ¬ mvFDE.entails K3.contradictionPremises (.atom Atom.q) := by
  constructor
  · exact K3.explosion
  · intro h
    have hq := h glut_p (by
      intro C hC
      rcases hC with hC | hC
      · cases hC
        rfl
      · cases hC
        rfl)
    change tr N = true at hq
    exact Bool.noConfusion hq

/-! ## Exact four-corner image -/

theorem fde_corner_table :
    kotiOf des4 neg4 T = Koti.K1 ∧
      kotiOf des4 neg4 F = Koti.K2 ∧
      kotiOf des4 neg4 B = Koti.K3 ∧
      kotiOf des4 neg4 N = Koti.K4 := by
  decide

/-- In the four-value matrix the four-corner classifier loses no information.
-/
theorem fde_corner_injective :
    Function.Injective (kotiOf des4 neg4) := by
  intro x y h
  cases x <;> cases y <;> simp_all [kotiOf, des4, neg4, tr, fa, BuddhistComparativeLogic.mk]

theorem fde_both_corner_iff (x : TV4) :
    kotiOf des4 neg4 x = Koti.K3 ↔ x = B := by
  cases x <;> decide

theorem fde_neither_corner_iff (x : TV4) :
    kotiOf des4 neg4 x = Koti.K4 ↔ x = N := by
  cases x <;> decide

/-- The K3 inclusion preserves the classifier built from designation and
negation. -/
theorem k3_corner_preserved (x : K3) :
    kotiOf des4 neg4 (k3Embed x) = kotiOf K3.des K3.neg x := by
  cases x <;> rfl

theorem k3_has_no_both_corner (x : K3) :
    kotiOf des4 neg4 (k3Embed x) ≠ Koti.K3 := by
  cases x <;> decide

theorem k3_corner_image_exact (k : Koti) :
    (∃ x : K3, kotiOf des4 neg4 (k3Embed x) = k) ↔
      k = Koti.K1 ∨ k = Koti.K2 ∨ k = Koti.K4 := by
  simpa only [k3_corner_preserved, K3.realizable] using K3.corners k

/-! ## Existential and universal set classification -/

/-- A four-corner classifier formed by universally quantifying designation
over a value set.  `pkoti_of` uses existential intersection instead. -/
noncomputable def universalKoti (L : MVLogic V) (S : PSet V) : Koti :=
  match propBool (psubset S L.designated),
      propBool (psubset (pimage L.neg S) L.designated) with
  | true, false => Koti.K1
  | false, true => Koti.K2
  | true, true => Koti.K3
  | false, false => Koti.K4

theorem universalKoti_positive_iff (L : MVLogic V) (S : PSet V) :
    psubset S L.designated ↔
      universalKoti L S = Koti.K1 ∨ universalKoti L S = Koti.K3 := by
  classical
  unfold universalKoti
  cases hp : propBool (psubset S L.designated) <;>
    cases hn : propBool (psubset (pimage L.neg S) L.designated) <;>
      simp_all [propBool_eq_true, propBool_eq_false]

theorem universalKoti_negative_iff (L : MVLogic V) (S : PSet V) :
    psubset (pimage L.neg S) L.designated ↔
      universalKoti L S = Koti.K2 ∨ universalKoti L S = Koti.K3 := by
  classical
  unfold universalKoti
  cases hp : propBool (psubset S L.designated) <;>
    cases hn : propBool (psubset (pimage L.neg S) L.designated) <;>
      simp_all [propBool_eq_true, propBool_eq_false]

theorem existentialKoti_positive_iff (L : MVLogic V) (S : PSet V) :
    pintersects S L.designated ↔
      pkoti_of L S = Koti.K1 ∨ pkoti_of L S = Koti.K3 := by
  classical
  unfold pkoti_of
  cases hp : propBool (pintersects S L.designated) <;>
    cases hn : propBool (pintersects (pimage L.neg S) L.designated) <;>
      simp_all [propBool_eq_true, propBool_eq_false]

theorem existentialKoti_negative_iff (L : MVLogic V) (S : PSet V) :
    pintersects (pimage L.neg S) L.designated ↔
      pkoti_of L S = Koti.K2 ∨ pkoti_of L S = Koti.K3 := by
  classical
  unfold pkoti_of
  cases hp : propBool (pintersects S L.designated) <;>
    cases hn : propBool (pintersects (pimage L.neg S) L.designated) <;>
      simp_all [propBool_eq_true, propBool_eq_false]

/-- The first bit of the universally quantified classifier is exactly the
existing universal satisfaction relation. -/
theorem upsat_iff_universalKoti_positive
    (L : MVLogic V) (Vn : α → PSet V) (A : Fm α) :
    upsat L Vn A ↔
      universalKoti L (peval L.neg L.mconj L.mdisj Vn A) = Koti.K1 ∨
      universalKoti L (peval L.neg L.mconj L.mdisj Vn A) = Koti.K3 := by
  exact universalKoti_positive_iff L
    (peval L.neg L.mconj L.mdisj Vn A)

/-- The second bit is universal satisfaction of the formula's negation. -/
theorem upsat_neg_iff_universalKoti_negative
    (L : MVLogic V) (Vn : α → PSet V) (A : Fm α) :
    upsat L Vn (.neg A) ↔
      universalKoti L (peval L.neg L.mconj L.mdisj Vn A) = Koti.K2 ∨
      universalKoti L (peval L.neg L.mconj L.mdisj Vn A) = Koti.K3 := by
  exact universalKoti_negative_iff L
    (peval L.neg L.mconj L.mdisj Vn A)

/-- The corresponding first-bit fact for existential plurivalent
satisfaction. -/
theorem psat_iff_existentialKoti_positive
    (L : MVLogic V) (Vn : α → PSet V) (A : Fm α) :
    psat L Vn A ↔
      pkoti_of L (peval L.neg L.mconj L.mdisj Vn A) = Koti.K1 ∨
      pkoti_of L (peval L.neg L.mconj L.mdisj Vn A) = Koti.K3 := by
  exact existentialKoti_positive_iff L
    (peval L.neg L.mconj L.mdisj Vn A)

/-- The corresponding second-bit fact for existential satisfaction. -/
theorem psat_neg_iff_existentialKoti_negative
    (L : MVLogic V) (Vn : α → PSet V) (A : Fm α) :
    psat L Vn (.neg A) ↔
      pkoti_of L (peval L.neg L.mconj L.mdisj Vn A) = Koti.K2 ∨
      pkoti_of L (peval L.neg L.mconj L.mdisj Vn A) = Koti.K3 := by
  exact existentialKoti_negative_iff L
    (peval L.neg L.mconj L.mdisj Vn A)

/-- Empty value sets expose the quantifier boundary: both universal claims
hold vacuously, while neither existential claim has a witness. -/
theorem empty_set_separates_universal_and_existential (L : MVLogic V) :
    universalKoti L (pempty : PSet V) = Koti.K3 ∧
      pkoti_of L (pempty : PSet V) = Koti.K4 := by
  classical
  constructor
  · simp [universalKoti, propBool, psubset, pimage, pempty]
  · exact pkoti_empty L

/-- On a singleton the two quantifier policies coincide. -/
theorem singleton_universal_eq_existential (L : MVLogic V) (x : V) :
    universalKoti L (psingleton x) = pkoti_of L (psingleton x) := by
  classical
  by_cases hp : L.designated x <;>
    by_cases hn : L.designated (L.neg x) <;>
      simp_all [universalKoti, pkoti_of, propBool, psubset, pintersects,
        pimage, psingleton]

end CatuskotiK3FDE

end BuddhistComparativeLogic
