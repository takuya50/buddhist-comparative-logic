/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.FDEProof

/-!
# Sound and complete proof calculi for FDE and FDE5

There are two layers. `Deriv` is the familiar lattice/De Morgan natural
deduction presentation and is proved sound and complete through a finite
disjunctive normal form. `Tableau` is an analytic signed tableau whose proof
objects close every counterexample branch produced by the connective rules.
It is also proved sound and complete. `Tableau5` adds the atom-containment
obligation exactly required by the absorbing fifth value.
-/

namespace BuddhistComparativeLogic.FDECalculus

open Fm TV4 FDEProof

/-! ## A standard sound derivation system -/

inductive Deriv : Fm α → Fm α → Prop
  | ax (X) : Deriv X X
  | cut : Deriv X Y → Deriv Y Z → Deriv X Z
  | conjE1 (X Y) : Deriv (.conj X Y) X
  | conjE2 (X Y) : Deriv (.conj X Y) Y
  | conjI : Deriv X Y → Deriv X Z → Deriv X (.conj Y Z)
  | disjI1 (X Y) : Deriv X (.disj X Y)
  | disjI2 (X Y) : Deriv Y (.disj X Y)
  | disjE : Deriv X Z → Deriv Y Z → Deriv (.disj X Y) Z
  | dist (X Y Z) : Deriv (.conj X (.disj Y Z))
      (.disj (.conj X Y) (.conj X Z))
  | dneg1 (X) : Deriv (.neg (.neg X)) X
  | dneg2 (X) : Deriv X (.neg (.neg X))
  | dmorg1 (X Y) : Deriv (.neg (.conj X Y)) (.disj (.neg X) (.neg Y))
  | dmorg2 (X Y) : Deriv (.disj (.neg X) (.neg Y)) (.neg (.conj X Y))
  | dmorg3 (X Y) : Deriv (.neg (.disj X Y)) (.conj (.neg X) (.neg Y))
  | dmorg4 (X Y) : Deriv (.conj (.neg X) (.neg Y)) (.neg (.disj X Y))

infix:50 " ⊢₄ " => Deriv

theorem deriv_sound {X Y : Fm α} (h : X ⊢₄ Y) : entails4 X Y := by
  induction h with
  | ax => exact fun _ hx => hx
  | cut _ _ ih₁ ih₂ => exact fun v hx => ih₂ v (ih₁ v hx)
  | conjE1 =>
      intro v h
      change tr (conj4 (eval4 v _) (eval4 v _)) = true at h
      change tr (eval4 v _) = true
      rw [tr_conj4, Bool.and_eq_true_iff] at h
      exact h.1
  | conjE2 =>
      intro v h
      change tr (conj4 (eval4 v _) (eval4 v _)) = true at h
      change tr (eval4 v _) = true
      rw [tr_conj4, Bool.and_eq_true_iff] at h
      exact h.2
  | conjI _ _ ih₁ ih₂ =>
      intro v hx
      change tr (conj4 (eval4 v _) (eval4 v _)) = true
      rw [tr_conj4, Bool.and_eq_true_iff]
      exact ⟨ih₁ v hx, ih₂ v hx⟩
  | disjI1 =>
      intro v hx
      change tr (disj4 (eval4 v _) (eval4 v _)) = true
      rw [tr_disj4, Bool.or_eq_true_iff]
      exact Or.inl hx
  | disjI2 =>
      intro v hy
      change tr (disj4 (eval4 v _) (eval4 v _)) = true
      rw [tr_disj4, Bool.or_eq_true_iff]
      exact Or.inr hy
  | disjE _ _ ih₁ ih₂ =>
      intro v hxy
      change tr (disj4 (eval4 v _) (eval4 v _)) = true at hxy
      rw [tr_disj4, Bool.or_eq_true_iff] at hxy
      cases hxy with
      | inl hx => exact ih₁ v hx
      | inr hy => exact ih₂ v hy
  | dist =>
      intro v h
      change tr (conj4 (eval4 v _) (disj4 (eval4 v _) (eval4 v _))) = true at h
      change tr (disj4 (conj4 (eval4 v _) (eval4 v _))
        (conj4 (eval4 v _) (eval4 v _))) = true
      simpa only [tr_conj4, tr_disj4, Bool.and_or_distrib_left] using h
  | dneg1 =>
      intro v h
      change tr (neg4 (neg4 (eval4 v _))) = true at h
      change tr (eval4 v _) = true
      simpa only [tr_neg4, fa_neg4] using h
  | dneg2 =>
      intro v h
      change tr (eval4 v _) = true at h
      change tr (neg4 (neg4 (eval4 v _))) = true
      simpa only [tr_neg4, fa_neg4] using h
  | dmorg1 =>
      intro v h
      change tr (neg4 (conj4 (eval4 v _) (eval4 v _))) = true at h
      change tr (disj4 (neg4 (eval4 v _)) (neg4 (eval4 v _))) = true
      simpa only [tr_neg4, fa_conj4, tr_disj4] using h
  | dmorg2 =>
      intro v h
      change tr (disj4 (neg4 (eval4 v _)) (neg4 (eval4 v _))) = true at h
      change tr (neg4 (conj4 (eval4 v _) (eval4 v _))) = true
      simpa only [tr_neg4, fa_conj4, tr_disj4] using h
  | dmorg3 =>
      intro v h
      change tr (neg4 (disj4 (eval4 v _) (eval4 v _))) = true at h
      change tr (conj4 (neg4 (eval4 v _)) (neg4 (eval4 v _))) = true
      simpa only [tr_neg4, fa_disj4, tr_conj4] using h
  | dmorg4 =>
      intro v h
      change tr (conj4 (neg4 (eval4 v _)) (neg4 (eval4 v _))) = true at h
      change tr (neg4 (disj4 (eval4 v _) (eval4 v _))) = true
      simpa only [tr_neg4, fa_disj4, tr_conj4] using h

theorem deriv_variable_sharing {X Y : Fm α} (h : X ⊢₄ Y) :
    pintersects (atoms X) (atoms Y) :=
  fde_variable_sharing (deriv_sound h)

theorem no_explosion_derivable {X Y : Fm α}
    (disjoint : ¬ pintersects (atoms X) (atoms Y)) : ¬ X ⊢₄ Y :=
  fun h => disjoint (deriv_variable_sharing h)

/-! ## Derived lattice rules -/

theorem deriv_conj_mono {X X' Y Y' : Fm α}
    (hx : X ⊢₄ X') (hy : Y ⊢₄ Y') :
    .conj X Y ⊢₄ .conj X' Y' :=
  .conjI (.cut (.conjE1 X Y) hx) (.cut (.conjE2 X Y) hy)

theorem deriv_disj_mono {X X' Y Y' : Fm α}
    (hx : X ⊢₄ X') (hy : Y ⊢₄ Y') :
    .disj X Y ⊢₄ .disj X' Y' :=
  .disjE (.cut hx (.disjI1 X' Y')) (.cut hy (.disjI2 X' Y'))

theorem deriv_dist_back (X Y Z : Fm α) :
    .disj (.conj X Y) (.conj X Z) ⊢₄ .conj X (.disj Y Z) := by
  apply Deriv.disjE
  · exact .conjI (.conjE1 X Y)
      (.cut (.conjE2 X Y) (.disjI1 Y Z))
  · exact .conjI (.conjE1 X Z)
      (.cut (.conjE2 X Z) (.disjI2 Y Z))

theorem deriv_conj_comm (X Y : Fm α) : .conj X Y ⊢₄ .conj Y X :=
  .conjI (.conjE2 X Y) (.conjE1 X Y)

theorem deriv_disj_comm (X Y : Fm α) : .disj X Y ⊢₄ .disj Y X :=
  .disjE (.disjI2 Y X) (.disjI1 Y X)

theorem deriv_disj_idem (X : Fm α) : .disj X X ⊢₄ X :=
  .disjE (.ax X) (.ax X)

theorem deriv_disj_absorb (X Y : Fm α) :
    .disj X (.disj X Y) ⊢₄ .disj X Y :=
  .disjE (.disjI1 X Y) (.ax (.disj X Y))

/-- The distributive law dual to the primitive `dist` rule. -/
theorem deriv_dist_dual (A C₁ C₂ : Fm α) :
    .conj (.disj A C₁) (.disj A C₂) ⊢₄ .disj A (.conj C₁ C₂) := by
  let start : Fm α := .conj (.disj A C₁) (.disj A C₂)
  let middle : Fm α := .disj (.conj (.disj A C₁) A)
    (.conj (.disj A C₁) C₂)
  have s₁ : start ⊢₄ middle := .dist (.disj A C₁) A C₂
  have left : .conj (.disj A C₁) A ⊢₄ A := .conjE2 _ _
  have right₁ : .conj (.disj A C₁) C₂ ⊢₄
      .conj C₂ (.disj A C₁) := deriv_conj_comm _ _
  have right₂ : .conj C₂ (.disj A C₁) ⊢₄
      .disj (.conj C₂ A) (.conj C₂ C₁) := .dist _ _ _
  have right₃ : .disj (.conj C₂ A) (.conj C₂ C₁) ⊢₄
      .disj A (.conj C₁ C₂) :=
    deriv_disj_mono (.conjE2 _ _) (deriv_conj_comm _ _)
  have right : .conj (.disj A C₁) C₂ ⊢₄
      .disj A (.conj C₁ C₂) :=
    .cut (.cut right₁ right₂) right₃
  have s₂ : middle ⊢₄ .disj A (.disj A (.conj C₁ C₂)) :=
    deriv_disj_mono left right
  exact .cut (.cut s₁ s₂) (deriv_disj_absorb A (.conj C₁ C₂))

/-! The natural-deduction fragment also contraposes. -/

theorem deriv_contraposition {X Y : Fm α} (h : X ⊢₄ Y) :
    .neg Y ⊢₄ .neg X := by
  induction h with
  | ax X => exact .ax (.neg X)
  | cut _ _ ih₁ ih₂ => exact .cut ih₂ ih₁
  | conjE1 X Y => exact .cut (.disjI1 (.neg X) (.neg Y)) (.dmorg2 X Y)
  | conjE2 X Y => exact .cut (.disjI2 (.neg X) (.neg Y)) (.dmorg2 X Y)
  | conjI _ _ ih₁ ih₂ =>
      exact .cut (.dmorg1 _ _) (.disjE ih₁ ih₂)
  | disjI1 X Y => exact .cut (.dmorg3 X Y) (.conjE1 (.neg X) (.neg Y))
  | disjI2 X Y => exact .cut (.dmorg3 X Y) (.conjE2 (.neg X) (.neg Y))
  | disjE _ _ ih₁ ih₂ =>
      exact .cut (.conjI ih₁ ih₂) (.dmorg4 _ _)
  | dist X Y Z =>
      have a : .neg (.disj (.conj X Y) (.conj X Z)) ⊢₄
          .conj (.neg (.conj X Y)) (.neg (.conj X Z)) := .dmorg3 _ _
      have b : .conj (.neg (.conj X Y)) (.neg (.conj X Z)) ⊢₄
          .conj (.disj (.neg X) (.neg Y)) (.disj (.neg X) (.neg Z)) :=
        deriv_conj_mono (.dmorg1 X Y) (.dmorg1 X Z)
      have c : .conj (.disj (.neg X) (.neg Y))
          (.disj (.neg X) (.neg Z)) ⊢₄
          .disj (.neg X) (.conj (.neg Y) (.neg Z)) :=
        deriv_dist_dual _ _ _
      have d : .disj (.neg X) (.conj (.neg Y) (.neg Z)) ⊢₄
          .disj (.neg X) (.neg (.disj Y Z)) :=
        deriv_disj_mono (.ax _) (.dmorg4 Y Z)
      have e : .disj (.neg X) (.neg (.disj Y Z)) ⊢₄
          .neg (.conj X (.disj Y Z)) := .dmorg2 _ _
      exact .cut (.cut (.cut (.cut a b) c) d) e
  | dneg1 X => exact .dneg2 (.neg X)
  | dneg2 X => exact .dneg1 (.neg X)
  | dmorg1 X Y =>
      have a : .neg (.disj (.neg X) (.neg Y)) ⊢₄
          .conj (.neg (.neg X)) (.neg (.neg Y)) := .dmorg3 _ _
      have b : .conj (.neg (.neg X)) (.neg (.neg Y)) ⊢₄ .conj X Y :=
        deriv_conj_mono (.dneg1 X) (.dneg1 Y)
      exact .cut (.cut a b) (.dneg2 (.conj X Y))
  | dmorg2 X Y =>
      have a : .neg (.neg (.conj X Y)) ⊢₄ .conj X Y := .dneg1 _
      have b : .conj X Y ⊢₄ .conj (.neg (.neg X)) (.neg (.neg Y)) :=
        deriv_conj_mono (.dneg2 X) (.dneg2 Y)
      exact .cut (.cut a b) (.dmorg4 _ _)
  | dmorg3 X Y =>
      have a : .neg (.conj (.neg X) (.neg Y)) ⊢₄
          .disj (.neg (.neg X)) (.neg (.neg Y)) := .dmorg1 _ _
      have b : .disj (.neg (.neg X)) (.neg (.neg Y)) ⊢₄ .disj X Y :=
        deriv_disj_mono (.dneg1 X) (.dneg1 Y)
      exact .cut (.cut a b) (.dneg2 (.disj X Y))
  | dmorg4 X Y =>
      have a : .neg (.neg (.disj X Y)) ⊢₄ .disj X Y := .dneg1 _
      have b : .disj X Y ⊢₄ .disj (.neg (.neg X)) (.neg (.neg Y)) :=
        deriv_disj_mono (.dneg2 X) (.dneg2 Y)
      exact .cut (.cut a b) (.dmorg2 _ _)

/-! ## Completeness of the natural-deduction calculus

Negated atoms are independent generators in FDE.  The construction below
puts every formula into a nonempty disjunction of nonempty conjunctions of
such literals.  Semantic consequence between these normal forms has the
usual finite subset characterization, from which a `Deriv` tree is built.
-/

/-- Mutual derivability, used to keep the normalization proof symmetric. -/
structure DerivEquiv (X Y : Fm α) : Prop where
  forward : X ⊢₄ Y
  backward : Y ⊢₄ X

namespace DerivEquiv

theorem refl (X : Fm α) : DerivEquiv X X := ⟨.ax X, .ax X⟩

theorem trans {X Y Z : Fm α} (hXY : DerivEquiv X Y)
    (hYZ : DerivEquiv Y Z) : DerivEquiv X Z :=
  ⟨.cut hXY.forward hYZ.forward,
   .cut hYZ.backward hXY.backward⟩

theorem conj {X X' Y Y' : Fm α} (hx : DerivEquiv X X')
    (hy : DerivEquiv Y Y') :
    DerivEquiv (.conj X Y) (.conj X' Y') :=
  ⟨deriv_conj_mono hx.forward hy.forward,
   deriv_conj_mono hx.backward hy.backward⟩

theorem disj {X X' Y Y' : Fm α} (hx : DerivEquiv X X')
    (hy : DerivEquiv Y Y') :
    DerivEquiv (.disj X Y) (.disj X' Y') :=
  ⟨deriv_disj_mono hx.forward hy.forward,
   deriv_disj_mono hx.backward hy.backward⟩

end DerivEquiv

theorem deriv_conj_assoc_forward (A B C : Fm α) :
    .conj (.conj A B) C ⊢₄ .conj A (.conj B C) := by
  apply Deriv.conjI
  · exact .cut (.conjE1 (.conj A B) C) (.conjE1 A B)
  · exact .conjI
      (.cut (.conjE1 (.conj A B) C) (.conjE2 A B))
      (.conjE2 (.conj A B) C)

theorem deriv_conj_assoc_backward (A B C : Fm α) :
    .conj A (.conj B C) ⊢₄ .conj (.conj A B) C := by
  apply Deriv.conjI
  · exact .conjI (.conjE1 A (.conj B C))
      (.cut (.conjE2 A (.conj B C)) (.conjE1 B C))
  · exact .cut (.conjE2 A (.conj B C)) (.conjE2 B C)

theorem deriv_disj_assoc_forward (A B C : Fm α) :
    .disj (.disj A B) C ⊢₄ .disj A (.disj B C) := by
  apply Deriv.disjE
  · apply Deriv.disjE
    · exact .disjI1 A (.disj B C)
    · exact .cut (.disjI1 B C) (.disjI2 A (.disj B C))
  · exact .cut (.disjI2 B C) (.disjI2 A (.disj B C))

theorem deriv_disj_assoc_backward (A B C : Fm α) :
    .disj A (.disj B C) ⊢₄ .disj (.disj A B) C := by
  apply Deriv.disjE
  · exact .cut (.disjI1 A B) (.disjI1 (.disj A B) C)
  · apply Deriv.disjE
    · exact .cut (.disjI2 A B) (.disjI1 (.disj A B) C)
    · exact .disjI2 (.disj A B) C

theorem deriv_dist_left_forward (A B C : Fm α) :
    .conj (.disj A B) C ⊢₄ .disj (.conj A C) (.conj B C) := by
  exact .cut (deriv_conj_comm _ _)
    (.cut (.dist C A B)
      (deriv_disj_mono (deriv_conj_comm C A) (deriv_conj_comm C B)))

theorem deriv_dist_left_backward (A B C : Fm α) :
    .disj (.conj A C) (.conj B C) ⊢₄ .conj (.disj A B) C := by
  exact .cut
    (deriv_disj_mono (deriv_conj_comm A C) (deriv_conj_comm B C))
    (.cut (deriv_dist_back C A B) (deriv_conj_comm C (.disj A B)))

/-- A small nonempty list, avoiding artificial truth and falsity constants
in normal forms. -/
inductive NList (β : Type u) where
  | one (head : β)
  | cons (head : β) (tail : NList β)
  deriving Repr

namespace NList

def append : NList β → NList β → NList β
  | .one x, ys => .cons x ys
  | .cons x xs, ys => .cons x (append xs ys)

def map (f : β → γ) : NList β → NList γ
  | .one x => .one (f x)
  | .cons x xs => .cons (f x) (map f xs)

def Mem (x : β) : NList β → Prop
  | .one y => x = y
  | .cons y ys => x = y ∨ Mem x ys

theorem mem_head (x : β) (xs : NList β) : Mem x (.cons x xs) :=
  Or.inl rfl

theorem mem_tail {x y : β} {ys : NList β} (h : Mem x ys) :
    Mem x (.cons y ys) := Or.inr h

end NList

/-- Signed atoms are the generators of FDE's truth component. -/
inductive DLiteral (α : Type u) where
  | pos (atom : α)
  | neg (atom : α)
  deriving Repr

abbrev Term (α : Type u) := NList (DLiteral α)
abbrev DNF (α : Type u) := NList (Term α)

def DNF.product : DNF α → DNF α → DNF α
  | .one s, ys => NList.map (NList.append s) ys
  | .cons s ss, ys =>
      NList.append (NList.map (NList.append s) ys) (product ss ys)

def literalFm : DLiteral α → Fm α
  | .pos a => .atom a
  | .neg a => .neg (.atom a)

def termFm : Term α → Fm α
  | .one l => literalFm l
  | .cons l ls => .conj (literalFm l) (termFm ls)

def dnfFm : DNF α → Fm α
  | .one t => termFm t
  | .cons t ts => .disj (termFm t) (dnfFm ts)

theorem termFm_append_equiv (s t : Term α) :
    DerivEquiv (termFm (NList.append s t)) (.conj (termFm s) (termFm t)) := by
  induction s with
  | one l => exact DerivEquiv.refl _
  | cons l ls ih =>
      apply DerivEquiv.trans (DerivEquiv.conj (DerivEquiv.refl _) ih)
      exact ⟨deriv_conj_assoc_backward _ _ _, deriv_conj_assoc_forward _ _ _⟩

theorem dnfFm_append_equiv (xs ys : DNF α) :
    DerivEquiv (dnfFm (NList.append xs ys))
      (.disj (dnfFm xs) (dnfFm ys)) := by
  induction xs with
  | one t => exact DerivEquiv.refl _
  | cons t ts ih =>
      apply DerivEquiv.trans (DerivEquiv.disj (DerivEquiv.refl _) ih)
      exact ⟨deriv_disj_assoc_backward _ _ _, deriv_disj_assoc_forward _ _ _⟩

theorem dnfFm_map_append_equiv (s : Term α) (ys : DNF α) :
    DerivEquiv (dnfFm (NList.map (NList.append s) ys))
      (.conj (termFm s) (dnfFm ys)) := by
  induction ys with
  | one t => exact termFm_append_equiv s t
  | cons t ts ih =>
      have pieces := DerivEquiv.disj (termFm_append_equiv s t) ih
      exact DerivEquiv.trans pieces
        ⟨deriv_dist_back _ _ _, Deriv.dist _ _ _⟩

theorem dnfFm_product_equiv (xs ys : DNF α) :
    DerivEquiv (dnfFm (DNF.product xs ys))
      (.conj (dnfFm xs) (dnfFm ys)) := by
  induction xs with
  | one s => exact dnfFm_map_append_equiv s ys
  | cons s ss ih =>
      have split := dnfFm_append_equiv
        (NList.map (NList.append s) ys) (DNF.product ss ys)
      have pieces := DerivEquiv.disj (dnfFm_map_append_equiv s ys) ih
      exact DerivEquiv.trans (DerivEquiv.trans split pieces)
        ⟨deriv_dist_left_backward _ _ _, deriv_dist_left_forward _ _ _⟩

/-- `polarity = true` normalizes a formula; `false` normalizes its negation. -/
def normal : Bool → Fm α → DNF α
  | true, .atom a => .one (.one (.pos a))
  | false, .atom a => .one (.one (.neg a))
  | polarity, .neg A => normal (!polarity) A
  | true, .conj A C => DNF.product (normal true A) (normal true C)
  | false, .conj A C => NList.append (normal false A) (normal false C)
  | true, .disj A C => NList.append (normal true A) (normal true C)
  | false, .disj A C => DNF.product (normal false A) (normal false C)

theorem normal_equiv (A : Fm α) :
    DerivEquiv A (dnfFm (normal true A)) ∧
      DerivEquiv (.neg A) (dnfFm (normal false A)) := by
  induction A with
  | atom a => exact ⟨DerivEquiv.refl _, DerivEquiv.refl _⟩
  | neg A ih =>
      constructor
      · exact ih.2
      · exact DerivEquiv.trans
          ⟨Deriv.dneg1 A, Deriv.dneg2 A⟩ ih.1
  | conj A C ihA ihC =>
      constructor
      · exact DerivEquiv.trans (DerivEquiv.conj ihA.1 ihC.1)
          ⟨(dnfFm_product_equiv _ _).backward,
           (dnfFm_product_equiv _ _).forward⟩
      · have hdm : DerivEquiv (.neg (.conj A C))
            (.disj (.neg A) (.neg C)) := ⟨Deriv.dmorg1 A C, Deriv.dmorg2 A C⟩
        have hparts := DerivEquiv.disj ihA.2 ihC.2
        exact DerivEquiv.trans (DerivEquiv.trans hdm hparts)
          ⟨(dnfFm_append_equiv _ _).backward,
           (dnfFm_append_equiv _ _).forward⟩
  | disj A C ihA ihC =>
      constructor
      · exact DerivEquiv.trans (DerivEquiv.disj ihA.1 ihC.1)
          ⟨(dnfFm_append_equiv _ _).backward,
           (dnfFm_append_equiv _ _).forward⟩
      · have hdm : DerivEquiv (.neg (.disj A C))
            (.conj (.neg A) (.neg C)) := ⟨Deriv.dmorg3 A C, Deriv.dmorg4 A C⟩
        have hparts := DerivEquiv.conj ihA.2 ihC.2
        exact DerivEquiv.trans (DerivEquiv.trans hdm hparts)
          ⟨(dnfFm_product_equiv _ _).backward,
           (dnfFm_product_equiv _ _).forward⟩

def literalHolds (v : α → TV4) : DLiteral α → Prop
  | .pos a => tr (v a) = true
  | .neg a => fa (v a) = true

theorem literalFm_true_iff (v : α → TV4) (l : DLiteral α) :
    tr (eval4 v (literalFm l)) = true ↔ literalHolds v l := by
  cases l <;> simp [literalFm, literalHolds, eval4]

theorem termFm_true_iff (v : α → TV4) (t : Term α) :
    tr (eval4 v (termFm t)) = true ↔
      ∀ l, NList.Mem l t → literalHolds v l := by
  induction t with
  | one head =>
      rw [termFm, literalFm_true_iff]
      constructor
      · intro hh l hl
        change l = head at hl
        cases hl
        exact hh
      · intro hall
        exact hall head rfl
  | cons head tail ih =>
      change tr (conj4 (eval4 v (literalFm head))
        (eval4 v (termFm tail))) = true ↔ _
      rw [tr_conj4, Bool.and_eq_true_iff, literalFm_true_iff, ih]
      constructor
      · rintro ⟨hhead, htail⟩ l hl
        cases hl with
        | inl heq => cases heq; exact hhead
        | inr hmem => exact htail l hmem
      · intro hall
        exact ⟨hall head (Or.inl rfl),
          fun l hl => hall l (Or.inr hl)⟩

theorem dnfFm_true_iff (v : α → TV4) (D : DNF α) :
    tr (eval4 v (dnfFm D)) = true ↔
      ∃ t, NList.Mem t D ∧
        ∀ l, NList.Mem l t → literalHolds v l := by
  induction D with
  | one head =>
      rw [dnfFm, termFm_true_iff]
      constructor
      · intro hall
        exact ⟨head, rfl, hall⟩
      · rintro ⟨t, ht, hall⟩
        change t = head at ht
        cases ht
        exact hall
  | cons head tail ih =>
      change tr (disj4 (eval4 v (termFm head))
        (eval4 v (dnfFm tail))) = true ↔ _
      rw [tr_disj4, Bool.or_eq_true_iff, termFm_true_iff, ih]
      constructor
      · intro h
        cases h with
        | inl hhead => exact ⟨head, Or.inl rfl, hhead⟩
        | inr htail =>
            obtain ⟨t, ht, hall⟩ := htail
            exact ⟨t, Or.inr ht, hall⟩
      · rintro ⟨t, ht, hall⟩
        cases ht with
        | inl heq => cases heq; exact Or.inl hall
        | inr ht => exact Or.inr ⟨t, ht, hall⟩

/-- The canonical valuation of one antecedent term.  Its independent truth
and falsity bits record exactly the positive and negative literals present
in that term. -/
noncomputable def canonicalVal (t : Term α) : α → TV4 :=
  fun a => BuddhistComparativeLogic.mk
    (propBool (NList.Mem (.pos a) t))
    (propBool (NList.Mem (.neg a) t))

theorem canonical_literal_iff (t : Term α) (l : DLiteral α) :
    literalHolds (canonicalVal t) l ↔ NList.Mem l t := by
  classical
  cases l <;>
    simp [literalHolds, canonicalVal, propBool_eq_true]

theorem termFm_elim_literal {l : DLiteral α} {t : Term α}
    (h : NList.Mem l t) : termFm t ⊢₄ literalFm l := by
  induction t with
  | one head =>
      change l = head at h
      cases h
      exact .ax _
  | cons head tail ih =>
      cases h with
      | inl heq =>
          cases heq
          exact .conjE1 _ _
      | inr hmem => exact .cut (.conjE2 _ _) (ih hmem)

theorem termFm_subset_deriv (source target : Term α)
    (hsub : ∀ l, NList.Mem l target → NList.Mem l source) :
    termFm source ⊢₄ termFm target := by
  induction target with
  | one head => exact termFm_elim_literal (hsub head rfl)
  | cons head tail ih =>
      exact .conjI
        (termFm_elim_literal (hsub head (Or.inl rfl)))
        (ih (fun l hl => hsub l (Or.inr hl)))

theorem dnfFm_intro_term (t : Term α) (D : DNF α)
    (h : NList.Mem t D) : termFm t ⊢₄ dnfFm D := by
  induction D with
  | one head =>
      change t = head at h
      cases h
      exact .ax _
  | cons head tail ih =>
      cases h with
      | inl heq =>
          cases heq
          exact .disjI1 _ _
      | inr hmem => exact .cut (ih hmem) (.disjI2 _ _)

theorem dnfFm_elim (D : DNF α) (Y : Fm α)
    (h : ∀ t, NList.Mem t D → termFm t ⊢₄ Y) :
    dnfFm D ⊢₄ Y := by
  induction D with
  | one head => exact h head rfl
  | cons head tail ih =>
      exact .disjE (h head (Or.inl rfl))
        (ih (fun t ht => h t (Or.inr ht)))

/-- Semantic consequence between two DNFs forces the standard term-subset
condition.  The canonical valuation makes this implication constructive at
the level of the finite truth bits. -/
theorem entails_dnf_term_subset {DX DY : DNF α}
    (h : entails4 (dnfFm DX) (dnfFm DY)) :
    ∀ source, NList.Mem source DX →
      ∃ target, NList.Mem target DY ∧
        ∀ l, NList.Mem l target → NList.Mem l source := by
  intro source hsource
  let v := canonicalVal source
  have hx : tr (eval4 v (dnfFm DX)) = true :=
    (dnfFm_true_iff v DX).2
      ⟨source, hsource, fun l _hl => (canonical_literal_iff source l).2 _hl⟩
  have hySat := h v (by simpa [sat4] using hx)
  have hy : tr (eval4 v (dnfFm DY)) = true := by
    simpa [sat4] using hySat
  obtain ⟨target, htarget, hall⟩ := (dnfFm_true_iff v DY).1 hy
  exact ⟨target, htarget,
    fun l hl => (canonical_literal_iff source l).1 (hall l hl)⟩

theorem dnf_deriv_of_entails {DX DY : DNF α}
    (h : entails4 (dnfFm DX) (dnfFm DY)) :
    dnfFm DX ⊢₄ dnfFm DY := by
  apply dnfFm_elim DX (dnfFm DY)
  intro source hsource
  obtain ⟨target, htarget, hsub⟩ := entails_dnf_term_subset h source hsource
  exact .cut (termFm_subset_deriv source target hsub)
    (dnfFm_intro_term target DY htarget)

/-- Completeness of the natural-deduction rules for single-premise FDE
consequence. -/
theorem deriv_complete {X Y : Fm α} (h : entails4 X Y) : X ⊢₄ Y := by
  have nx := (normal_equiv X).1
  have ny := (normal_equiv Y).1
  have hnormal : entails4 (dnfFm (normal true X))
      (dnfFm (normal true Y)) := by
    intro v hx
    have hx' := deriv_sound nx.backward v hx
    have hy := h v hx'
    exact deriv_sound ny.forward v hy
  exact .cut nx.forward (.cut (dnf_deriv_of_entails hnormal) ny.backward)

theorem deriv_sound_complete (X Y : Fm α) :
    (X ⊢₄ Y) ↔ entails4 X Y :=
  ⟨deriv_sound, deriv_complete⟩

/-- FDE5 natural derivations use exactly the atom-containment side condition
identified by the semantic characterization. -/
structure Deriv5 (X Y : Fm α) : Prop where
  containment : psubset (atoms Y) (atoms X)
  derivation : X ⊢₄ Y

theorem deriv5_sound {X Y : Fm α} (h : Deriv5 X Y) : entails5 X Y :=
  fde5_is_fde_plus_containment.mpr ⟨h.containment, deriv_sound h.derivation⟩

theorem deriv5_complete {X Y : Fm α} (h : entails5 X Y) : Deriv5 X Y := by
  obtain ⟨containment, fde⟩ := fde5_is_fde_plus_containment.mp h
  exact ⟨containment, deriv_complete fde⟩

theorem deriv5_sound_complete (X Y : Fm α) :
    Deriv5 X Y ↔ entails5 X Y :=
  ⟨deriv5_sound, deriv5_complete⟩

theorem fde5_does_not_contrapose :
    entails5 (.conj (.atom true) (.atom false)) (.atom true) ∧
      ¬ entails5 (.neg (.atom true))
        (.neg (.conj (.atom true) (.atom false))) := by
  constructor
  · exact fde5_is_fde_plus_containment.mpr
      ⟨by
        intro a ha
        change a = true at ha
        change a = true ∨ a = false
        exact Or.inl ha
      , fun v h => by
        change tr (conj4 (eval4 v (.atom true))
          (eval4 v (.atom false))) = true at h
        rw [tr_conj4, Bool.and_eq_true_iff] at h
        exact h.1⟩
  · intro h
    have containment := (fde5_is_fde_plus_containment.mp h).1
    have bad := containment false (by
      change false = true ∨ false = false
      exact Or.inr rfl)
    change false = true at bad
    exact Bool.noConfusion bad

/-! ## Analytic signed tableaux -/

def counterBranches (X Y : Fm α) : List (List (SLit α)) :=
  meetBranches (expand true .tr X) (expand false .tr Y)

/-- A proof object names an explicit complementary pair on a branch. -/
inductive BranchClosed (branch : List (SLit α)) : Prop
  | clash (literal : SLit α) : literal ∈ branch → negLit literal ∈ branch →
      BranchClosed branch

def Tableau (X Y : Fm α) : Prop :=
  ∀ branch, branch ∈ counterBranches X Y → BranchClosed branch

theorem branch_closed_iff [DecidableEq α] {branch : List (SLit α)} :
    BranchClosed branch ↔ closedLits branch = true := by
  constructor
  · rintro ⟨literal, hl, hnl⟩
    exact closedLits_iff.mpr ⟨literal, hl, hnl⟩
  · intro h
    obtain ⟨literal, hl, hnl⟩ := closedLits_iff.mp h
    exact .clash literal hl hnl

theorem tableau_iff_decision [DecidableEq α] (X Y : Fm α) :
    Tableau X Y ↔ fdeDec X Y = true := by
  rw [fdeDec, List.all_eq_true]
  exact forall_congr' fun branch =>
    forall_congr' fun _ => branch_closed_iff

theorem tableau_sound [DecidableEq α] {X Y : Fm α}
    (proof : Tableau X Y) : entails4 X Y :=
  (fde_dec_correct X Y).mpr ((tableau_iff_decision X Y).mp proof)

theorem tableau_complete [DecidableEq α] {X Y : Fm α}
    (valid : entails4 X Y) : Tableau X Y :=
  (tableau_iff_decision X Y).mpr ((fde_dec_correct X Y).mp valid)

theorem tableau_sound_complete [DecidableEq α] (X Y : Fm α) :
    Tableau X Y ↔ entails4 X Y :=
  ⟨tableau_sound, tableau_complete⟩

theorem tableau_to_deriv [DecidableEq α] {X Y : Fm α}
    (h : Tableau X Y) : X ⊢₄ Y :=
  deriv_complete (tableau_sound h)

theorem deriv_to_tableau [DecidableEq α] {X Y : Fm α}
    (h : X ⊢₄ Y) : Tableau X Y :=
  tableau_complete (deriv_sound h)

theorem tableau_iff_deriv [DecidableEq α] (X Y : Fm α) :
    Tableau X Y ↔ X ⊢₄ Y :=
  ⟨tableau_to_deriv, deriv_to_tableau⟩

/-- Decidable proof search returns either a complete tableau certificate or
a semantic countervaluation. -/
theorem proof_or_countermodel [DecidableEq α] (X Y : Fm α) :
    Tableau X Y ∨ ∃ v : α → TV4,
      sat4 v X = true ∧ sat4 v Y = false := by
  by_cases h : entails4 X Y
  · exact Or.inl (tableau_complete h)
  · right
    apply Classical.byContradiction
    intro noCounter
    apply h
    intro v hx
    by_cases hy : sat4 v Y = true
    · exact hy
    · have hyf : sat4 v Y = false := Bool.eq_false_iff.mpr hy
      exact False.elim (noCounter ⟨v, hx, hyf⟩)

/-! ## FDE5: proof plus relevance containment -/

structure Tableau5 (X Y : Fm α) : Prop where
  containment : psubset (atoms Y) (atoms X)
  fde : Tableau X Y

theorem tableau5_sound [DecidableEq α] {X Y : Fm α}
    (proof : Tableau5 X Y) : entails5 X Y :=
  fde5_is_fde_plus_containment.mpr
    ⟨proof.containment, tableau_sound proof.fde⟩

theorem tableau5_complete [DecidableEq α] {X Y : Fm α}
    (valid : entails5 X Y) : Tableau5 X Y := by
  obtain ⟨containment, fde⟩ := fde5_is_fde_plus_containment.mp valid
  exact ⟨containment, tableau_complete fde⟩

theorem tableau5_sound_complete [DecidableEq α] (X Y : Fm α) :
    Tableau5 X Y ↔ entails5 X Y :=
  ⟨tableau5_sound, tableau5_complete⟩

theorem tableau5_iff_deriv5 [DecidableEq α] (X Y : Fm α) :
    Tableau5 X Y ↔ Deriv5 X Y :=
  ⟨fun h => deriv5_complete (tableau5_sound h),
   fun h => tableau5_complete (deriv5_sound h)⟩

/-! Small proof objects demonstrate that the calculus is inhabited. -/

theorem atomReflexiveTableau [DecidableEq α] (a : α) :
    Tableau (.atom a) (.atom a) := by
  intro branch hb
  simp [counterBranches, expand, meetBranches] at hb
  subst branch
  exact .clash (.mk true .tr a) (by simp) (by simp [negLit])

theorem analytic_calculus_nonvacuous [DecidableEq α] (a : α) :
    Tableau (.atom a) (.atom a) := atomReflexiveTableau a

end BuddhistComparativeLogic.FDECalculus
