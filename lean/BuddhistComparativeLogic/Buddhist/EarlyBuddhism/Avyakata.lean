/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.UniversalDesignation

/-!
# The fourteen unanswered questions

Lean counterpart of the formula- and designation-level results in
`isabelle/Buddhist/EarlyBuddhism/Avyakata.thy`.  Negating all four corners is a glut at formula level;
leaving every corner undesignated is a gap (or the fifth, ineffable value).
-/

namespace BuddhistComparativeLogic

inductive AvyakataTopic where
  | worldEternal | worldFinite | tathagataAfterDeath | soulBody
  deriving DecidableEq, Repr

structure AvyakataQuestion where
  topic : AvyakataTopic
  corner : Koti
  deriving DecidableEq, Repr

open AvyakataTopic Koti Fm

def avyakataQuestions : List AvyakataQuestion :=
  [⟨worldEternal, K1⟩, ⟨worldEternal, K2⟩, ⟨worldEternal, K3⟩, ⟨worldEternal, K4⟩,
   ⟨worldFinite, K1⟩, ⟨worldFinite, K2⟩, ⟨worldFinite, K3⟩, ⟨worldFinite, K4⟩,
   ⟨tathagataAfterDeath, K1⟩, ⟨tathagataAfterDeath, K2⟩,
   ⟨tathagataAfterDeath, K3⟩, ⟨tathagataAfterDeath, K4⟩,
   ⟨soulBody, K1⟩, ⟨soulBody, K2⟩]

theorem fourteen : avyakataQuestions.length = 14 ∧ avyakataQuestions.Nodup := by decide

def cornerFormula (a : α) : Koti → Fm α
  | .K1 => atom a
  | .K2 => neg (atom a)
  | .K3 => conj (atom a) (neg (atom a))
  | .K4 => conj (neg (atom a)) (neg (neg (atom a)))

def rejection (a : α) : Fm α :=
  conj (conj (neg (cornerFormula a .K1)) (neg (cornerFormula a .K2)))
       (conj (neg (cornerFormula a .K3)) (neg (cornerFormula a .K4)))

theorem rejection_formula_cl (v : α → Bool) (a : α) :
    eval2 v (rejection a) = false := by
  cases h : v a <;>
    simp [rejection, cornerFormula, eval2, h]

theorem rejection_formula_fde (v : α → TV4) (a : α) :
    sat4 v (rejection a) = true ↔ v a = .B := by
  cases h : v a <;>
    simp [rejection, cornerFormula, sat4, eval4, h, neg4, conj4,
      BuddhistComparativeLogic.mk, tr, fa]

def sat5 (v : α → TV5) (A : Fm α) : Bool := des5 (eval5 v A)

theorem rejection_formula_fde5 (v : α → TV5) (a : α) :
    sat5 v (rejection a) = true ↔ v a = .fin .B := by
  cases h : v a with
  | E => simp [sat5, rejection, cornerFormula, eval5, h, des5, neg5, conj5]
  | fin x =>
      cases x <;>
        simp [sat5, rejection, cornerFormula, eval5, h, des5, neg5, conj5,
          neg4, conj4, BuddhistComparativeLogic.mk, tr, fa]

def cornerValue4 (x : TV4) : Koti → TV4
  | .K1 => x
  | .K2 => neg4 x
  | .K3 => conj4 x (neg4 x)
  | .K4 => conj4 (neg4 x) (neg4 (neg4 x))

def cornerValue5 (x : TV5) : Koti → TV5
  | .K1 => x
  | .K2 => neg5 x
  | .K3 => conj5 x (neg5 x)
  | .K4 => conj5 (neg5 x) (neg5 (neg5 x))

theorem corner_semantics4 (v : α → TV4) (a : α) (k : Koti) :
    sat4 v (cornerFormula a k) = tr (cornerValue4 (v a) k) := by
  cases k <;> rfl

theorem corner_semantics5 (v : α → TV5) (a : α) (k : Koti) :
    sat5 v (cornerFormula a k) = des5 (cornerValue5 (v a) k) := by
  cases k <;> rfl

def rejectsAll4 (v : α → TV4) (a : α) : Prop :=
  ∀ k, tr (cornerValue4 (v a) k) = false

def rejectsAll5 (v : α → TV5) (a : α) : Prop :=
  ∀ k, des5 (cornerValue5 (v a) k) = false

theorem rejection_designation_fde (v : α → TV4) (a : α) :
    rejectsAll4 v a ↔ v a = .N := by
  cases hv : v a with
  | T =>
      constructor
      · intro hall
        unfold rejectsAll4 at hall
        have hk := hall K1
        simp [hv, cornerValue4, tr] at hk
      · intro h; cases h
  | B =>
      constructor
      · intro hall
        unfold rejectsAll4 at hall
        have hk := hall K1
        simp [hv, cornerValue4, tr] at hk
      · intro h; cases h
  | N =>
      constructor
      · intro _; rfl
      · intro _
        unfold rejectsAll4
        intro k
        cases k <;> simp [hv, cornerValue4, neg4, conj4, BuddhistComparativeLogic.mk, tr, fa]
  | F =>
      constructor
      · intro hall
        unfold rejectsAll4 at hall
        have hk := hall K2
        simp [hv, cornerValue4, neg4, BuddhistComparativeLogic.mk, tr, fa] at hk
      · intro h; cases h

theorem rejection_designation_fde5 (v : α → TV5) (a : α) :
    rejectsAll5 v a ↔ v a = .fin .N ∨ v a = .E := by
  cases hv : v a with
  | E =>
      constructor
      · intro _; exact Or.inr rfl
      · intro _
        unfold rejectsAll5
        intro k
        cases k <;> simp [hv, cornerValue5, des5, neg5, conj5]
  | fin x =>
      cases x
      · constructor
        · intro hall
          unfold rejectsAll5 at hall
          have hk := hall K1
          simp [hv, cornerValue5, des5, tr] at hk
        · intro h; rcases h with h | h <;> cases h
      · constructor
        · intro hall
          unfold rejectsAll5 at hall
          have hk := hall K1
          simp [hv, cornerValue5, des5, tr] at hk
        · intro h; rcases h with h | h <;> cases h
      · constructor
        · intro _; exact Or.inl rfl
        · intro _
          unfold rejectsAll5
          intro k
          cases k <;>
            simp [hv, cornerValue5, des5, neg5, conj5, neg4, conj4,
              BuddhistComparativeLogic.mk, tr, fa]
      · constructor
        · intro hall
          unfold rejectsAll5 at hall
          have hk := hall K2
          simp [hv, cornerValue5, neg5, des5, neg4, BuddhistComparativeLogic.mk, tr, fa] at hk
        · intro h; rcases h with h | h <;> cases h

theorem rejection_is_K4_fde (v : α → TV4) (a : α) :
    rejectsAll4 v a ↔ kotiOf des4 neg4 (v a) = .K4 := by
  rw [rejection_designation_fde]
  cases h : v a <;> decide

theorem rejection_is_K4_fde5 (v : α → TV5) (a : α) :
    rejectsAll5 v a ↔ kotiOf des5 neg5 (v a) = .K4 := by
  rw [rejection_designation_fde5]
  cases h : v a with
  | E => decide
  | fin x => cases x <;> decide

theorem silence_gap_or_ineffable :
    kotiOf des5 neg5 (.fin .N) = .K4 ∧ kotiOf des5 neg5 .E = .K4 := by decide

/-! ## A valueless question under universal and existential designation -/

theorem silence_is_assent_under_universal_designation
    (Vn : α → PSet Bool) (a : α) (h : Vn a = pempty) :
    upsat mvClassical Vn (atom a) ∧
    upsat mvClassical Vn (neg (atom a)) ∧
    pkoti_of mvClassical (Vn a) = .K4 ∧
    upsat mvClassical Vn (cornerFormula a .K3) := by
  classical
  simp [upsat, peval, psubset, pimage, pimage₂, pempty, h,
    cornerFormula, pkoti_empty]

theorem silence_is_gap_under_existential_designation
    (Vn : α → PSet Bool) (a : α) (h : Vn a = pempty) :
    ¬ psat mvClassical Vn (atom a) ∧
    ¬ psat mvClassical Vn (neg (atom a)) ∧
    pkoti_of mvClassical (Vn a) = .K4 := by
  classical
  simp [psat, peval, pintersects, pimage, pempty, h, pkoti_empty]

end BuddhistComparativeLogic
