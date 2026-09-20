/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation
import BuddhistComparativeLogic.Core.Connexive
import BuddhistComparativeLogic.Buddhist.HeartSutra.Emptiness

/-!
# Executable decision procedures for the three-atom fragment

Lean counterpart of `isabelle/Core/FiniteDecisionProcedures.thy`.  The checkers enumerate 8 classical,
64 FDE, and 125 FDE5 valuations.  Their correctness theorems connect finite
Boolean computation back to quantification over all three-atom valuations.
-/

namespace BuddhistComparativeLogic

set_option maxRecDepth 4096

/-- Every valuation of the three-atom language occurs in the product list
when the supplied value list is complete.  This is the direct Lean form of
Isabelle's `all_vals_UNIV`; the existential avoids requiring decidable
equality on the value type. -/
theorem all_vals_UNIV (vs : List β) (hvs : ∀ x : β, x ∈ vs)
    (v : Atom → β) :
    ∃ t ∈ triples vs, valOf t = v := by
  refine ⟨(v .p, v .q, v .r), ?_, valOf_eta v⟩
  simp [triples, hvs]

def tv5Values : List TV5 := [.fin .T, .fin .B, .fin .N, .fin .F, .E]
def all5 : List (Tri TV5) := triples tv5Values

theorem tv5Values_complete (x : TV5) : x ∈ tv5Values := by
  cases x with
  | E => decide
  | fin y => cases y <;> decide

theorem all5_length : all5.length = 125 := by decide

theorem mem_all5 (v : Atom → TV5) : (v .p, v .q, v .r) ∈ all5 := by
  cases hp : v .p with
  | E =>
      cases hq : v .q with
      | E =>
          cases hr : v .r with
          | E => decide
          | fin z => cases z <;> decide
      | fin y =>
          cases y <;>
            cases hr : v .r with
            | E => decide
            | fin z => cases z <;> decide
  | fin x =>
      cases x <;>
        cases hq : v .q with
        | E =>
            cases hr : v .r with
            | E => decide
            | fin z => cases z <;> decide
        | fin y =>
            cases y <;>
              cases hr : v .r with
              | E => decide
              | fin z => cases z <;> decide

def valid2Dec (X : Fm Atom) : Bool :=
  all2.all fun t => eval2 (valOf t) X

def valid4Dec (X : Fm Atom) : Bool :=
  all4.all fun t => sat4 (valOf t) X

def valid5Dec (X : Fm Atom) : Bool :=
  all5.all fun t => des5 (eval5 (valOf t) X)

def entails4ListDec (Γ : List (Fm Atom)) (X : Fm Atom) : Bool :=
  all4.all fun t => (!(Γ.all fun Y => sat4 (valOf t) Y)) || sat4 (valOf t) X

def entails4List (Γ : List (Fm Atom)) (X : Fm Atom) : Prop :=
  ∀ v : Atom → TV4, (∀ Y, Y ∈ Γ → sat4 v Y = true) → sat4 v X = true

def cvalidDec (implication : TV4 → TV4 → TV4) (X : CFm Atom) : Bool :=
  all4.all fun t => CFm.sat implication (valOf t) X

theorem valid2_correct (X : Fm Atom) :
    (∀ v : Atom → Bool, eval2 v X = true) ↔ valid2Dec X = true := by
  constructor
  · intro h
    unfold valid2Dec
    rw [List.all_eq_true]
    intro t _
    exact h (valOf t)
  · intro h v
    unfold valid2Dec at h
    rw [List.all_eq_true] at h
    have hv := h (v .p, v .q, v .r) (mem_all2 v)
    rwa [valOf_eta v] at hv

theorem valid4_correct (X : Fm Atom) :
    (∀ v : Atom → TV4, sat4 v X = true) ↔ valid4Dec X = true := by
  constructor
  · intro h
    unfold valid4Dec
    rw [List.all_eq_true]
    intro t _
    exact h (valOf t)
  · intro h v
    unfold valid4Dec at h
    rw [List.all_eq_true] at h
    have hv := h (v .p, v .q, v .r) (mem_all4 v)
    rwa [valOf_eta v] at hv

theorem valid5_correct (X : Fm Atom) :
    (∀ v : Atom → TV5, des5 (eval5 v X) = true) ↔ valid5Dec X = true := by
  constructor
  · intro h
    unfold valid5Dec
    rw [List.all_eq_true]
    intro t _
    exact h (valOf t)
  · intro h v
    unfold valid5Dec at h
    rw [List.all_eq_true] at h
    have hv := h (v .p, v .q, v .r) (mem_all5 v)
    rwa [valOf_eta v] at hv

theorem cvalid_dec_correct (implication : TV4 → TV4 → TV4) (X : CFm Atom) :
    CFm.valid implication X ↔ cvalidDec implication X = true := by
  constructor
  · intro h
    unfold cvalidDec
    rw [List.all_eq_true]
    intro t _
    exact h (valOf t)
  · intro h v
    unfold cvalidDec at h
    rw [List.all_eq_true] at h
    have hv := h (v .p, v .q, v .r) (mem_all4 v)
    rwa [valOf_eta v] at hv

theorem entails4_correct (Γ : List (Fm Atom)) (X : Fm Atom) :
    entails4List Γ X ↔ entails4ListDec Γ X = true := by
  constructor
  · intro h
    unfold entails4ListDec
    rw [List.all_eq_true]
    intro t _
    cases hp : Γ.all (fun Y => sat4 (valOf t) Y)
    · simp
    · have hp' : ∀ Y, Y ∈ Γ → sat4 (valOf t) Y = true :=
        (List.all_eq_true.mp hp)
      have hx := h (valOf t) hp'
      simp [hx]
  · intro h
    unfold entails4ListDec at h
    rw [List.all_eq_true] at h
    intro v hp
    have hv := h (v .p, v .q, v .r) (mem_all4 v)
    rw [valOf_eta v] at hv
    have hall : Γ.all (fun Y => sat4 v Y) = true :=
      List.all_eq_true.mpr hp
    simpa [hall] using hv

theorem valid2_lem : valid2Dec (.disj (.atom .p) (.neg (.atom .p))) = true := by decide
theorem valid4_lem_fails : valid4Dec (.disj (.atom .p) (.neg (.atom .p))) = false := by decide
theorem valid5_lem_fails : valid5Dec (.disj (.atom .p) (.neg (.atom .p))) = false := by decide

theorem decide_fde_mp_fails :
    entails4ListDec [.atom .p, .disj (.neg (.atom .p)) (.atom .q)] (.atom .q) = false := by
  decide

theorem decide_fde_explosion_fails :
    entails4ListDec [.atom .p, .neg (.atom .p)] (.atom .q) = false := by decide

theorem decide_aristotle_connexive :
    cvalidDec CFm.cimp4 (.neg (.imp (.atom .p) (.neg (.atom .p)))) = true := by decide

theorem decide_aristotle_material_fails :
    cvalidDec CFm.mimp4 (.neg (.imp (.atom .p) (.neg (.atom .p)))) = false := by decide

theorem decide_boethius_connexive :
    cvalidDec CFm.cimp4
      (.imp (.imp (.atom .p) (.atom .q))
        (.neg (.imp (.atom .p) (.neg (.atom .q))))) = true := by decide

theorem decide_hs10_glut :
    all4.all (fun t =>
      sat4 (valOf t) (hs10Formula .p) == (valOf t .p == .B)) = true := by
  decide

end BuddhistComparativeLogic
