/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Hetucakra

/-!
# Apoha and revision

Sets are represented extensionally as predicates.  Unlike Isabelle/HOL,
Lean permits empty types, so `apoha_no_fixpoint` explicitly assumes that the
underlying type is inhabited; without it the statement is false.
-/

namespace BuddhistComparativeLogic.Apoha

open BuddhistComparativeLogic.Hetucakra

abbrev PredSet (α : Type u) := α → Prop

def compl (S : PredSet α) : PredSet α := fun x => ¬ S x

theorem compl_compl (S : PredSet α) : compl (compl S) = S := by
  classical
  funext x
  apply propext
  constructor
  · intro h
    exact Classical.byContradiction h
  · intro hx hnot
    exact hnot hx

theorem apoha_no_fixpoint {α : Type u} [Nonempty α] (M : PredSet α) :
    M ≠ compl M := by
  intro h
  let x : α := Classical.choice inferInstance
  have hx := congrFun h x
  classical
  by_cases hm : M x <;> simp [compl, hm] at hx

def apohaPair (M N : PredSet α) : Prop := M = compl N ∧ N = compl M

theorem apoha_pair_underdetermined (S : PredSet α) :
    apohaPair S (compl S) := by
  exact ⟨(compl_compl S).symm, rfl⟩

theorem apoha_pair_no_constraint (M N : PredSet α) :
    apohaPair M N ↔ N = compl M := by
  constructor
  · exact fun h => h.2
  · intro h
    constructor
    · rw [h, compl_compl]
    · exact h

theorem circularity_is_underdetermination {α : Type u} [Nonempty α] :
    (¬ ∃ M : PredSet α, M = compl M) ∧
      (∀ S : PredSet α, ∃ N, apohaPair S N) := by
  constructor
  · rintro ⟨M, hM⟩
    exact apoha_no_fixpoint M hM
  · intro S
    exact ⟨compl S, apoha_pair_underdetermined S⟩

/-! ## Revision theory -/

def revSeq (S : PredSet α) : Nat → PredSet α
  | 0 => S
  | n + 1 => compl (revSeq S n)

theorem revision_oscillates (S : PredSet α) (n : Nat) :
    revSeq S (n + 2) = revSeq S n := by
  simp [revSeq, compl_compl]

theorem revision_never_stabilises {α : Type u} [Nonempty α]
    (S : PredSet α) (n : Nat) :
    revSeq S (n + 1) ≠ revSeq S n := by
  simp only [revSeq]
  intro h
  exact apoha_no_fixpoint (revSeq S n) h.symm

theorem revision_has_no_stable_set {α : Type u} [Nonempty α]
    (S : PredSet α) :
    ¬ ∃ n, revSeq S (n + 1) = revSeq S n := by
  rintro ⟨n, hn⟩
  exact revision_never_stabilises S n hn

/-! ## Equivalence-class grounding

`sameEffect` is only the name of the supplied equivalence-like relation.  This
structure contains no effects, production relation, perception chain, or
other data that would establish a causal interpretation.  Such an
interpretation is an external premise.
-/

structure Grounding (α : Type u) where
  sameEffect : α → α → Prop
  refl : ∀ x, sameEffect x x
  symm : ∀ {x y}, sameEffect x y → sameEffect y x
  trans : ∀ {x y z}, sameEffect x y → sameEffect y z → sameEffect x z

namespace Grounding

variable {α : Type u} (g : Grounding α)

def cls (x : α) : PredSet α := fun y => g.sameEffect x y

def grounded (M : PredSet α) : Prop := ∃ x, M = g.cls x

theorem mem_cls_self (x : α) : g.cls x x := g.refl x

theorem cls_eq {x y : α} (hxy : g.sameEffect x y) : g.cls x = g.cls y := by
  funext z
  apply propext
  constructor
  · intro hxz
    exact g.trans (g.symm hxy) hxz
  · intro hyz
    exact g.trans hxy hyz

/-- Two grounded classes containing one common object are equal.  The theorem
name is retained for compatibility with the Isabelle port; the proof uses
only the explicitly supplied equivalence-like laws above. -/
theorem causal_grounding_unique {M N : PredSet α} {x : α}
    (hM : g.grounded M) (hN : g.grounded N) (xM : M x) (xN : N x) :
    M = N := by
  rcases hM with ⟨a, rfl⟩
  rcases hN with ⟨b, rfl⟩
  exact g.cls_eq (g.trans xM (g.symm xN))

/-- Retain both the supplied grounding and the generic complement-pair fact.
The second conjunct alone holds for every extension and does not derive the
first. -/
theorem grounding_selects_a_solution {M : PredSet α}
    (grounded : g.grounded M) :
    g.grounded M ∧ apohaPair M (compl M) :=
  ⟨grounded, apoha_pair_underdetermined M⟩

end Grounding

def identityEffect (α : Type u) : Grounding α where
  sameEffect := (· = ·)
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans

def parityEffect : Grounding Nat where
  sameEffect := fun m n => m % 2 = n % 2
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans

def close (m n : Nat) : Prop :=
  (m ≤ n ∧ n ≤ m + 1) ∨ (n ≤ m ∧ m ≤ n + 1)

def ccls (x : Nat) : PredSet Nat := fun y => close x y

theorem close_refl (x : Nat) : close x x :=
  Or.inl ⟨Nat.le_refl _, Nat.le_add_right _ _⟩

theorem close_symm {x y : Nat} (h : close x y) : close y x := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem grounding_needs_transitivity :
    (¬ ∀ x y z, close x y → close y z → close x z) ∧
      ccls 0 1 ∧ ccls 1 1 ∧ ccls 0 ≠ ccls 1 := by
  constructor
  · intro h
    have h02 := h 0 1 2 (by simp [close]) (by simp [close])
    exact (by simp [close] : ¬ close 0 2) h02
  · refine ⟨by simp [ccls, close], by simp [ccls, close], ?_⟩
    intro heq
    have h2 := congrFun heq 2
    have hc1 : ccls 1 2 := by simp [ccls, close]
    have hc0 : ccls 0 2 := Eq.mpr h2 hc1
    exact (by simp [ccls, close] : ¬ ccls 0 2) hc0

/-! ## Apoha inside the inference schema -/

theorem vipaksa_is_apoha_of_sapaksa {L : Type u}
    (a : Hetucakra.Anumana L) (x : L) :
    a.vipaksa x ↔ compl a.sapaksa x ∧ x ≠ a.paksa := by
  classical
  constructor
  · intro h
    refine ⟨?_, h.1⟩
    intro hs
    exact h.2 hs.2
  · intro h
    refine ⟨h.2, ?_⟩
    intro hs
    exact h.1 ⟨h.2, hs⟩

theorem sapaksa_vipaksa_partition {L : Type u}
    (a : Hetucakra.Anumana L) (x : L) :
    (a.sapaksa x ∨ a.vipaksa x) ↔ x ≠ a.paksa := by
  classical
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hne
    by_cases hs : a.sadhya x
    · exact Or.inl ⟨hne, hs⟩
    · exact Or.inr ⟨hne, hs⟩

def wheelPositive : Hetucakra.Anumana Nat where
  paksa := 0
  sadhya := fun _ => True
  reason := fun x => x = 2

def wheelNegative : Hetucakra.Anumana Nat where
  paksa := 0
  sadhya := fun _ => False
  reason := fun x => x = 2

theorem apoha_underdetermines_the_wheel :
    wheelPositive.wheelVerdict = .valid ∧
      wheelNegative.wheelVerdict = .contradictory := by
  constructor
  · apply wheelPositive.wheel_valid_iff.mpr
    constructor
    · exact ⟨2, ⟨by decide, trivial⟩, rfl⟩
    · intro x hx _
      exact hx.2 trivial
  · apply wheelNegative.wheel_contradictory_iff.mpr
    constructor
    · intro x hx
      exact False.elim hx.2
    · exact ⟨2, ⟨by decide, id⟩, rfl⟩

end BuddhistComparativeLogic.Apoha
