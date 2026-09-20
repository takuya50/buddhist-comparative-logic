/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation

/-!
# MMK 1:1: fourfold non-arising

Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_MMK1.thy`.  The four refutations yield
formula-level non-arising in classical and FDE semantics.  FDE still admits a
valuation on which arising itself is designated, and it does not in general
validate the modus-tollens step used by each reductio.
-/

namespace BuddhistComparativeLogic

inductive Origin where
  | self | other | both | neither
  deriving DecidableEq, Repr

inductive UtpadaAtom where
  | fromOrigin : Origin → UtpadaAtom
  deriving DecidableEq, Repr

open Origin UtpadaAtom Fm

def arises : Fm UtpadaAtom :=
  disj (disj (atom (fromOrigin self)) (atom (fromOrigin other)))
       (disj (atom (fromOrigin both)) (atom (fromOrigin neither)))

def refuted2 (v : UtpadaAtom → Bool) : Prop :=
  ∀ og, eval2 v (neg (atom (fromOrigin og))) = true

def refuted4 (v : UtpadaAtom → TV4) : Prop :=
  ∀ og, sat4 v (neg (atom (fromOrigin og))) = true

theorem catuh_utpada_cl (v : UtpadaAtom → Bool) (h : refuted2 v) :
    eval2 v (neg arises) = true := by
  have hself := h self
  have hother := h other
  have hboth := h both
  have hneither := h neither
  simp [eval2] at hself hother hboth hneither ⊢
  cases hs : v (fromOrigin self) <;>
    cases ho : v (fromOrigin other) <;>
    cases hb : v (fromOrigin both) <;>
    cases hn : v (fromOrigin neither) <;>
    simp_all [arises, eval2]

theorem anutpada_fde_formula (v : UtpadaAtom → TV4) (h : refuted4 v) :
    sat4 v (neg arises) = true := by
  have hself := h self
  have hother := h other
  have hboth := h both
  have hneither := h neither
  cases hs : v (fromOrigin self) <;>
    cases ho : v (fromOrigin other) <;>
    cases hb : v (fromOrigin both) <;>
    cases hn : v (fromOrigin neither) <;>
    simp_all [refuted4, sat4, eval4, arises, neg4, disj4, mk, tr, fa]

def allGlutUtpada : UtpadaAtom → TV4 := fun _ => .B

theorem anutpada_fde_designation_fails :
    refuted4 allGlutUtpada ∧ sat4 allGlutUtpada arises = true := by
  constructor
  · intro og
    rfl
  · rfl

/-- Classical modus tollens, with material implication `¬p ∨ q`. -/
theorem cl_mt :
    entails2
      (conj (disj (neg (atom Atom.p)) (atom Atom.q)) (neg (atom Atom.q)))
      (neg (atom Atom.p)) := by
  rw [entails2_iff]
  decide

/-- The matching FDE inference has a finite countermodel. -/
theorem fde_mt_fails :
    ¬ entails4
      (conj (disj (neg (atom Atom.p)) (atom Atom.q)) (neg (atom Atom.q)))
      (neg (atom Atom.p)) := by
  rw [entails4_iff]
  decide

def mtCountermodel : Atom → TV4
  | .p => .T
  | .q => .B
  | .r => .F

theorem fde_mt_countermodel :
    sat4 mtCountermodel
      (conj (disj (neg (atom Atom.p)) (atom Atom.q)) (neg (atom Atom.q))) = true ∧
    sat4 mtCountermodel (neg (atom Atom.p)) = false := by decide

end BuddhistComparativeLogic
