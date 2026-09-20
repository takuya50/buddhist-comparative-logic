/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation
import BuddhistComparativeLogic.Core.MVLogic

/-!
# Worked example: adding strong Kleene K3

Lean counterpart of `isabelle/Core/ManyValuedLogicExample.thy`.  This has no doctrinal content; it
demonstrates the reusable many-valued interface and isolates the glut that
separates K3 from FDE.
-/

namespace BuddhistComparativeLogic

inductive K3 where | t | u | f deriving DecidableEq, Repr

namespace K3

def neg : K3 → K3
  | .t => .f | .u => .u | .f => .t

def conj : K3 → K3 → K3
  | .f, _ => .f | _, .f => .f
  | .u, _ => .u | _, .u => .u
  | .t, .t => .t

def disj : K3 → K3 → K3
  | .t, _ => .t | _, .t => .t
  | .u, _ => .u | _, .u => .u
  | .f, .f => .f

def logic : MVLogic K3 where
  designated x := x = .t
  neg := neg
  mconj := conj
  mdisj := disj
  designated_nonempty := ⟨.t, rfl⟩
  designated_proper := ⟨.u, by decide⟩

def gapP : Atom → K3
  | .p => .u
  | _ => .f

theorem lem_fails : ¬ logic.valid (.disj (.atom Atom.p) (.neg (.atom Atom.p))) := by
  intro h
  have hv := (MVLogic.valid_iff_all_sat logic).mp h gapP
  simp [MVLogic.sat, MVLogic.eval, mvEval, logic, gapP, neg, disj] at hv

def contradictionPremises : MVLogic.Theory Atom :=
  fun X => X = .atom .p ∨ X = .neg (.atom .p)

theorem explosion : logic.entails contradictionPremises (.atom .q) := by
  intro v h
  have hp := h (.atom .p) (Or.inl rfl)
  have hnp := h (.neg (.atom .p)) (Or.inr rfl)
  cases hv : v .p <;>
    simp [MVLogic.sat, MVLogic.eval, mvEval, logic, neg, hv] at hp hnp

def des : K3 → Bool
  | .t => true
  | _ => false

def realizable (k : Koti) : Prop := ∃ x : K3, kotiOf des neg x = k

theorem corners (k : Koti) :
    realizable k ↔ k = .K1 ∨ k = .K2 ∨ k = .K4 := by
  constructor
  · rintro ⟨x, rfl⟩
    cases x <;> decide
  · intro h
    rcases h with rfl | rfl | rfl
    · exact ⟨.t, rfl⟩
    · exact ⟨.f, rfl⟩
    · exact ⟨.u, rfl⟩

end K3

theorem k3_and_fde_agree_on_excluded_middle :
    ¬ K3.logic.valid (.disj (.atom Atom.p) (.neg (.atom Atom.p))) ∧
    ¬ (∀ v : Atom → TV4,
      sat4 v (.disj (.atom Atom.p) (.neg (.atom Atom.p))) = true) := by
  constructor
  · exact K3.lem_fails
  · intro h
    have hx := h (fun _ => .N)
    simp [sat4, eval4, disj4, neg4, BuddhistComparativeLogic.mk, tr, fa] at hx

theorem k3_and_fde_differ_on_explosion :
    K3.logic.entails K3.contradictionPremises (.atom Atom.q) ∧
    ¬ entails4 (.conj (.atom Atom.p) (.neg (.atom Atom.p))) (.atom Atom.q) :=
  ⟨K3.explosion, fde_no_explosion⟩

end BuddhistComparativeLogic
