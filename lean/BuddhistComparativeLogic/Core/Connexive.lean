/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation

/-!
# A connexive reading of 「不生不滅」

Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Connexive.thy`.  Truth and falsity are tracked
independently.  The connexive conditional is compared with FDE's material
conditional, including the bivalent result that turns the pair of negated
conditionals into absence of own-being.
-/

namespace BuddhistComparativeLogic

inductive CFm (α : Type) where
  | atom : α → CFm α
  | neg : CFm α → CFm α
  | conj : CFm α → CFm α → CFm α
  | disj : CFm α → CFm α → CFm α
  | imp : CFm α → CFm α → CFm α
  deriving Repr

namespace CFm

def boolImp (a b : Bool) : Bool := (!a) || b

/-- Material connexive logic MC: truth and falsity conditions are separate. -/
def cimp4 (x y : TV4) : TV4 :=
  mk (boolImp (tr x) (tr y)) (boolImp (tr x) (fa y))

def mimp4 (x y : TV4) : TV4 := disj4 (neg4 x) y

def eval (implication : TV4 → TV4 → TV4) (v : α → TV4) : CFm α → TV4
  | .atom a => v a
  | .neg X => neg4 (eval implication v X)
  | .conj X Y => conj4 (eval implication v X) (eval implication v Y)
  | .disj X Y => disj4 (eval implication v X) (eval implication v Y)
  | .imp X Y => implication (eval implication v X) (eval implication v Y)

def sat (implication : TV4 → TV4 → TV4) (v : α → TV4) (A : CFm α) : Bool :=
  tr (eval implication v A)

def valid (implication : TV4 → TV4 → TV4) (A : CFm α) : Prop :=
  ∀ v, sat implication v A = true

theorem aristotle_connexive (X : CFm α) :
    valid cimp4 (.neg (.imp X (.neg X))) := by
  intro v
  cases hx : eval cimp4 v X <;>
    simp [sat, eval, hx, cimp4, boolImp, neg4, mk, tr, fa]

theorem boethius_connexive (X Y : CFm α) :
    valid cimp4 (.imp (.imp X Y) (.neg (.imp X (.neg Y)))) := by
  intro v
  cases hx : eval cimp4 v X <;>
    cases hy : eval cimp4 v Y <;>
    simp [sat, eval, hx, hy, cimp4, boolImp, neg4, mk, tr, fa]

def allFalse : Atom → TV4 := fun _ => .F

theorem aristotle_fails_material :
    ¬ valid mimp4 (.neg (.imp (.atom Atom.p) (.neg (.atom Atom.p)))) := by
  intro h
  simpa [sat, eval, mimp4, allFalse, neg4, disj4, mk, tr, fa] using h allFalse

def pFalseQTrue : Atom → TV4
  | .q => .T
  | _ => .F

theorem connexive_not_symmetric :
    ¬ valid cimp4 (.imp (.imp (.atom Atom.p) (.atom Atom.q))
                         (.imp (.atom Atom.q) (.atom Atom.p))) := by
  intro h
  simpa [sat, eval, cimp4, boolImp, pFalseQTrue, mk, tr, fa] using h pFalseQTrue

def hs10Conn (existence arising : α) : CFm α :=
  .conj (.neg (.imp (.atom existence) (.atom arising)))
        (.neg (.imp (.atom existence) (.neg (.atom arising))))

theorem hs10_connexive_iff (v : α → TV4) (e a : α) :
    sat cimp4 v (hs10Conn e a) = true ↔
      (tr (v e) = true → v a = .B) := by
  cases he : v e <;> cases ha : v a <;>
    simp [sat, eval, hs10Conn, cimp4, boolImp, neg4, conj4, mk, tr, fa, he, ha]

theorem hs10_material_iff (v : α → TV4) (e a : α) :
    sat mimp4 v (hs10Conn e a) = true ↔
      tr (v e) = true ∧ v a = .B := by
  cases he : v e <;> cases ha : v a <;>
    simp [sat, eval, hs10Conn, mimp4, neg4, conj4, disj4, mk, tr, fa, he, ha]

def Bivalent (x : TV4) : Prop := x = .T ∨ x = .F

theorem hs10_connexive_bivalent
    (v : α → TV4) (e a : α) (he : Bivalent (v e)) (ha : Bivalent (v a)) :
    sat cimp4 v (hs10Conn e a) = true ↔ v e = .F := by
  rw [hs10_connexive_iff]
  rcases he with he | he <;> rcases ha with ha | ha
  all_goals simp_all [tr]

theorem hs10_material_bivalent_unsat
    (v : α → TV4) (e a : α) (he : Bivalent (v e)) (ha : Bivalent (v a)) :
    sat mimp4 v (hs10Conn e a) = false := by
  cases hs : sat mimp4 v (hs10Conn e a)
  · rfl
  · have hm := (hs10_material_iff v e a).mp hs
    rcases he with he | he <;> rcases ha with ha | ha
    all_goals simp_all [tr]

def noSvabhava : Atom → TV4
  | .p => .F
  | _ => .T

theorem hs10_connexive_witness : sat cimp4 noSvabhava (hs10Conn Atom.p Atom.q) = true := by
  decide

end CFm
end BuddhistComparativeLogic
