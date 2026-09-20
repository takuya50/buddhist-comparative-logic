/- SPDX-License-Identifier: Apache-2.0 -/

/-!
# Core finite logic layer

A self-contained Lean 4 port of the parts of the Isabelle session
`Buddhist_Comparative_Logic` that carry the logical content: the formula type, the
Belnap-Dunn four-valued semantics, Priest's absorbing fifth value, and the
results the rest of the session leans on.

The point of the port is to make the session's methodological claim
checkable rather than asserted. `docs/STATUS.md` says Isabelle/HOL was chosen
because non-classical object logics are usually embedded there and because
Nitpick finds countermodels automatically. What this file shows is the
other side of the ledger:

* the finite-matrix results are no harder in Lean -- `decide` discharges
  each of them once the quantifier over valuations is replaced by a
  quantifier over a finite list, exactly as `by eval` does in
  `isabelle/Core/FiniteDecisionProcedures.thy`;
* the plumbing that licenses that replacement (`entails4_iff` here,
  `all_vals_UNIV` there) costs about the same in both systems;
* what Lean does not give for free is the locale structure that the other
  twenty-eight theories use to state one set of definitions once and
  instantiate it at classical, FDE and FDE5 semantics. Reproducing that
  here would mean type classes or explicit records, and every theorem
  would carry its structure argument.

No Mathlib import: the whole tree compiles against the bare pinned toolchain
with `sh tools/check-lean.sh` from the repository root.
-/

namespace BuddhistComparativeLogic

/-! ## Formulas -/

inductive Fm (α : Type u) where
  | atom : α → Fm α
  | neg  : Fm α → Fm α
  | conj : Fm α → Fm α → Fm α
  | disj : Fm α → Fm α → Fm α
  deriving DecidableEq, Repr

open Fm

/-! ## The four values, as a pair of independent bits

`tr x` is "x is at least true", `fa x` is "x is at least false"; the two
bits are independent, which is the whole content of FDE. -/

inductive TV4 where
  | T | B | N | F
  deriving DecidableEq, Repr, Inhabited

open TV4

def tr : TV4 → Bool
  | T => true | B => true | N => false | F => false

def fa : TV4 → Bool
  | T => false | B => true | N => false | F => true

def mk (t f : Bool) : TV4 :=
  match t, f with
  | true,  true  => B
  | true,  false => T
  | false, true  => F
  | false, false => N

theorem mk_tr_fa (x : TV4) : mk (tr x) (fa x) = x := by cases x <;> rfl

def neg4 (x : TV4) : TV4 := mk (fa x) (tr x)
def conj4 (x y : TV4) : TV4 := mk (tr x && tr y) (fa x || fa y)
def disj4 (x y : TV4) : TV4 := mk (tr x || tr y) (fa x && fa y)

/-- The diamond lattice: `B` and `N` are incomparable, so their meet is `F`
and their join is `T`. -/
theorem conj4_B_N : conj4 B N = F := rfl
theorem disj4_B_N : disj4 B N = T := rfl

/-! ## Evaluation, designation, consequence -/

def eval4 (v : α → TV4) : Fm α → TV4
  | .atom a   => v a
  | .neg X    => neg4 (eval4 v X)
  | .conj X Y => conj4 (eval4 v X) (eval4 v Y)
  | .disj X Y => disj4 (eval4 v X) (eval4 v Y)

/-- Designated: at least true. -/
def sat4 (v : α → TV4) (X : Fm α) : Bool := tr (eval4 v X)

def entails4 (X Y : Fm α) : Prop := ∀ v : α → TV4, sat4 v X = true → sat4 v Y = true

/-- The classical fragment, for comparison. -/
def eval2 (v : α → Bool) : Fm α → Bool
  | .atom a   => v a
  | .neg X    => !(eval2 v X)
  | .conj X Y => eval2 v X && eval2 v Y
  | .disj X Y => eval2 v X || eval2 v Y

def entails2 (X Y : Fm α) : Prop := ∀ v : α → Bool, eval2 v X = true → eval2 v Y = true

/-! ## The classical embedding into FDE -/

/-- Isabelle's `FiniteLogics.emb`: the two classical values sit inside FDE as
`T` and `F`. -/
def emb : Bool → TV4
  | true => T
  | false => F

theorem emb_neg (b : Bool) : neg4 (emb b) = emb (!b) := by
  cases b <;> rfl

theorem emb_conj (a b : Bool) :
    conj4 (emb a) (emb b) = emb (a && b) := by
  cases a <;> cases b <;> rfl

theorem emb_disj (a b : Bool) :
    disj4 (emb a) (emb b) = emb (a || b) := by
  cases a <;> cases b <;> rfl

theorem emb_range (b : Bool) : emb b = T ∨ emb b = F := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Membership in Isabelle's designated set `{T, B}`, stated through its
equivalent Boolean designation test. -/
theorem emb_TB_iff (b : Bool) : tr (emb b) = true ↔ b = true := by
  cases b <;> decide

theorem emb_hom (v : α → Bool) (A : Fm α) :
    eval4 (fun a => emb (v a)) A = emb (eval2 v A) := by
  induction A with
  | atom _ => rfl
  | neg A ih => rw [eval4, eval2, ih, emb_neg]
  | conj A C ihA ihC => rw [eval4, eval2, ihA, ihC, emb_conj]
  | disj A C ihA ihC => rw [eval4, eval2, ihA, ihC, emb_disj]

/-- Classical satisfaction is exactly FDE satisfaction on embedded
valuations. -/
theorem fde_conservative_over_cl (v : α → Bool) (A : Fm α) :
    eval2 v A = true ↔ sat4 (fun a => emb (v a)) A = true := by
  rw [sat4, emb_hom]
  exact (emb_TB_iff (eval2 v A)).symm

/-- The material connectives used by the locale-level `iff_fm` definition in
`ManyValuedLogic`. -/
def materialImpFm (A C : Fm α) : Fm α := disj (neg A) C

def materialIffFm (A C : Fm α) : Fm α :=
  conj (materialImpFm A C) (materialImpFm C A)

theorem cl_iff_fm_sat (v : α → Bool) (A C : Fm α) :
    eval2 v (materialIffFm A C) = true ↔
      (eval2 v A = true ↔ eval2 v C = true) := by
  cases hA : eval2 v A <;> cases hC : eval2 v C <;>
    simp [materialIffFm, materialImpFm, eval2, hA, hC]

/-! ## Three atoms, so the quantifier over valuations becomes finite -/

inductive Atom where
  | p | q | r
  deriving DecidableEq, Repr, Inhabited

open Atom

abbrev Tri (β : Type) := β × β × β

def valOf (t : Tri β) : Atom → β
  | p => t.1
  | q => t.2.1
  | r => t.2.2

def triples (vs : List β) : List (Tri β) :=
  vs.flatMap fun x => vs.flatMap fun y => vs.map fun z => (x, y, z)

def all4 : List (Tri TV4) := triples [T, B, N, F]
def all2 : List (Tri Bool) := triples [true, false]

theorem all4_length : all4.length = 64 := by decide
theorem all2_length : all2.length = 8 := by decide

theorem mem_all4 (v : Atom → TV4) : (v p, v q, v r) ∈ all4 := by
  cases hp : v p <;> cases hq : v q <;> cases hr : v r <;> decide

theorem mem_all2 (v : Atom → Bool) : (v p, v q, v r) ∈ all2 := by
  cases hp : v p <;> cases hq : v q <;> cases hr : v r <;> decide

theorem valOf_eta (v : Atom → β) : valOf (v p, v q, v r) = v := by
  funext a; cases a <;> rfl

/-- The finite reformulation that makes `decide` applicable. This is the
Lean counterpart of `FiniteDecisionProcedures.all_vals_UNIV`, and costs about as much. -/
theorem entails4_iff (X Y : Fm Atom) :
    entails4 X Y ↔ ∀ t ∈ all4, sat4 (valOf t) X = true → sat4 (valOf t) Y = true := by
  constructor
  · intro h t _; exact h _
  · intro h v hx
    have := h _ (mem_all4 v)
    rw [valOf_eta v] at this
    exact this hx

theorem entails2_iff (X Y : Fm Atom) :
    entails2 X Y ↔ ∀ t ∈ all2, eval2 (valOf t) X = true → eval2 (valOf t) Y = true := by
  constructor
  · intro h t _; exact h _
  · intro h v hx
    have := h _ (mem_all2 v)
    rw [valOf_eta v] at this
    exact this hx

/-! ## The results the Isabelle session states about FDE

Each is `FiniteLogics`'s theorem of the same name, and each is `by decide`
here where Isabelle needed either a constructed countermodel or `by eval`
over an enumeration. -/

/-- Explosion holds classically (`FiniteLogics.cl_explosion`). -/
theorem cl_explosion : entails2 (conj (atom p) (neg (atom p))) (atom q) := by
  rw [entails2_iff]; decide

/-- Explosion fails in FDE (`FiniteLogics.fde_no_explosion`). -/
theorem fde_no_explosion : ¬ entails4 (conj (atom p) (neg (atom p))) (atom q) := by
  rw [entails4_iff]; decide

/-- Modus ponens holds classically (`FiniteLogics.cl_mp`). -/
theorem cl_mp : entails2 (conj (atom p) (disj (neg (atom p)) (atom q))) (atom q) := by
  rw [entails2_iff]; decide

/-- Modus ponens fails in FDE (`FiniteLogics.fde_mp_fails`). This is A. J.
Cotnoir's objection to reading Nagarjuna's catuskoti in FDE. -/
theorem fde_mp_fails : ¬ entails4 (conj (atom p) (disj (neg (atom p)) (atom q))) (atom q) := by
  rw [entails4_iff]; decide

/-- The explicit countermodel of the Isabelle proof: `p` a glut, `q` a gap. -/
def glut_p : Atom → TV4
  | p => B | q => N | r => F

theorem fde_mp_countermodel :
    sat4 glut_p (conj (atom p) (disj (neg (atom p)) (atom q))) = true
      ∧ sat4 glut_p (atom q) = false := by
  decide

/-- In FDE the material biconditional can be designated while its two sides
have different designation status.  Isabelle states these three facts as a
theorem bundle; Lean packages them as a conjunction. -/
theorem fde_iff_fm_not_equivalence :
    sat4 glut_p (materialIffFm (atom p) (atom q)) = true ∧
      sat4 glut_p (atom p) = true ∧
      sat4 glut_p (atom q) = false := by
  decide

/-- Excluded middle: classical, not FDE (`FiniteLogics.cl_lem`, `fde_lem_fails`). -/
theorem cl_lem : ∀ v : Atom → Bool, eval2 v (disj (atom p) (neg (atom p))) = true := by
  intro v
  have : ∀ t ∈ all2, eval2 (valOf t) (disj (atom p) (neg (atom p))) = true := by decide
  have h := this _ (mem_all2 v)
  rwa [valOf_eta v] at h

theorem fde_lem_fails : ¬ (∀ v : Atom → TV4, sat4 v (disj (atom p) (neg (atom p))) = true) := by
  intro h
  have := h (fun _ => N)
  simp [sat4, eval4, disj4, neg4, mk, tr, fa] at this

/-- Modus ponens is recovered on bivalent valuations: the failure needs the
glut (`FiniteLogics.fde_mp_bivalent`). -/
theorem fde_mp_bivalent (v : Atom → TV4) (hp : v p = T ∨ v p = F) (hq : v q = T ∨ v q = F) :
    sat4 v (conj (atom p) (disj (neg (atom p)) (atom q))) = true → sat4 v (atom q) = true := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    simp [sat4, eval4, hp, hq, conj4, disj4, neg4, mk, tr, fa]

/-! ## Priest's fifth value, and the collapse of the fifth corner -/

inductive TV5 where
  | fin : TV4 → TV5
  | E : TV5
  deriving DecidableEq, Repr, Inhabited

def neg5 : TV5 → TV5
  | .fin x => .fin (neg4 x)
  | .E => .E

def conj5 : TV5 → TV5 → TV5
  | .fin x, .fin y => .fin (conj4 x y)
  | _, _ => .E

def disj5 : TV5 → TV5 → TV5
  | .fin x, .fin y => .fin (disj4 x y)
  | _, _ => .E

/-- `E` is absorbing and self-negating: Priest's tables as adopted in
`FiniteLogics` (`fde5_E_absorbing`). -/
theorem neg5_E : neg5 .E = .E := rfl
theorem conj5_E_left (y : TV5) : conj5 .E y = .E := by cases y <;> rfl
theorem conj5_E_right (x : TV5) : conj5 x .E = .E := by cases x <;> rfl
theorem disj5_E_left (y : TV5) : disj5 .E y = .E := by cases y <;> rfl
theorem disj5_E_right (x : TV5) : disj5 x .E = .E := by cases x <;> rfl

/-- The four corners, by designation of a value and of its negation. -/
inductive Koti where
  | K1 | K2 | K3 | K4
  deriving DecidableEq, Repr

def kotiOf (des : β → Bool) (neg : β → β) (x : β) : Koti :=
  match des x, des (neg x) with
  | true,  false => .K1
  | false, true  => .K2
  | true,  true  => .K3
  | false, false => .K4

def des4 : TV4 → Bool := tr

def des5 : TV5 → Bool
  | .fin x => tr x
  | .E => false

/-- Alternative designation used in the Isabelle `fde5D` interpretation:
the ineffable value is designated. -/
def des5D : TV5 → Bool
  | .fin x => tr x
  | .E => true

def kotiRealizable (des : β → Bool) (neg : β → β) (k : Koti) : Prop :=
  ∃ x, kotiOf des neg x = k

/-- Classical logic realizes exactly the first two corners. -/
theorem cl_koti (k : Koti) :
    kotiRealizable (fun b : Bool => b) Bool.not k ↔
      k = Koti.K1 ∨ k = Koti.K2 := by
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inr hb.symm
    · exact Or.inl hb.symm
  · intro hk
    rcases hk with hk | hk
    · cases hk
      exact ⟨true, rfl⟩
    · cases hk
      exact ⟨false, rfl⟩

/-- All four corners are realized in FDE (`Catuskoti.fde_koti_all`). -/
theorem fde_koti_all (k : Koti) : ∃ x : TV4, kotiOf des4 neg4 x = k := by
  cases k
  · exact ⟨T, rfl⟩
  · exact ⟨F, rfl⟩
  · exact ⟨B, rfl⟩
  · exact ⟨N, rfl⟩

/-- The fifth value is not a fifth corner: at the level of designation it
collapses into the fourth, the one the gap already occupies
(`Catuskoti.fde5_koti_of_E`, `Avyakata.silence_gap_or_ineffable`). -/
theorem fifth_corner_collapses :
    kotiOf des5 neg5 .E = Koti.K4 ∧ kotiOf des5 neg5 (.fin N) = Koti.K4 := by decide

/-- Isabelle-compatible names for the two designation policies. -/
theorem fde5_koti_of_E : kotiOf des5 neg5 .E = Koti.K4 := by decide

theorem fde5D_koti_of_E : kotiOf des5D neg5 .E = Koti.K3 := by decide

/-- What separates them is the value, not the corner
(`Catuskoti.fifth_corner_value_level`). -/
theorem fifth_corner_value_level (x : TV4) : TV5.fin x ≠ TV5.E := by
  intro h; cases h

/-! ## Containment: FDE5 is FDE plus atom containment

`FDEProofTheory.fde5_is_fde_plus_containment` proves the equivalence in
general. Here we check the separating instance: disjunction introduction is
FDE-valid and FDE5-invalid, because the new disjunct brings in an atom the
premise does not contain. -/

def eval5 (v : α → TV5) : Fm α → TV5
  | .atom a   => v a
  | .neg X    => neg5 (eval5 v X)
  | .conj X Y => conj5 (eval5 v X) (eval5 v Y)
  | .disj X Y => disj5 (eval5 v X) (eval5 v Y)

def vE : Atom → TV5
  | p => .fin T | q => .E | r => .fin T

def glut5_p : Atom → TV5
  | p => .fin B | q => .fin F | r => .fin F

theorem disj_intro_fde : entails4 (atom p) (disj (atom p) (atom q)) := by
  rw [entails4_iff]; decide

theorem disj_intro_fde5_fails :
    des5 (eval5 vE (atom p)) = true ∧ des5 (eval5 vE (disj (atom p) (atom q))) = false := by
  decide

/-- Material modus ponens fails for FDE5 on the same glut countermodel as
for FDE.  The three implications spell out satisfaction of the two-premise
theory used by the Isabelle statement. -/
theorem fde5_mp_fails :
    ¬ (∀ v : Atom → TV5,
      des5 (eval5 v (atom p)) = true →
      des5 (eval5 v (disj (neg (atom p)) (atom q))) = true →
      des5 (eval5 v (atom q)) = true) := by
  intro h
  have hq := h glut5_p (by decide) (by decide)
  exact Bool.noConfusion hq

end BuddhistComparativeLogic
