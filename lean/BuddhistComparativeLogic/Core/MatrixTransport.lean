/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Ineffable

/-!
# Transporting universal designation across explicit finite matrices

The remaining instance-classification problem should not depend on the names
chosen for truth values.  This module records the exact data required for two
many-valued matrices to be isomorphic and proves that ordinary consequence,
positive universal designation, and unrestricted universal designation are
all invariant under that data.

The final section supplies a second, fully explicit presentation of FDE whose
values are pairs of truth and falsity bits.  It is classified by the general
transport theorem rather than by repeating the substantial `theta` proof.
No historical identification of an arbitrary proposed matrix is inferred:
callers must still construct the displayed isomorphism.
-/

namespace BuddhistComparativeLogic
namespace MatrixTransport

open Fm

/-- An isomorphism of matrices preserves designation and every primitive
truth operation, as well as being a bijection on values. -/
structure MatrixIso (L : MVLogic V) (K : MVLogic W) where
  toFun : V → W
  invFun : W → V
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  designated_iff : ∀ x, K.designated (toFun x) ↔ L.designated x
  map_neg : ∀ x, K.neg (toFun x) = toFun (L.neg x)
  map_conj : ∀ x y, K.mconj (toFun x) (toFun y) = toFun (L.mconj x y)
  map_disj : ∀ x y, K.mdisj (toFun x) (toFun y) = toFun (L.mdisj x y)

namespace MatrixIso

variable {L : MVLogic V} {K : MVLogic W}

@[simp] theorem inv_to (e : MatrixIso L K) (x : V) :
    e.invFun (e.toFun x) = x :=
  e.left_inv x

@[simp] theorem to_inv (e : MatrixIso L K) (y : W) :
    e.toFun (e.invFun y) = y :=
  e.right_inv y

theorem to_injective (e : MatrixIso L K) : Function.Injective e.toFun := by
  intro x y h
  simpa using congrArg e.invFun h

theorem inv_injective (e : MatrixIso L K) : Function.Injective e.invFun := by
  intro x y h
  simpa using congrArg e.toFun h

theorem inv_map_neg (e : MatrixIso L K) (y : W) :
    e.invFun (K.neg y) = L.neg (e.invFun y) := by
  have h := congrArg e.invFun (e.map_neg (e.invFun y))
  simpa using h

theorem inv_map_conj (e : MatrixIso L K) (x y : W) :
    e.invFun (K.mconj x y) = L.mconj (e.invFun x) (e.invFun y) := by
  have h := congrArg e.invFun (e.map_conj (e.invFun x) (e.invFun y))
  simpa using h

theorem inv_map_disj (e : MatrixIso L K) (x y : W) :
    e.invFun (K.mdisj x y) = L.mdisj (e.invFun x) (e.invFun y) := by
  have h := congrArg e.invFun (e.map_disj (e.invFun x) (e.invFun y))
  simpa using h

/-- Reverse an explicit matrix isomorphism without adding any assumptions. -/
def symm (e : MatrixIso L K) : MatrixIso K L where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  designated_iff := by
    intro y
    simpa using (e.designated_iff (e.invFun y)).symm
  map_neg := by
    intro y
    exact (e.inv_map_neg y).symm
  map_conj := by
    intro x y
    exact (e.inv_map_conj x y).symm
  map_disj := by
    intro x y
    exact (e.inv_map_disj x y).symm

@[simp] theorem symm_toFun (e : MatrixIso L K) : e.symm.toFun = e.invFun := rfl
@[simp] theorem symm_invFun (e : MatrixIso L K) : e.symm.invFun = e.toFun := rfl

/-- Point valuations commute with evaluation along a matrix isomorphism. -/
theorem eval_map (e : MatrixIso L K) (v : α → V) (A : Fm α) :
    K.eval (fun a => e.toFun (v a)) A = e.toFun (L.eval v A) := by
  induction A with
  | atom _ => rfl
  | neg A ih =>
      change K.neg (K.eval (fun a => e.toFun (v a)) A) =
        e.toFun (L.neg (L.eval v A))
      rw [ih, e.map_neg]
  | conj A C ihA ihC =>
      change K.mconj (K.eval (fun a => e.toFun (v a)) A)
          (K.eval (fun a => e.toFun (v a)) C) =
        e.toFun (L.mconj (L.eval v A) (L.eval v C))
      rw [ihA, ihC, e.map_conj]
  | disj A C ihA ihC =>
      change K.mdisj (K.eval (fun a => e.toFun (v a)) A)
          (K.eval (fun a => e.toFun (v a)) C) =
        e.toFun (L.mdisj (L.eval v A) (L.eval v C))
      rw [ihA, ihC, e.map_disj]

theorem sat_map_iff (e : MatrixIso L K) (v : α → V) (A : Fm α) :
    K.sat (fun a => e.toFun (v a)) A ↔ L.sat v A := by
  change K.designated (K.eval (fun a => e.toFun (v a)) A) ↔
    L.designated (L.eval v A)
  rw [e.eval_map]
  exact e.designated_iff _

theorem entails_transport (e : MatrixIso L K)
    {Γ : MVLogic.Theory α} {A : Fm α} (h : L.entails Γ A) :
    K.entails Γ A := by
  intro w hprem
  let v : α → V := fun a => e.invFun (w a)
  have hprem' : ∀ C, Γ C → L.sat v C := by
    intro C hC
    have hs := hprem C hC
    have hmapped : K.sat (fun a => e.toFun (v a)) C := by
      simpa [v] using hs
    exact (e.sat_map_iff v C).1 hmapped
  have hout := h v hprem'
  have hmapped := (e.sat_map_iff v A).2 hout
  simpa [v] using hmapped

theorem entails_iff (e : MatrixIso L K)
    (Γ : MVLogic.Theory α) (A : Fm α) :
    L.entails Γ A ↔ K.entails Γ A :=
  ⟨e.entails_transport, e.symm.entails_transport⟩

/-! ## Predicate-set and universal-designation transport -/

/-- Transport a predicate set through the value bijection. -/
def mapSet (e : MatrixIso L K) (S : PSet V) : PSet W :=
  fun y => S (e.invFun y)

@[simp] theorem mem_mapSet (e : MatrixIso L K) (S : PSet V) (y : W) :
    e.mapSet S y ↔ S (e.invFun y) :=
  Iff.rfl

theorem mapSet_nonempty_iff (e : MatrixIso L K) (S : PSet V) :
    pnonempty (e.mapSet S) ↔ pnonempty S := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨e.invFun y, hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨e.toFun x, by simpa [mapSet] using hx⟩

theorem mapSet_symm_mapSet (e : MatrixIso L K) (S : PSet V) :
    e.symm.mapSet (e.mapSet S) = S := by
  apply pset_ext
  intro x
  simp [mapSet]

theorem mapSet_mapSet_symm (e : MatrixIso L K) (S : PSet W) :
    e.mapSet (e.symm.mapSet S) = S := by
  apply pset_ext
  intro y
  simp [mapSet]

/-- Plurivalent evaluation commutes with pointwise transport of every set of
possible atom values. -/
theorem peval_map (e : MatrixIso L K) (Vn : α → PSet V) (A : Fm α) :
    peval K.neg K.mconj K.mdisj (fun a => e.mapSet (Vn a)) A =
      e.mapSet (peval L.neg L.mconj L.mdisj Vn A) := by
  induction A with
  | atom _ => rfl
  | neg A ih =>
      rw [peval, peval, ih]
      apply pset_ext
      intro z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨e.invFun y, hy, e.inv_map_neg y⟩
      · rintro ⟨x, hx, hz⟩
        refine ⟨e.toFun x, ?_, ?_⟩
        · simpa [mapSet] using hx
        · apply e.inv_injective
          rw [hz, e.inv_map_neg, e.inv_to]
  | conj A C ihA ihC =>
      rw [peval, peval, ihA, ihC]
      apply pset_ext
      intro z
      constructor
      · rintro ⟨x, y, hx, hy, rfl⟩
        exact ⟨e.invFun x, e.invFun y, hx, hy, e.inv_map_conj x y⟩
      · rintro ⟨x, y, hx, hy, hz⟩
        refine ⟨e.toFun x, e.toFun y, ?_, ?_, ?_⟩
        · simpa [mapSet] using hx
        · simpa [mapSet] using hy
        · apply e.inv_injective
          rw [hz, e.inv_map_conj, e.inv_to, e.inv_to]
  | disj A C ihA ihC =>
      rw [peval, peval, ihA, ihC]
      apply pset_ext
      intro z
      constructor
      · rintro ⟨x, y, hx, hy, rfl⟩
        exact ⟨e.invFun x, e.invFun y, hx, hy, e.inv_map_disj x y⟩
      · rintro ⟨x, y, hx, hy, hz⟩
        refine ⟨e.toFun x, e.toFun y, ?_, ?_, ?_⟩
        · simpa [mapSet] using hx
        · simpa [mapSet] using hy
        · apply e.inv_injective
          rw [hz, e.inv_map_disj, e.inv_to, e.inv_to]

theorem upsat_map_iff (e : MatrixIso L K) (Vn : α → PSet V) (A : Fm α) :
    upsat K (fun a => e.mapSet (Vn a)) A ↔ upsat L Vn A := by
  rw [upsat, upsat, e.peval_map]
  constructor
  · intro h x hx
    exact (e.designated_iff x).1
      (h (e.toFun x) (by simpa [mapSet] using hx))
  · intro h y hy
    have hs := h (e.invFun y) hy
    have ht := (e.designated_iff (e.invFun y)).2 hs
    simpa using ht

theorem pos_upentails_transport (e : MatrixIso L K)
    {Γ : MVLogic.Theory α} {A : Fm α} (h : pos_upentails L Γ A) :
    pos_upentails K Γ A := by
  intro Wn hpos hprem
  let Vn : α → PSet V := fun a => e.symm.mapSet (Wn a)
  have hpos' : ∀ a, pnonempty (Vn a) := by
    intro a
    exact (e.symm.mapSet_nonempty_iff (Wn a)).2 (hpos a)
  have hprem' : ∀ C, Γ C → upsat L Vn C := by
    intro C hC
    exact (e.symm.upsat_map_iff Wn C).2 (hprem C hC)
  have hout := h Vn hpos' hprem'
  exact (e.symm.upsat_map_iff Wn A).1 hout

theorem pos_upentails_iff (e : MatrixIso L K)
    (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails L Γ A ↔ pos_upentails K Γ A :=
  ⟨e.pos_upentails_transport, e.symm.pos_upentails_transport⟩

theorem upentails_transport (e : MatrixIso L K)
    {Γ : MVLogic.Theory α} {A : Fm α} (h : upentails L Γ A) :
    upentails K Γ A := by
  intro Wn hprem
  let Vn : α → PSet V := fun a => e.symm.mapSet (Wn a)
  have hprem' : ∀ C, Γ C → upsat L Vn C := by
    intro C hC
    exact (e.symm.upsat_map_iff Wn C).2 (hprem C hC)
  have hout := h Vn hprem'
  exact (e.symm.upsat_map_iff Wn A).1 hout

theorem upentails_iff (e : MatrixIso L K)
    (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails L Γ A ↔ upentails K Γ A :=
  ⟨e.upentails_transport, e.symm.upentails_transport⟩

end MatrixIso

/-! ## An explicit truth/falsity-bit presentation of FDE -/

namespace BitPairFDE

abbrev Value := Bool × Bool

def neg : Value → Value
  | (t, f) => (f, t)

def conj : Value → Value → Value
  | (tx, fx), (ty, fy) => (tx && ty, fx || fy)

def disj : Value → Value → Value
  | (tx, fx), (ty, fy) => (tx || ty, fx && fy)

def logic : MVLogic Value where
  designated x := x.1 = true
  neg := neg
  mconj := conj
  mdisj := disj
  designated_nonempty := ⟨(true, false), rfl⟩
  designated_proper := ⟨(false, false), by decide⟩

end BitPairFDE

/-- The pair presentation contains exactly the same matrix structure as FDE. -/
def fdeBitIso : MatrixIso mvFDE BitPairFDE.logic where
  toFun x := (tr x, fa x)
  invFun x := mk x.1 x.2
  left_inv := mk_tr_fa
  right_inv := by
    rintro ⟨t, f⟩
    cases t <;> cases f <;> rfl
  designated_iff := by intro x; rfl
  map_neg := by intro x; cases x <;> rfl
  map_conj := by intro x y; cases x <;> cases y <;> rfl
  map_disj := by intro x y; cases x <;> cases y <;> rfl

theorem bitPair_entails_iff_fde (Γ : MVLogic.Theory α) (A : Fm α) :
    BitPairFDE.logic.entails Γ A ↔ mvFDE.entails Γ A :=
  (fdeBitIso.entails_iff Γ A).symm

theorem bitPair_pos_upentails_iff_fde
    (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails BitPairFDE.logic Γ A ↔ mvFDE.entails Γ A := by
  calc
    pos_upentails BitPairFDE.logic Γ A ↔ pos_upentails mvFDE Γ A :=
      (fdeBitIso.pos_upentails_iff Γ A).symm
    _ ↔ mvFDE.entails Γ A := pos_up_fde_is_fde Γ A

theorem bitPair_upentails_iff_fde
    (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails BitPairFDE.logic Γ A ↔
      mvFDE.entails (restrictToAtoms Γ A) A := by
  calc
    upentails BitPairFDE.logic Γ A ↔ upentails mvFDE Γ A :=
      (fdeBitIso.upentails_iff Γ A).symm
    _ ↔ mvFDE.entails (restrictToAtoms Γ A) A :=
      priest_open_question_fde Γ A

/-- The generic absorbing-ineffable theorem applies to the explicit pair
matrix after its base consequence has been transported to FDE. -/
theorem bitPair_ineff_pos_upentails_iff
    (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails (WithIneff.logic BitPairFDE.logic) Γ A ↔
      mvFDE.entails Γ A ∧
        (psubset (atoms A) (WithIneff.coveredBy Γ) ∨
          WithIneff.PosUnsatisfiable BitPairFDE.logic Γ) := by
  rw [WithIneff.pos_upentails_iff, bitPair_pos_upentails_iff_fde]

end MatrixTransport
end BuddhistComparativeLogic
