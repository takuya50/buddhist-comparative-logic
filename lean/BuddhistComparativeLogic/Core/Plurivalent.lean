/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.MVLogic

/-!
# Plurivalent semantics

Lean counterpart of `isabelle/Core/PlurivalentSemantics.thy`.  Sets are represented by their
membership predicates (`PSet α = α → Prop`), which keeps the image semantics
literal while requiring no set library.  The functional and relational
liftings are compared explicitly, and Priest's absorbing value is recovered
as the empty-set case.
-/

namespace BuddhistComparativeLogic

open Fm TV4 TV5 Atom Koti

abbrev PSet (α : Type u) := α → Prop

def pempty : PSet α := fun _ => False
def psingleton (a : α) : PSet α := fun x => x = a
def pnonempty (S : PSet α) : Prop := ∃ x, S x
def psubset (S T : PSet α) : Prop := ∀ x, S x → T x
def pintersects (S T : PSet α) : Prop := ∃ x, S x ∧ T x

def pimage (f : α → β) (S : PSet α) : PSet β :=
  fun y => ∃ x, S x ∧ y = f x

def pimage₂ (f : α → β → γ) (S : PSet α) (T : PSet β) : PSet γ :=
  fun z => ∃ x y, S x ∧ T y ∧ z = f x y

/-- A classical proposition reflected into a Boolean, used only to package
predicate sets into finite truth values. -/
noncomputable def propBool (P : Prop) : Bool :=
  @ite Bool P (Classical.propDecidable P) true false

theorem propBool_eq_true (P : Prop) : propBool P = true ↔ P := by
  classical
  by_cases h : P <;> simp [propBool, h]

theorem propBool_eq_false (P : Prop) : propBool P = false ↔ ¬ P := by
  classical
  by_cases h : P <;> simp [propBool, h]

theorem pset_ext {S T : PSet α} (h : ∀ x, S x ↔ T x) : S = T := by
  funext x
  exact propext (h x)

theorem pimage_singleton (f : α → β) (x : α) :
    pimage f (psingleton x) = psingleton (f x) := by
  apply pset_ext
  intro y
  simp [pimage, psingleton]

theorem pimage₂_singleton (f : α → β → γ) (x : α) (y : β) :
    pimage₂ f (psingleton x) (psingleton y) = psingleton (f x y) := by
  apply pset_ext
  intro z
  simp [pimage₂, psingleton]

theorem pimage_empty (f : α → β) : pimage f (pempty : PSet α) = pempty := by
  apply pset_ext
  intro y
  simp [pimage, pempty]

theorem pimage₂_empty_left (f : α → β → γ) (T : PSet β) :
    pimage₂ f (pempty : PSet α) T = pempty := by
  apply pset_ext
  intro z
  simp [pimage₂, pempty]

theorem pimage₂_empty_right (f : α → β → γ) (S : PSet α) :
    pimage₂ f S (pempty : PSet β) = pempty := by
  apply pset_ext
  intro z
  simp [pimage₂, pempty]

theorem pimage_nonempty_iff (f : α → β) (S : PSet α) :
    pnonempty (pimage f S) ↔ pnonempty S := by
  constructor
  · rintro ⟨_, x, hx, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨f x, x, hx, rfl⟩

theorem pimage₂_nonempty_iff (f : α → β → γ) (S : PSet α) (T : PSet β) :
    pnonempty (pimage₂ f S T) ↔ pnonempty S ∧ pnonempty T := by
  constructor
  · rintro ⟨_, x, y, hx, hy, _⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨f x y, x, y, hx, hy, rfl⟩

/-! ## Functional (image) plurivalent evaluation -/

def peval (neg : V → V) (mconj mdisj : V → V → V)
    (Vn : α → PSet V) : Fm α → PSet V
  | .atom a => Vn a
  | .neg A => pimage neg (peval neg mconj mdisj Vn A)
  | .conj A C => pimage₂ mconj (peval neg mconj mdisj Vn A)
      (peval neg mconj mdisj Vn C)
  | .disj A C => pimage₂ mdisj (peval neg mconj mdisj Vn A)
      (peval neg mconj mdisj Vn C)

theorem peval_singleton (neg : V → V) (mconj mdisj : V → V → V)
    (v : α → V) (A : Fm α) :
    peval neg mconj mdisj (fun a => psingleton (v a)) A =
      psingleton (mvEval neg mconj mdisj v A) := by
  induction A with
  | atom _ => rfl
  | neg A ih =>
      rw [peval, mvEval, ih, pimage_singleton]
  | conj A C ihA ihC =>
      rw [peval, mvEval, ihA, ihC, pimage₂_singleton]
  | disj A C ihA ihC =>
      rw [peval, mvEval, ihA, ihC, pimage₂_singleton]

theorem peval_nonempty (neg : V → V) (mconj mdisj : V → V → V)
    (Vn : α → PSet V) (A : Fm α) (hV : ∀ a, pnonempty (Vn a)) :
    pnonempty (peval neg mconj mdisj Vn A) := by
  induction A with
  | atom a => exact hV a
  | neg A ih => exact (pimage_nonempty_iff _ _).2 ih
  | conj A C ihA ihC => exact (pimage₂_nonempty_iff _ _ _).2 ⟨ihA, ihC⟩
  | disj A C ihA ihC => exact (pimage₂_nonempty_iff _ _ _).2 ⟨ihA, ihC⟩

def psat (L : MVLogic V) (Vn : α → PSet V) (A : Fm α) : Prop :=
  pintersects (peval L.neg L.mconj L.mdisj Vn A) L.designated

def pentails (L : MVLogic V) (Γ : MVLogic.Theory α) (A : Fm α) : Prop :=
  ∀ Vn, (∀ B, Γ B → psat L Vn B) → psat L Vn A

theorem psat_singleton (L : MVLogic V) (v : α → V) (A : Fm α) :
    psat L (fun a => psingleton (v a)) A ↔ L.sat v A := by
  rw [psat, peval_singleton]
  simp [pintersects, psingleton, MVLogic.sat, MVLogic.eval]

theorem pentails_refl (L : MVLogic V) {Γ : MVLogic.Theory α} {A : Fm α}
    (hA : Γ A) : pentails L Γ A := by
  intro Vn hΓ
  exact hΓ A hA

theorem pentails_mono (L : MVLogic V) {Γ Δ : MVLogic.Theory α} {A : Fm α}
    (hsub : ∀ {B}, Γ B → Δ B) (h : pentails L Γ A) : pentails L Δ A := by
  intro Vn hΔ
  exact h Vn (fun B hB => hΔ B (hsub hB))

theorem entails_of_pentails (L : MVLogic V) {Γ : MVLogic.Theory α} {A : Fm α}
    (h : pentails L Γ A) : L.entails Γ A := by
  intro v hΓ
  exact (psat_singleton L v A).1
    (h (fun a => psingleton (v a))
      (fun B hB => (psat_singleton L v B).2 (hΓ B hB)))

noncomputable def pkoti_of (L : MVLogic V) (S : PSet V) : Koti :=
  match propBool (pintersects S L.designated),
      propBool (pintersects (pimage L.neg S) L.designated) with
  | true, false => K1
  | false, true => K2
  | true, true => K3
  | false, false => K4

theorem pkoti_empty (L : MVLogic V) : pkoti_of L (pempty : PSet V) = K4 := by
  classical
  simp [pkoti_of, propBool, pintersects, pimage, pempty]

/-! ## FDE5 as the at-most-one-value fragment of plurivalent FDE -/

def sing : TV5 → PSet TV4
  | .fin x => psingleton x
  | .E => pempty

theorem sing_neg (t : TV5) : pimage neg4 (sing t) = sing (neg5 t) := by
  cases t with
  | fin x => simp [sing, neg5, pimage_singleton]
  | E => simp [sing, neg5, pimage_empty]

theorem sing_conj (s t : TV5) :
    pimage₂ conj4 (sing s) (sing t) = sing (conj5 s t) := by
  cases s <;> cases t <;>
    simp [sing, conj5, pimage₂_singleton, pimage₂_empty_left,
      pimage₂_empty_right]

theorem sing_disj (s t : TV5) :
    pimage₂ disj4 (sing s) (sing t) = sing (disj5 s t) := by
  cases s <;> cases t <;>
    simp [sing, disj5, pimage₂_singleton, pimage₂_empty_left,
      pimage₂_empty_right]

theorem fde5_is_singleton_fragment (Vn : α → TV5) (A : Fm α) :
    peval neg4 conj4 disj4 (fun a => sing (Vn a)) A =
      sing (mvEval neg5 conj5 disj5 Vn A) := by
  induction A with
  | atom _ => rfl
  | neg A ih => rw [peval, mvEval, ih, sing_neg]
  | conj A C ihA ihC => rw [peval, mvEval, ihA, ihC, sing_conj]
  | disj A C ihA ihC => rw [peval, mvEval, ihA, ihC, sing_disj]

theorem fde5_sat_is_fde_psat (Vn : α → TV5) (A : Fm α) :
    mvFDE5.sat Vn A ↔ psat mvFDE (fun a => sing (Vn a)) A := by
  change des5 (mvEval neg5 conj5 disj5 Vn A) = true ↔
    pintersects (peval neg4 conj4 disj4 (fun a => sing (Vn a)) A)
      (fun x => tr x = true)
  rw [fde5_is_singleton_fragment]
  cases h : mvEval neg5 conj5 disj5 Vn A with
  | fin x => cases x <;> simp [sing, psingleton, pintersects, des5, tr]
  | E => simp [sing, pempty, pintersects, des5]

theorem pkoti_sing (t : TV5) : pkoti_of mvFDE (sing t) = kotiOf des5 neg5 t := by
  classical
  cases t with
  | fin x => cases x <;> simp [pkoti_of, propBool, sing, pintersects,
      pimage, psingleton, mvFDE, kotiOf, des5, tr, neg5, neg4, mk, fa]
  | E => simp [pkoti_of, propBool, sing, pempty, pintersects, pimage,
      mvFDE, kotiOf, des5, neg5]

theorem fifth_corner_is_valueless : pkoti_of mvFDE (pempty : PSet TV4) = K4 :=
  pkoti_empty mvFDE

/-! ## Functional plurivalent classical logic -/

theorem exists_bool_iff (P : Bool → Prop) :
    (∃ b, P b) ↔ P false ∨ P true := by
  constructor
  · rintro ⟨b, hb⟩
    cases b <;> simp_all
  · intro h
    cases h with
    | inl h => exact ⟨false, h⟩
    | inr h => exact ⟨true, h⟩

theorem pnonempty_bool_iff (S : PSet Bool) :
    pnonempty S ↔ S false ∨ S true := by
  exact exists_bool_iff S

theorem bex_id (S : PSet Bool) :
    (∃ x, S x ∧ x = true) ↔ S true := by
  simp

theorem bex_not (S : PSet Bool) :
    (∃ x, S x ∧ x = false) ↔ S false := by
  simp

theorem img_nonempty (f : α → β → γ) (S : PSet α) (Tn : PSet β)
    (hS : pnonempty S) (hT : pnonempty Tn) :
    pnonempty (pimage₂ f S Tn) :=
  (pimage₂_nonempty_iff f S Tn).2 ⟨hS, hT⟩

noncomputable def bs (S : PSet Bool) : TV4 :=
  mk (propBool (S true)) (propBool (S false))

noncomputable def bs5 (S : PSet Bool) : TV5 :=
  match propBool (pnonempty S) with
  | true => .fin (bs S)
  | false => .E

theorem img_neg_T (S : PSet Bool) : pimage Bool.not S true ↔ S false := by
  simp [pimage]

theorem img_neg_F (S : PSet Bool) : pimage Bool.not S false ↔ S true := by
  simp [pimage]

theorem img_conj_T (S Tn : PSet Bool) :
    pimage₂ Bool.and S Tn true ↔ S true ∧ Tn true := by
  simp [pimage₂]

theorem img_conj_F (S Tn : PSet Bool) :
    pimage₂ Bool.and S Tn false ↔
      (S false ∧ Tn false) ∨ (S false ∧ Tn true) ∨ (S true ∧ Tn false) := by
  simp only [pimage₂, exists_bool_iff]
  grind

theorem img_disj_T (S Tn : PSet Bool) :
    pimage₂ Bool.or S Tn true ↔
      (S false ∧ Tn true) ∨ (S true ∧ Tn false) ∨ (S true ∧ Tn true) := by
  simp only [pimage₂, exists_bool_iff]
  grind

theorem img_disj_F (S Tn : PSet Bool) :
    pimage₂ Bool.or S Tn false ↔ S false ∧ Tn false := by
  simp [pimage₂]

theorem bs5_neg (S : PSet Bool) : bs5 (pimage Bool.not S) = neg5 (bs5 S) := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    simp_all [bs5, bs, propBool, pnonempty_bool_iff, pimage_nonempty_iff,
      img_neg_T, img_neg_F, neg5, neg4, mk, tr, fa]

theorem bs5_conj (S Tn : PSet Bool) :
    bs5 (pimage₂ Bool.and S Tn) = conj5 (bs5 S) (bs5 Tn) := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    by_cases tt : Tn true <;> by_cases tf : Tn false <;>
      simp_all [bs5, bs, propBool, pnonempty_bool_iff, pimage₂_nonempty_iff,
        img_conj_T, img_conj_F, conj5, conj4, mk, tr, fa]

theorem bs5_disj (S Tn : PSet Bool) :
    bs5 (pimage₂ Bool.or S Tn) = disj5 (bs5 S) (bs5 Tn) := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    by_cases tt : Tn true <;> by_cases tf : Tn false <;>
      simp_all [bs5, bs, propBool, pnonempty_bool_iff, pimage₂_nonempty_iff,
        img_disj_T, img_disj_F, disj5, disj4, mk, tr, fa]

theorem image_plurivalent_classical_is_fde5 (Vn : α → PSet Bool) (A : Fm α) :
    bs5 (peval Bool.not Bool.and Bool.or Vn A) =
      mvEval neg5 conj5 disj5 (fun a => bs5 (Vn a)) A := by
  induction A with
  | atom _ => rfl
  | neg A ih => rw [peval, mvEval, ← ih, bs5_neg]
  | conj A C ihA ihC => rw [peval, mvEval, ← ihA, ← ihC, bs5_conj]
  | disj A C ihA ihC => rw [peval, mvEval, ← ihA, ← ihC, bs5_disj]

theorem image_plurivalent_classical_has_no_gap (S : PSet Bool) :
    bs5 S ≠ .fin N := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    simp_all [bs5, bs, propBool, pnonempty_bool_iff, mk]

theorem existential_bool_designation (S : PSet Bool) :
    pintersects S (fun b => b = true) ↔ des5 (bs5 S) = true := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    simp_all [pintersects, bs5, bs, propBool, pnonempty_bool_iff,
      des5, tr, mk]

theorem image_plurivalent_classical_sat (Vn : α → PSet Bool) (A : Fm α) :
    psat mvClassical Vn A ↔ mvFDE5.sat (fun a => bs5 (Vn a)) A := by
  change pintersects (peval Bool.not Bool.and Bool.or Vn A)
      (fun b => b = true) ↔
    des5 (mvEval neg5 conj5 disj5 (fun a => bs5 (Vn a)) A) = true
  rw [existential_bool_designation, image_plurivalent_classical_is_fde5]

/-! ## Relational plurivalent classical logic -/

def rneg (S : PSet Bool) : PSet Bool
  | true => S false
  | false => S true

def rconj (S Tn : PSet Bool) : PSet Bool
  | true => S true ∧ Tn true
  | false => S false ∨ Tn false

def rdisj (S Tn : PSet Bool) : PSet Bool
  | true => S true ∨ Tn true
  | false => S false ∧ Tn false

def reval (Vn : α → PSet Bool) : Fm α → PSet Bool
  | .atom a => Vn a
  | .neg A => rneg (reval Vn A)
  | .conj A C => rconj (reval Vn A) (reval Vn C)
  | .disj A C => rdisj (reval Vn A) (reval Vn C)

theorem bs_rneg (S : PSet Bool) : bs (rneg S) = neg4 (bs S) := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    simp_all [bs, propBool, rneg, neg4, mk, tr, fa]

theorem bs_rconj (S Tn : PSet Bool) : bs (rconj S Tn) = conj4 (bs S) (bs Tn) := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    by_cases tt : Tn true <;> by_cases tf : Tn false <;>
      simp_all [bs, propBool, rconj, conj4, mk, tr, fa]

theorem bs_rdisj (S Tn : PSet Bool) : bs (rdisj S Tn) = disj4 (bs S) (bs Tn) := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    by_cases tt : Tn true <;> by_cases tf : Tn false <;>
      simp_all [bs, propBool, rdisj, disj4, mk, tr, fa]

theorem relational_plurivalent_classical_is_fde (Vn : α → PSet Bool) (A : Fm α) :
    mvEval neg4 conj4 disj4 (fun a => bs (Vn a)) A = bs (reval Vn A) := by
  induction A with
  | atom _ => rfl
  | neg A ih => rw [mvEval, reval, ih, bs_rneg]
  | conj A C ihA ihC => rw [mvEval, reval, ihA, ihC, bs_rconj]
  | disj A C ihA ihC => rw [mvEval, reval, ihA, ihC, bs_rdisj]

theorem true_mem_iff_bs_designated (S : PSet Bool) :
    S true ↔ tr (bs S) = true := by
  classical
  by_cases st : S true <;> by_cases sf : S false <;>
    simp_all [bs, propBool, tr, mk]

theorem relational_plurivalent_classical_sat (Vn : α → PSet Bool) (A : Fm α) :
    reval Vn A true ↔ mvFDE.sat (fun a => bs (Vn a)) A := by
  change reval Vn A true ↔
    tr (mvEval neg4 conj4 disj4 (fun a => bs (Vn a)) A) = true
  rw [true_mem_iff_bs_designated (reval Vn A),
    ← relational_plurivalent_classical_is_fde]

def V_gap : Atom → PSet Bool
  | p => psingleton false
  | _ => pempty

theorem image_vs_relational :
    peval Bool.not Bool.and Bool.or V_gap (conj (atom p) (atom q)) = pempty ∧
    reval V_gap (conj (atom p) (atom q)) = psingleton false := by
  constructor <;>
    apply pset_ext <;> intro b <;> cases b <;>
    simp [peval, reval, V_gap, pimage₂, pempty, psingleton, rconj]

theorem bool_set_eq_iff (S Tn : PSet Bool) :
    S = Tn ↔ (S true ↔ Tn true) ∧ (S false ↔ Tn false) := by
  constructor
  · intro h
    cases h
    exact ⟨Iff.rfl, Iff.rfl⟩
  · rintro ⟨ht, hf⟩
    apply pset_ext
    intro b
    cases b
    · exact hf
    · exact ht

theorem image_not_eq_rneg (S : PSet Bool) : pimage Bool.not S = rneg S := by
  apply pset_ext
  intro b
  cases b <;> simp [img_neg_T, img_neg_F, rneg]

theorem image_conj_eq_rconj (S Tn : PSet Bool)
    (hS : pnonempty S) (hT : pnonempty Tn) :
    pimage₂ Bool.and S Tn = rconj S Tn := by
  apply pset_ext
  intro b
  cases b
  · simp only [img_conj_F, rconj]
    have hs := (pnonempty_bool_iff S).1 hS
    have ht := (pnonempty_bool_iff Tn).1 hT
    grind
  · simp [img_conj_T, rconj]

theorem image_disj_eq_rdisj (S Tn : PSet Bool)
    (hS : pnonempty S) (hT : pnonempty Tn) :
    pimage₂ Bool.or S Tn = rdisj S Tn := by
  apply pset_ext
  intro b
  cases b
  · simp [img_disj_F, rdisj]
  · simp only [img_disj_T, rdisj]
    have hs := (pnonempty_bool_iff S).1 hS
    have ht := (pnonempty_bool_iff Tn).1 hT
    grind

theorem nonempty_agree (Vn : α → PSet Bool) (A : Fm α)
    (hV : ∀ a, pnonempty (Vn a)) :
    peval Bool.not Bool.and Bool.or Vn A = reval Vn A := by
  induction A with
  | atom _ => rfl
  | neg A ih => rw [peval, reval, ih, image_not_eq_rneg]
  | conj A C ihA ihC =>
      have neA : pnonempty (reval Vn A) := by
        rw [← ihA]
        exact peval_nonempty Bool.not Bool.and Bool.or Vn A hV
      have neC : pnonempty (reval Vn C) := by
        rw [← ihC]
        exact peval_nonempty Bool.not Bool.and Bool.or Vn C hV
      rw [peval, reval, ihA, ihC]
      exact image_conj_eq_rconj _ _ neA neC
  | disj A C ihA ihC =>
      have neA : pnonempty (reval Vn A) := by
        rw [← ihA]
        exact peval_nonempty Bool.not Bool.and Bool.or Vn A hV
      have neC : pnonempty (reval Vn C) := by
        rw [← ihC]
        exact peval_nonempty Bool.not Bool.and Bool.or Vn C hV
      rw [peval, reval, ihA, ihC]
      exact image_disj_eq_rdisj _ _ neA neC

theorem nonempty_agree_mem (Vn : α → PSet Bool) (A : Fm α)
    (hV : ∀ a, pnonempty (Vn a)) :
    pnonempty (peval Bool.not Bool.and Bool.or Vn A) ∧
      (peval Bool.not Bool.and Bool.or Vn A true ↔ reval Vn A true) ∧
      (peval Bool.not Bool.and Bool.or Vn A false ↔ reval Vn A false) := by
  have hEq := nonempty_agree Vn A hV
  constructor
  · exact peval_nonempty Bool.not Bool.and Bool.or Vn A hV
  · rw [hEq]
    exact ⟨Iff.rfl, Iff.rfl⟩

end BuddhistComparativeLogic
