/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Plurivalent

/-!
# Universal designation over the classical base

Lean counterpart of `isabelle/Core/UniversalDesignation.thy`.  General plurivalent
designation is universal: a formula is designated when every value it has is
designated, including the empty value set vacuously.  The resulting classical
logic is represented by the `T/E`-designated FDE5 matrix and characterized by
K3 consequence after discarding premises with variables absent from the
conclusion.
-/

namespace BuddhistComparativeLogic

open Fm TV4 TV5 Atom

/-! ## Atoms and congruence -/

def atoms : Fm α → PSet α
  | .atom a => psingleton a
  | .neg A => atoms A
  | .conj A C => fun a => atoms A a ∨ atoms C a
  | .disj A C => fun a => atoms A a ∨ atoms C a

theorem mv_eval_cong (neg : V → V) (mconj mdisj : V → V → V)
    (v w : α → V) (A : Fm α)
    (h : ∀ a, atoms A a → v a = w a) :
    mvEval neg mconj mdisj v A = mvEval neg mconj mdisj w A := by
  induction A with
  | atom a => exact h a rfl
  | neg A ih =>
      rw [mvEval, mvEval, ih (fun a ha => h a ha)]
  | conj A C ihA ihC =>
      rw [mvEval, mvEval,
        ihA (fun a ha => h a (Or.inl ha)),
        ihC (fun a ha => h a (Or.inr ha))]
  | disj A C ihA ihC =>
      rw [mvEval, mvEval,
        ihA (fun a ha => h a (Or.inl ha)),
        ihC (fun a ha => h a (Or.inr ha))]

/-! ## Universal designation -/

def upsat (L : MVLogic V) (Vn : α → PSet V) (A : Fm α) : Prop :=
  psubset (peval L.neg L.mconj L.mdisj Vn A) L.designated

def upentails (L : MVLogic V) (Γ : MVLogic.Theory α) (A : Fm α) : Prop :=
  ∀ Vn, (∀ B, Γ B → upsat L Vn B) → upsat L Vn A

theorem upsat_empty (L : MVLogic V) (Vn : α → PSet V) (A : Fm α)
    (h : peval L.neg L.mconj L.mdisj Vn A = pempty) : upsat L Vn A := by
  rw [upsat, h]
  intro x hx
  exact False.elim hx

theorem upentails_refl (L : MVLogic V) (A : Fm α) :
    upentails L (fun B => B = A) A := by
  intro Vn h
  exact h A rfl

/-! ## Priest's examples -/

def V_glut_gap : Atom → PSet Bool
  | p => fun _ => True
  | _ => pempty

def V_priest : Atom → PSet Bool
  | q => psingleton false
  | _ => pempty

def singletonTheory (A : Fm α) : MVLogic.Theory α := fun B => B = A
def pairTheory (A C : Fm α) : MVLogic.Theory α := fun B => B = A ∨ B = C
def emptyTheory : MVLogic.Theory α := fun _ => False

theorem cl_up_conj_elim_fails :
    ¬ upentails mvClassical (singletonTheory (conj (atom p) (atom q))) (atom p) := by
  intro h
  have hprem : upsat mvClassical V_glut_gap (conj (atom p) (atom q)) := by
    intro z hz
    rcases hz with ⟨x, y, hx, hy, _⟩
    exact False.elim hy
  have hout := h V_glut_gap (fun B hB => by cases hB; exact hprem)
  have hfalse := hout false (by trivial)
  exact Bool.noConfusion hfalse

theorem priest_witness_is_not_a_countermodel :
    upsat mvClassical V_priest (conj (atom p) (atom q)) ∧
    upsat mvClassical V_priest (atom p) := by
  constructor
  · intro z hz
    rcases hz with ⟨x, y, hx, _, _⟩
    exact False.elim hx
  · intro _ hx
    exact False.elim hx

theorem cl_up_disj_intro :
    upentails mvClassical (singletonTheory (atom p)) (disj (atom p) (atom q)) := by
  intro Vn hprem z hz
  rcases hz with ⟨x, y, hx, _, hxy⟩
  have hxD := hprem (atom p) rfl x hx
  cases x <;> cases y <;> simp_all [mvClassical]

theorem cl_up_explosion_fails :
    ¬ upentails mvClassical (pairTheory (atom p) (neg (atom p))) (atom q) := by
  intro h
  have hp : upsat mvClassical V_priest (atom p) := by
    intro _ hx
    exact False.elim hx
  have hnp : upsat mvClassical V_priest (neg (atom p)) := by
    intro _ hx
    rcases hx with ⟨_, hpv, _⟩
    exact False.elim hpv
  have hout := h V_priest (fun B hB => by
    cases hB with
    | inl hB => cases hB; exact hp
    | inr hB => cases hB; exact hnp)
  have hfalse := hout false (by rfl)
  exact Bool.noConfusion hfalse

def implication (A C : Fm α) : Fm α := disj (neg A) C

theorem cl_up_mp_fails :
    ¬ upentails mvClassical
      (pairTheory (atom p) (implication (atom p) (atom q))) (atom q) := by
  intro h
  have hp : upsat mvClassical V_priest (atom p) := by
    intro _ hx
    exact False.elim hx
  have himp : upsat mvClassical V_priest (implication (atom p) (atom q)) := by
    intro z hz
    rcases hz with ⟨x, y, hx, _, _⟩
    rcases hx with ⟨_, hpv, _⟩
    exact False.elim hpv
  have hout := h V_priest (fun B hB => by
    cases hB with
    | inl hB => cases hB; exact hp
    | inr hB => cases hB; exact himp)
  have hfalse := hout false (by rfl)
  exact Bool.noConfusion hfalse

theorem cl_up_lem_fails :
    ¬ upentails mvClassical emptyTheory (disj (atom p) (neg (atom p))) := by
  intro h
  have hout := h V_glut_gap (fun _ hFalse => False.elim hFalse)
  have hbad : peval Bool.not Bool.and Bool.or V_glut_gap
      (disj (atom p) (neg (atom p))) false := by
    exact ⟨false, false, trivial, ⟨true, trivial, rfl⟩, rfl⟩
  have hfalse := hout false hbad
  exact Bool.noConfusion hfalse

/-! ## The finite matrix -/

theorem subset_True_iff (S : PSet Bool) :
    psubset S (fun b => b = true) ↔ ¬ S false := by
  constructor
  · intro h hf
    exact Bool.noConfusion (h false hf)
  · intro hf b hb
    cases b
    · exact False.elim (hf hb)
    · rfl

def udDesignated : TV5 → Prop
  | .fin T => True
  | .E => True
  | _ => False

theorem FinTE_not_UNIV : ¬ ∀ x : TV5, udDesignated x := by
  intro h
  exact h (.fin N)

def mvUD : MVLogic TV5 where
  designated := udDesignated
  neg := neg5
  mconj := conj5
  mdisj := disj5
  designated_nonempty := ⟨.E, trivial⟩
  designated_proper := ⟨.fin N, by simp [udDesignated]⟩

theorem subset_True_iff_bs5 (S : PSet Bool) :
    psubset S (fun b => b = true) ↔ udDesignated (bs5 S) := by
  classical
  rw [subset_True_iff]
  by_cases st : S true <;> by_cases sf : S false <;>
    simp_all [bs5, bs, propBool, pnonempty_bool_iff, udDesignated, mk]

theorem cl_upsat_matrix (Vn : α → PSet Bool) (A : Fm α) :
    upsat mvClassical Vn A ↔ mvUD.sat (fun a => bs5 (Vn a)) A := by
  change psubset (peval Bool.not Bool.and Bool.or Vn A)
      (fun b => b = true) ↔
    udDesignated (mvEval neg5 conj5 disj5 (fun a => bs5 (Vn a)) A)
  rw [subset_True_iff_bs5, image_plurivalent_classical_is_fde5]

def nfree (v : α → TV5) : Prop := ∀ a, v a ≠ .fin N

def sb5 : TV5 → PSet Bool
  | .fin T => psingleton true
  | .fin F => psingleton false
  | .fin B => fun _ => True
  | .fin N => pempty
  | .E => pempty

theorem bs5_sb5 (x : TV5) (h : x ≠ .fin N) : bs5 (sb5 x) = x := by
  classical
  cases x with
  | fin y => cases y <;> simp_all [sb5, bs5, bs, propBool,
      pnonempty_bool_iff, psingleton, mk]
  | E => simp [sb5, bs5, propBool, pnonempty_bool_iff, pempty]

def udNFreeEntails (Γ : MVLogic.Theory α) (A : Fm α) : Prop :=
  ∀ v, nfree v → (∀ B, Γ B → mvUD.sat v B) → mvUD.sat v A

theorem cl_upentails_matrix (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails mvClassical Γ A ↔ udNFreeEntails Γ A := by
  constructor
  · intro h v hnf hprem
    have hv : (fun a => bs5 (sb5 (v a))) = v := by
      funext a
      exact bs5_sb5 (v a) (hnf a)
    have hprem' : ∀ B, Γ B → upsat mvClassical (fun a => sb5 (v a)) B := by
      intro B hB
      apply (cl_upsat_matrix _ _).2
      rw [hv]
      exact hprem B hB
    have hout := h (fun a => sb5 (v a)) hprem'
    have := (cl_upsat_matrix _ _).1 hout
    rwa [hv] at this
  · intro h Vn hprem
    have hnf : nfree (fun a => bs5 (Vn a)) := by
      intro a
      exact image_plurivalent_classical_has_no_gap (Vn a)
    have hprem' : ∀ B, Γ B → mvUD.sat (fun a => bs5 (Vn a)) B := by
      intro B hB
      exact (cl_upsat_matrix _ _).1 (hprem B hB)
    exact (cl_upsat_matrix _ _).2 (h _ hnf hprem')

/-! ## Variable inclusion and K3 -/

def restrictToAtoms (Γ : MVLogic.Theory α) (A : Fm α) : MVLogic.Theory α :=
  fun B => Γ B ∧ psubset (atoms B) (atoms A)

def k3_entails (Γ : MVLogic.Theory α) (A : Fm α) : Prop :=
  ∀ w : α → TV4, (∀ a, w a ≠ N) →
    (∀ B, Γ B → mvEval neg4 conj4 disj4 w B = T) →
    mvEval neg4 conj4 disj4 w A = T

def proj : TV5 → TV4
  | .fin x => x
  | .E => T

theorem eval5_infect_at (v : α → TV5) (A : Fm α) {a : α}
    (ha : atoms A a) (hv : v a = E) :
    mvEval neg5 conj5 disj5 v A = E := by
  induction A with
  | atom b =>
      change a = b at ha
      cases ha
      exact hv
  | neg A ih =>
      rw [mvEval, ih ha, neg5]
  | conj A C ihA ihC =>
      cases ha with
      | inl ha =>
          rw [mvEval, ihA ha]
          exact conj5_E_left _
      | inr ha => rw [mvEval, ihC ha, conj5_E_right]
  | disj A C ihA ihC =>
      cases ha with
      | inl ha =>
          rw [mvEval, ihA ha]
          exact disj5_E_left _
      | inr ha => rw [mvEval, ihC ha, disj5_E_right]

theorem eval5_infect (v : α → TV5) (A : Fm α)
    (h : ∃ a, atoms A a ∧ v a = E) :
    mvEval neg5 conj5 disj5 v A = E := by
  rcases h with ⟨a, ha, hv⟩
  exact eval5_infect_at v A ha hv

theorem eval5_clean (v : α → TV5) (A : Fm α)
    (h : ∀ a, atoms A a → v a ≠ E) :
    mvEval neg5 conj5 disj5 v A =
      .fin (mvEval neg4 conj4 disj4 (fun a => proj (v a)) A) := by
  induction A with
  | atom a =>
      cases hv : v a with
      | fin x => simp [mvEval, hv, proj]
      | E => exact False.elim (h a rfl hv)
  | neg A ih =>
      rw [mvEval, mvEval, ih (fun a ha => h a ha), neg5]
  | conj A C ihA ihC =>
      rw [mvEval, mvEval,
        ihA (fun a ha => h a (Or.inl ha)),
        ihC (fun a ha => h a (Or.inr ha)), conj5]
  | disj A C ihA ihC =>
      rw [mvEval, mvEval,
        ihA (fun a ha => h a (Or.inl ha)),
        ihC (fun a ha => h a (Or.inr ha)), disj5]

theorem ud_sat_Fin (v : α → TV5) (A : Fm α) (x : TV4)
    (hs : mvUD.sat v A)
    (he : mvEval neg5 conj5 disj5 v A = .fin x) : x = T := by
  change udDesignated (mvEval neg5 conj5 disj5 v A) at hs
  rw [he] at hs
  cases x <;> simp_all [udDesignated]

theorem ud_variable_inclusion (Γ : MVLogic.Theory α) (A : Fm α) :
    udNFreeEntails Γ A ↔ k3_entails (restrictToAtoms Γ A) A := by
  classical
  constructor
  · intro h w hw hprem
    let v : α → TV5 := fun a => if atoms A a then .fin (w a) else .E
    have hnf : nfree v := by
      intro a
      by_cases ha : atoms A a <;> simp [v, ha, hw a]
    have hAgree (C : Fm α) (hsub : psubset (atoms C) (atoms A)) :
        mvEval neg4 conj4 disj4 (fun a => proj (v a)) C =
          mvEval neg4 conj4 disj4 w C := by
      apply mv_eval_cong
      intro a ha
      simp [v, hsub a ha, proj]
    have hpremUD : ∀ C, Γ C → mvUD.sat v C := by
      intro C hC
      by_cases hsub : psubset (atoms C) (atoms A)
      · have hclean : ∀ a, atoms C a → v a ≠ E := by
          intro a ha
          simp [v, hsub a ha]
        have he := eval5_clean v C hclean
        rw [hAgree C hsub] at he
        have hk := hprem C ⟨hC, hsub⟩
        change udDesignated (mvEval neg5 conj5 disj5 v C)
        rw [he, hk]
        trivial
      · have hex : ∃ a, atoms C a ∧ ¬ atoms A a := by
          apply Classical.byContradiction
          intro hn
          apply hsub
          intro a ha
          apply Classical.byContradiction
          intro hna
          exact hn ⟨a, ha, hna⟩
        have he : mvEval neg5 conj5 disj5 v C = E := by
          apply eval5_infect
          rcases hex with ⟨a, ha, hna⟩
          exact ⟨a, ha, by simp [v, hna]⟩
        change udDesignated (mvEval neg5 conj5 disj5 v C)
        simp [he, udDesignated]
    have hout := h v hnf hpremUD
    have hcleanA : ∀ a, atoms A a → v a ≠ E := by
      intro a ha
      simp [v, ha]
    have he := eval5_clean v A hcleanA
    rw [hAgree A (fun _ h => h)] at he
    exact ud_sat_Fin v A _ hout he
  · intro h v hnf hprem
    by_cases hinfect : ∃ a, atoms A a ∧ v a = E
    · have he := eval5_infect v A hinfect
      change udDesignated (mvEval neg5 conj5 disj5 v A)
      rw [he]
      trivial
    · let w : α → TV4 := fun a => proj (v a)
      have hw : ∀ a, w a ≠ N := by
        intro a
        have hn := hnf a
        cases hv : v a with
        | fin x =>
            cases x <;> simp_all [w, proj]
        | E =>
            change proj (v a) ≠ N
            rw [hv]
            decide
      have hpremK3 : ∀ C, restrictToAtoms Γ A C →
          mvEval neg4 conj4 disj4 w C = T := by
        intro C hC
        have hclean : ∀ a, atoms C a → v a ≠ E := by
          intro a ha hv
          exact hinfect ⟨a, hC.2 a ha, hv⟩
        have he := eval5_clean v C hclean
        change mvEval neg5 conj5 disj5 v C =
          .fin (mvEval neg4 conj4 disj4 w C) at he
        exact ud_sat_Fin v C _ (hprem C hC.1) he
      have hk := h w hw hpremK3
      have hcleanA : ∀ a, atoms A a → v a ≠ E := by
        intro a ha hv
        exact hinfect ⟨a, ha, hv⟩
      have he := eval5_clean v A hcleanA
      change mvEval neg5 conj5 disj5 v A =
        .fin (mvEval neg4 conj4 disj4 w A) at he
      change udDesignated (mvEval neg5 conj5 disj5 v A)
      rw [he, hk]
      trivial

theorem priest_open_question_classical (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails mvClassical Γ A ↔ k3_entails (restrictToAtoms Γ A) A := by
  rw [cl_upentails_matrix, ud_variable_inclusion]

theorem k3_tables :
    neg4 B = B ∧ conj4 T B = B ∧ conj4 B T = B ∧ conj4 B B = B ∧
    conj4 B F = F ∧ conj4 F B = F ∧ disj4 T B = T ∧ disj4 B T = T ∧
    disj4 B B = B ∧ disj4 B F = B ∧ disj4 F B = B := by
  decide

theorem conj_elim_explained : ¬ k3_entails emptyTheory (atom p) := by
  intro h
  have := h (fun _ => F) (by intro _; decide)
    (fun _ hFalse => False.elim hFalse)
  exact TV4.noConfusion this

theorem disj_intro_explained :
    k3_entails (singletonTheory (atom p)) (disj (atom p) (atom q)) := by
  intro w hw hprem
  have hp := hprem (atom p) rfl
  cases hq : w q <;> simp_all [mvEval, disj4, mk, tr, fa]

end BuddhistComparativeLogic
