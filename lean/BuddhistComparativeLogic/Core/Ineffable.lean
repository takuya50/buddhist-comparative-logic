/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.UniversalDesignationMore

/-!
# An absorbing ineffable value over an arbitrary many-valued base

This module adjoins one undesignated, operation-absorbing value to any
`MVLogic`.  It proves two exact boundary theorems.

* For ordinary single-premise consequence, the extension is the base logic
  plus atom containment, except when the premise has no base model.
* For positive universal plurivalent consequence, the extension is the base
  positive consequence plus collective atom coverage, except when the base
  premises have no positive universal model.

The second result fills the universal-designation gap left by the original
FDE5 argument: it applies uniformly to the classical, K3, LP, and FDE bases.
-/

namespace BuddhistComparativeLogic

open Fm

/-- A base value, or a single absorbing ineffable value. -/
inductive WithIneff (V : Type u) where
  | val (x : V)
  | ineff
  deriving DecidableEq, Repr

namespace WithIneff

def neg (L : MVLogic V) : WithIneff V → WithIneff V
  | .val x => .val (L.neg x)
  | .ineff => .ineff

def conj (L : MVLogic V) : WithIneff V → WithIneff V → WithIneff V
  | .val x, .val y => .val (L.mconj x y)
  | _, _ => .ineff

def disj (L : MVLogic V) : WithIneff V → WithIneff V → WithIneff V
  | .val x, .val y => .val (L.mdisj x y)
  | _, _ => .ineff

/-- The absorbing value is deliberately undesignated. -/
def logic (L : MVLogic V) : MVLogic (WithIneff V) where
  designated
    | .val x => L.designated x
    | .ineff => False
  neg := neg L
  mconj := conj L
  mdisj := disj L
  designated_nonempty := by
    obtain ⟨x, hx⟩ := L.designated_nonempty
    exact ⟨.val x, hx⟩
  designated_proper := ⟨.ineff, by simp⟩

instance : Inhabited (WithIneff V) := ⟨.ineff⟩

/-- Remove the ineffable alternative from a predicate set. -/
def baseSet (S : PSet (WithIneff V)) : PSet V :=
  fun x => S (.val x)

/-- Embed a predicate set without adding the ineffable alternative. -/
def liftSet (S : PSet V) : PSet (WithIneff V)
  | .val x => S x
  | .ineff => False

/-- Add the ineffable alternative at exactly one atom. -/
def injectAt (Vn : α → PSet V) (a : α) : α → PSet (WithIneff V) :=
  fun b z => match z with
    | .val x => Vn b x
    | .ineff => b = a

/-- Replace an ineffable alternative by a chosen base value. -/
def eraseSet (d : V) (S : PSet (WithIneff V)) : PSet V :=
  fun x => S (.val x) ∨ (S .ineff ∧ x = d)

@[simp] theorem baseSet_liftSet (S : PSet V) : baseSet (liftSet S) = S := by
  rfl

@[simp] theorem baseSet_injectAt (Vn : α → PSet V) (a b : α) :
    baseSet (injectAt Vn a b) = Vn b := by
  rfl

theorem liftSet_nonempty {S : PSet V} (hS : pnonempty S) :
    pnonempty (liftSet S) := by
  obtain ⟨x, hx⟩ := hS
  exact ⟨.val x, hx⟩

theorem injectAt_nonempty (Vn : α → PSet V) (a : α)
    (hV : ∀ b, pnonempty (Vn b)) :
    ∀ b, pnonempty (injectAt Vn a b) := by
  intro b
  obtain ⟨x, hx⟩ := hV b
  exact ⟨.val x, hx⟩

theorem eraseSet_nonempty (d : V) {S : PSet (WithIneff V)}
    (hS : pnonempty S) : pnonempty (eraseSet d S) := by
  obtain ⟨z, hz⟩ := hS
  cases z with
  | val x => exact ⟨x, Or.inl hz⟩
  | ineff => exact ⟨d, Or.inr ⟨hz, rfl⟩⟩

theorem eraseSet_eq_baseSet_of_clean (d : V) (S : PSet (WithIneff V))
    (hclean : ¬ S .ineff) : eraseSet d S = baseSet S := by
  apply pset_ext
  intro x
  simp [eraseSet, baseSet, hclean]

/-! ## Evaluation lemmas -/

theorem eval_embedded (L : MVLogic V) (w : α → V) (A : Fm α) :
    mvEval (neg L) (conj L) (disj L) (fun a => .val (w a)) A =
      .val (mvEval L.neg L.mconj L.mdisj w A) := by
  induction A with
  | atom _ => rfl
  | neg A ih => simp [mvEval, neg, ih]
  | conj A C ihA ihC => simp [mvEval, conj, ihA, ihC]
  | disj A C ihA ihC => simp [mvEval, disj, ihA, ihC]

theorem eval_ineff_of_atom (L : MVLogic V) (v : α → WithIneff V)
    (A : Fm α) {a : α} (ha : atoms A a) (hv : v a = .ineff) :
    mvEval (neg L) (conj L) (disj L) v A = .ineff := by
  induction A with
  | atom b =>
      change a = b at ha
      cases ha
      exact hv
  | neg A ih => simp [mvEval, neg, ih ha]
  | conj A C ihA ihC =>
      cases ha with
      | inl ha => simp [mvEval, conj, ihA ha]
      | inr ha =>
          have hC := ihC ha
          cases hA : mvEval (neg L) (conj L) (disj L) v A <;>
            simp [mvEval, conj, hA, hC]
  | disj A C ihA ihC =>
      cases ha with
      | inl ha => simp [mvEval, disj, ihA ha]
      | inr ha =>
          have hC := ihC ha
          cases hA : mvEval (neg L) (conj L) (disj L) v A <;>
            simp [mvEval, disj, hA, hC]

def project (d : V) : WithIneff V → V
  | .val x => x
  | .ineff => d

theorem eval_clean (L : MVLogic V) (d : V) (v : α → WithIneff V)
    (A : Fm α) (hclean : ∀ a, atoms A a → v a ≠ .ineff) :
    mvEval (neg L) (conj L) (disj L) v A =
      .val (mvEval L.neg L.mconj L.mdisj (fun a => project d (v a)) A) := by
  induction A with
  | atom a =>
      cases hv : v a with
      | val x => simp [mvEval, project, hv]
      | ineff => exact False.elim (hclean a rfl hv)
  | neg A ih =>
      rw [mvEval, mvEval, ih (fun a ha => hclean a ha)]
      rfl
  | conj A C ihA ihC =>
      rw [mvEval, mvEval,
        ihA (fun a ha => hclean a (Or.inl ha)),
        ihC (fun a ha => hclean a (Or.inr ha))]
      rfl
  | disj A C ihA ihC =>
      rw [mvEval, mvEval,
        ihA (fun a ha => hclean a (Or.inl ha)),
        ihC (fun a ha => hclean a (Or.inr ha))]
      rfl

theorem peval_val_iff (L : MVLogic V) (Vn : α → PSet (WithIneff V))
    (A : Fm α) (x : V) :
    peval (neg L) (conj L) (disj L) Vn A (.val x) ↔
      peval L.neg L.mconj L.mdisj (fun a => baseSet (Vn a)) A x := by
  induction A generalizing x with
  | atom _ => rfl
  | neg A ih =>
      constructor
      · rintro ⟨z, hz, heq⟩
        cases z with
        | val y =>
            have hxy : x = L.neg y := WithIneff.val.inj heq
            exact ⟨y, (ih y).1 hz, hxy⟩
        | ineff => simp [neg] at heq
      · rintro ⟨y, hy, hxy⟩
        exact ⟨.val y, (ih y).2 hy, congrArg val hxy⟩
  | conj A C ihA ihC =>
      constructor
      · rintro ⟨z, w, hz, hw, heq⟩
        cases z with
        | ineff => simp [conj] at heq
        | val y =>
          cases w with
          | ineff => simp [conj] at heq
          | val z =>
            have hx : x = L.mconj y z := WithIneff.val.inj heq
            exact ⟨y, z, (ihA y).1 hz, (ihC z).1 hw, hx⟩
      · rintro ⟨y, z, hy, hz, hx⟩
        exact ⟨.val y, val z, (ihA y).2 hy, (ihC z).2 hz, congrArg val hx⟩
  | disj A C ihA ihC =>
      constructor
      · rintro ⟨z, w, hz, hw, heq⟩
        cases z with
        | ineff => simp [disj] at heq
        | val y =>
          cases w with
          | ineff => simp [disj] at heq
          | val z =>
            have hx : x = L.mdisj y z := WithIneff.val.inj heq
            exact ⟨y, z, (ihA y).1 hz, (ihC z).1 hw, hx⟩
      · rintro ⟨y, z, hy, hz, hx⟩
        exact ⟨val y, val z, (ihA y).2 hy, (ihC z).2 hz, congrArg val hx⟩

theorem peval_ineff_origin (L : MVLogic V)
    (Vn : α → PSet (WithIneff V)) (A : Fm α)
    (h : peval (neg L) (conj L) (disj L) Vn A .ineff) :
    ∃ a, atoms A a ∧ Vn a .ineff := by
  induction A with
  | atom a => exact ⟨a, rfl, h⟩
  | neg A ih =>
      rcases h with ⟨z, hz, heq⟩
      cases z with
      | val _ => simp [neg] at heq
      | ineff => exact ih hz
  | conj A C ihA ihC =>
      rcases h with ⟨z, w, hz, hw, heq⟩
      cases z with
      | ineff =>
          obtain ⟨a, ha, hVa⟩ := ihA hz
          exact ⟨a, Or.inl ha, hVa⟩
      | val _ =>
          cases w with
          | ineff =>
              obtain ⟨a, ha, hVa⟩ := ihC hw
              exact ⟨a, Or.inr ha, hVa⟩
          | val _ => simp [conj] at heq
  | disj A C ihA ihC =>
      rcases h with ⟨z, w, hz, hw, heq⟩
      cases z with
      | ineff =>
          obtain ⟨a, ha, hVa⟩ := ihA hz
          exact ⟨a, Or.inl ha, hVa⟩
      | val _ =>
          cases w with
          | ineff =>
              obtain ⟨a, ha, hVa⟩ := ihC hw
              exact ⟨a, Or.inr ha, hVa⟩
          | val _ => simp [disj] at heq

theorem peval_ineff_of_atom (L : MVLogic V)
    (Vn : α → PSet (WithIneff V)) (A : Fm α)
    (hpos : ∀ a, pnonempty (Vn a)) {a : α}
    (ha : atoms A a) (hVa : Vn a .ineff) :
    peval (neg L) (conj L) (disj L) Vn A .ineff := by
  induction A with
  | atom b =>
      change a = b at ha
      cases ha
      exact hVa
  | neg A ih => exact ⟨.ineff, ih ha, rfl⟩
  | conj A C ihA ihC =>
      cases ha with
      | inl ha =>
          obtain ⟨z, hz⟩ := peval_nonempty (neg L) (conj L) (disj L) Vn C hpos
          exact ⟨.ineff, z, ihA ha, hz, rfl⟩
      | inr ha =>
          obtain ⟨z, hz⟩ := peval_nonempty (neg L) (conj L) (disj L) Vn A hpos
          cases z with
          | val x => exact ⟨.val x, .ineff, hz, ihC ha, rfl⟩
          | ineff => exact ⟨.ineff, .ineff, hz, ihC ha, rfl⟩
  | disj A C ihA ihC =>
      cases ha with
      | inl ha =>
          obtain ⟨z, hz⟩ := peval_nonempty (neg L) (conj L) (disj L) Vn C hpos
          exact ⟨.ineff, z, ihA ha, hz, rfl⟩
      | inr ha =>
          obtain ⟨z, hz⟩ := peval_nonempty (neg L) (conj L) (disj L) Vn A hpos
          cases z with
          | val x => exact ⟨.val x, .ineff, hz, ihC ha, rfl⟩
          | ineff => exact ⟨.ineff, .ineff, hz, ihC ha, rfl⟩

/-! ## Satisfaction transfers -/

theorem upsat_implies_base (L : MVLogic V)
    (Vn : α → PSet (WithIneff V)) (A : Fm α)
    (h : upsat (logic L) Vn A) :
    upsat L (fun a => baseSet (Vn a)) A := by
  intro x hx
  exact h (.val x) ((peval_val_iff L Vn A x).2 hx)

theorem upsat_atoms_clean (L : MVLogic V)
    (Vn : α → PSet (WithIneff V)) (A : Fm α)
    (hpos : ∀ a, pnonempty (Vn a)) (h : upsat (logic L) Vn A)
    {a : α} (ha : atoms A a) : ¬ Vn a .ineff := by
  intro hVa
  have hi := peval_ineff_of_atom L Vn A hpos ha hVa
  exact h .ineff hi

theorem upsat_of_base (L : MVLogic V)
    (Vn : α → PSet (WithIneff V)) (A : Fm α)
    (hclean : ∀ a, atoms A a → ¬ Vn a .ineff)
    (h : upsat L (fun a => baseSet (Vn a)) A) :
    upsat (logic L) Vn A := by
  intro z hz
  cases z with
  | val x => exact h x ((peval_val_iff L Vn A x).1 hz)
  | ineff =>
      obtain ⟨a, ha, hVa⟩ := peval_ineff_origin L Vn A hz
      exact False.elim (hclean a ha hVa)

theorem lift_upsat_iff (L : MVLogic V) (Vn : α → PSet V) (A : Fm α) :
    upsat (logic L) (fun a => liftSet (Vn a)) A ↔ upsat L Vn A := by
  constructor
  · exact upsat_implies_base L _ A
  · intro h
    apply upsat_of_base L _ A
    · intro a _
      simp [liftSet]
    · exact h

/-! ## Ordinary consequence: base plus containment -/

theorem entails_singleton_iff (L : MVLogic V) (X Y : Fm α) :
    (logic L).entails (singletonTheory X) Y ↔
      L.entails (singletonTheory X) Y ∧
        (psubset (atoms Y) (atoms X) ∨ ∀ w, ¬ L.sat w X) := by
  classical
  obtain ⟨d, _hd⟩ := L.designated_nonempty
  constructor
  · intro h
    constructor
    · intro w hw
      have hX : (logic L).sat (fun a => .val (w a)) X := by
        change (logic L).designated
          (mvEval (neg L) (conj L) (disj L) (fun a => .val (w a)) X)
        rw [eval_embedded]
        exact hw X rfl
      have hY := h (fun a => .val (w a)) (fun B hB => by cases hB; exact hX)
      change (logic L).designated
        (mvEval (neg L) (conj L) (disj L) (fun a => .val (w a)) Y) at hY
      rw [eval_embedded] at hY
      exact hY
    · by_cases hcont : psubset (atoms Y) (atoms X)
      · exact Or.inl hcont
      · right
        intro w hw
        have hex : ∃ a, atoms Y a ∧ ¬ atoms X a := by
          apply Classical.byContradiction
          intro hn
          apply hcont
          intro a ha
          apply Classical.byContradiction
          intro hna
          exact hn ⟨a, ha, hna⟩
        obtain ⟨a, haY, haX⟩ := hex
        let v : α → WithIneff V := fun b =>
          if b = a then .ineff else .val (w b)
        have hcleanX : ∀ b, atoms X b → v b ≠ .ineff := by
          intro b hb
          have hba : b ≠ a := by
            intro hEq
            subst b
            exact haX hb
          simp [v, hba]
        have heX := eval_clean L d v X hcleanX
        have hagree :
            mvEval L.neg L.mconj L.mdisj (fun b => project d (v b)) X =
              mvEval L.neg L.mconj L.mdisj w X := by
          apply mv_eval_cong
          intro b hb
          have hba : b ≠ a := by
            intro hEq
            subst b
            exact haX hb
          simp [v, hba, project]
        have hsatX : (logic L).sat v X := by
          change (logic L).designated
            (mvEval (neg L) (conj L) (disj L) v X)
          rw [heX, hagree]
          exact hw
        have hsatY := h v (fun B hB => by cases hB; exact hsatX)
        have heY : mvEval (neg L) (conj L) (disj L) v Y = .ineff := by
          apply eval_ineff_of_atom L v Y haY
          simp [v]
        change (logic L).designated
          (mvEval (neg L) (conj L) (disj L) v Y) at hsatY
        rw [heY] at hsatY
        exact hsatY
  · rintro ⟨hbase, hboundary⟩ v hprem
    have hsatX := hprem X rfl
    have hcleanX : ∀ a, atoms X a → v a ≠ .ineff := by
      intro a ha hv
      have he := eval_ineff_of_atom L v X ha hv
      change (logic L).designated
        (mvEval (neg L) (conj L) (disj L) v X) at hsatX
      rw [he] at hsatX
      exact hsatX
    have heX := eval_clean L d v X hcleanX
    have hbaseX : L.sat (fun a => project d (v a)) X := by
      change (logic L).designated
        (mvEval (neg L) (conj L) (disj L) v X) at hsatX
      rw [heX] at hsatX
      exact hsatX
    have hcont : psubset (atoms Y) (atoms X) := by
      cases hboundary with
      | inl h => exact h
      | inr h => exact False.elim (h _ hbaseX)
    have hcleanY : ∀ a, atoms Y a → v a ≠ .ineff := by
      intro a ha
      exact hcleanX a (hcont a ha)
    have heY := eval_clean L d v Y hcleanY
    change (logic L).designated
      (mvEval (neg L) (conj L) (disj L) v Y)
    rw [heY]
    exact hbase (fun a => project d (v a))
      (fun B hB => by cases hB; exact hbaseX)

/-! ## Universal designation: base plus collective atom coverage -/

/-- An atom is covered when it occurs in at least one premise. -/
def coveredBy (Γ : MVLogic.Theory α) (a : α) : Prop :=
  ∃ C, Γ C ∧ atoms C a

/-- The base premises have no positive universally designated model. -/
def PosUnsatisfiable (L : MVLogic V) (Γ : MVLogic.Theory α) : Prop :=
  ∀ Vn, (∀ a, pnonempty (Vn a)) →
    ¬ (∀ C, Γ C → upsat L Vn C)

theorem pos_upentails_iff (L : MVLogic V) (Γ : MVLogic.Theory α)
    (A : Fm α) :
    pos_upentails (logic L) Γ A ↔
      pos_upentails L Γ A ∧
        (psubset (atoms A) (coveredBy Γ) ∨ PosUnsatisfiable L Γ) := by
  classical
  obtain ⟨d, _hd⟩ := L.designated_nonempty
  constructor
  · intro h
    constructor
    · intro Vn hpos hprem
      have hposLift : ∀ a, pnonempty (liftSet (Vn a)) := by
        intro a
        exact liftSet_nonempty (hpos a)
      have hpremLift : ∀ C, Γ C →
          upsat (logic L) (fun a => liftSet (Vn a)) C := by
        intro C hC
        exact (lift_upsat_iff L Vn C).2 (hprem C hC)
      have hout := h (fun a => liftSet (Vn a)) hposLift hpremLift
      exact (lift_upsat_iff L Vn A).1 hout
    · by_cases hcover : psubset (atoms A) (coveredBy Γ)
      · exact Or.inl hcover
      · right
        intro Vn hpos hprem
        have hex : ∃ a, atoms A a ∧ ¬ coveredBy Γ a := by
          apply Classical.byContradiction
          intro hn
          apply hcover
          intro a ha
          apply Classical.byContradiction
          intro hna
          exact hn ⟨a, ha, hna⟩
        obtain ⟨a, haA, haCover⟩ := hex
        let Wn := injectAt Vn a
        have hposW : ∀ b, pnonempty (Wn b) := injectAt_nonempty Vn a hpos
        have hpremW : ∀ C, Γ C → upsat (logic L) Wn C := by
          intro C hC
          apply upsat_of_base L Wn C
          · intro b hb hbi
            change b = a at hbi
            subst b
            exact haCover ⟨C, hC, hb⟩
          · exact hprem C hC
        have hout := h Wn hposW hpremW
        have hi : peval (neg L) (conj L) (disj L) Wn A .ineff := by
          apply peval_ineff_of_atom L Wn A hposW haA
          rfl
        exact hout .ineff hi
  · rintro ⟨hbase, hboundary⟩ Wn hposW hpremW
    let Un : α → PSet V := fun a => eraseSet d (Wn a)
    have hposU : ∀ a, pnonempty (Un a) := by
      intro a
      exact eraseSet_nonempty d (hposW a)
    have hpremClean : ∀ C, Γ C →
        ∀ a, atoms C a → ¬ Wn a .ineff := by
      intro C hC a ha
      exact upsat_atoms_clean L Wn C hposW (hpremW C hC) ha
    have hpremU : ∀ C, Γ C → upsat L Un C := by
      intro C hC
      have hbaseC := upsat_implies_base L Wn C (hpremW C hC)
      change psubset (peval L.neg L.mconj L.mdisj Un C) L.designated
      have heval :
          peval L.neg L.mconj L.mdisj Un C =
            peval L.neg L.mconj L.mdisj (fun a => baseSet (Wn a)) C := by
        apply peval_cong
        intro a ha
        exact eraseSet_eq_baseSet_of_clean d (Wn a) (hpremClean C hC a ha)
      rw [heval]
      exact hbaseC
    cases hboundary with
    | inr hunsat => exact False.elim (hunsat Un hposU hpremU)
    | inl hcover =>
        have hcleanA : ∀ a, atoms A a → ¬ Wn a .ineff := by
          intro a ha
          obtain ⟨C, hC, haC⟩ := hcover a ha
          exact hpremClean C hC a haC
        have hbaseA := hbase Un hposU hpremU
        have hevalA :
            peval L.neg L.mconj L.mdisj Un A =
              peval L.neg L.mconj L.mdisj (fun a => baseSet (Wn a)) A := by
          apply peval_cong
          intro a ha
          exact eraseSet_eq_baseSet_of_clean d (Wn a) (hcleanA a ha)
        apply upsat_of_base L Wn A hcleanA
        change psubset
          (peval L.neg L.mconj L.mdisj (fun a => baseSet (Wn a)) A)
          L.designated
        rw [← hevalA]
        exact hbaseA

theorem upentails_iff (L : MVLogic V) (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails (logic L) Γ A ↔
      pos_upentails L (restrictToAtoms Γ A) A ∧
        (psubset (atoms A) (coveredBy (restrictToAtoms Γ A)) ∨
          PosUnsatisfiable L (restrictToAtoms Γ A)) := by
  rw [upentails_variable_inclusion, pos_upentails_iff]

/-! ## Concrete bases -/

theorem bs_ne_N_of_nonempty (S : PSet Bool) (hS : pnonempty S) :
    bs S ≠ TV4.N := by
  classical
  rw [pnonempty_bool_iff] at hS
  by_cases ht : S true <;> by_cases hf : S false <;>
    simp_all [bs, propBool, BuddhistComparativeLogic.mk]

theorem bs5_eq_fin_bs_of_nonempty (S : PSet Bool) (hS : pnonempty S) :
    bs5 S = .fin (bs S) := by
  classical
  have hb : propBool (pnonempty S) = true := (propBool_eq_true _).2 hS
  simp [bs5, hb]

/-- Positive universal designation over the Boolean base is exactly the
three-valued `T/B/F` consequence relation used in the classical analysis. -/
theorem pos_up_classical_is_k3 (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails mvClassical Γ A ↔ k3_entails Γ A := by
  constructor
  · intro h w hw hprem
    let Vn : α → PSet Bool := fun a => sb5 (.fin (w a))
    have hpos : ∀ a, pnonempty (Vn a) := by
      intro a
      cases hwa : w a with
      | T => exact ⟨true, by simp [Vn, sb5, psingleton, hwa]⟩
      | B => exact ⟨true, by simp [Vn, sb5, hwa]⟩
      | N => exact False.elim (hw a hwa)
      | F => exact ⟨false, by simp [Vn, sb5, psingleton, hwa]⟩
    have hv : (fun a => bs5 (Vn a)) = (fun a => .fin (w a)) := by
      funext a
      apply bs5_sb5
      intro heq
      exact hw a (TV5.fin.inj heq)
    have hpremUp : ∀ C, Γ C → upsat mvClassical Vn C := by
      intro C hC
      apply (cl_upsat_matrix Vn C).2
      rw [hv]
      have he := eval5_clean (fun a => .fin (w a)) C (by simp)
      change mvEval neg5 conj5 disj5 (fun a => .fin (w a)) C =
        .fin (mvEval neg4 conj4 disj4 w C) at he
      change udDesignated
        (mvEval neg5 conj5 disj5 (fun a => .fin (w a)) C)
      rw [he, hprem C hC]
      trivial
    have hout := h Vn hpos hpremUp
    have hud := (cl_upsat_matrix Vn A).1 hout
    rw [hv] at hud
    have he := eval5_clean (fun a => .fin (w a)) A (by simp)
    change mvEval neg5 conj5 disj5 (fun a => .fin (w a)) A =
      .fin (mvEval neg4 conj4 disj4 w A) at he
    exact ud_sat_Fin _ A _ hud he
  · intro h Vn hpos hprem
    let w : α → TV4 := fun a => bs (Vn a)
    have hw : ∀ a, w a ≠ TV4.N := by
      intro a
      exact bs_ne_N_of_nonempty (Vn a) (hpos a)
    have hv : (fun a => bs5 (Vn a)) = (fun a => .fin (w a)) := by
      funext a
      exact bs5_eq_fin_bs_of_nonempty (Vn a) (hpos a)
    have hpremK3 : ∀ C, Γ C →
        mvEval neg4 conj4 disj4 w C = TV4.T := by
      intro C hC
      have hud := (cl_upsat_matrix Vn C).1 (hprem C hC)
      rw [hv] at hud
      have he := eval5_clean (fun a => .fin (w a)) C (by simp)
      change mvEval neg5 conj5 disj5 (fun a => .fin (w a)) C =
        .fin (mvEval neg4 conj4 disj4 w C) at he
      exact ud_sat_Fin _ C _ hud he
    have hout := h w hw hpremK3
    apply (cl_upsat_matrix Vn A).2
    rw [hv]
    have he := eval5_clean (fun a => .fin (w a)) A (by simp)
    change mvEval neg5 conj5 disj5 (fun a => .fin (w a)) A =
      .fin (mvEval neg4 conj4 disj4 w A) at he
    change udDesignated
      (mvEval neg5 conj5 disj5 (fun a => .fin (w a)) A)
    rw [he, hout]
    trivial

theorem classical_pos_upentails_iff (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails (logic mvClassical) Γ A ↔
      k3_entails Γ A ∧
        (psubset (atoms A) (coveredBy Γ) ∨
          PosUnsatisfiable mvClassical Γ) := by
  rw [pos_upentails_iff, pos_up_classical_is_k3]

theorem k3_pos_upentails_iff (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails (logic K3.logic) Γ A ↔
      K3.logic.entails Γ A ∧
        (psubset (atoms A) (coveredBy Γ) ∨ PosUnsatisfiable K3.logic Γ) := by
  rw [pos_upentails_iff, pos_up_k3_is_k3]

theorem lp_pos_upentails_iff (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails (logic LP3.logic) Γ A ↔
      mvFDE.entails Γ A ∧
        (psubset (atoms A) (coveredBy Γ) ∨ PosUnsatisfiable LP3.logic Γ) := by
  rw [pos_upentails_iff, pos_up_lp_is_fde]

theorem fde_pos_upentails_iff (Γ : MVLogic.Theory α) (A : Fm α) :
    pos_upentails (logic mvFDE) Γ A ↔
      mvFDE.entails Γ A ∧
        (psubset (atoms A) (coveredBy Γ) ∨ PosUnsatisfiable mvFDE Γ) := by
  rw [pos_upentails_iff, pos_up_fde_is_fde]

theorem classical_upentails_iff (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails (logic mvClassical) Γ A ↔
      k3_entails (restrictToAtoms Γ A) A ∧
        (psubset (atoms A) (coveredBy (restrictToAtoms Γ A)) ∨
          PosUnsatisfiable mvClassical (restrictToAtoms Γ A)) := by
  rw [upentails_iff, pos_up_classical_is_k3]

theorem k3_upentails_iff (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails (logic K3.logic) Γ A ↔
      K3.logic.entails (restrictToAtoms Γ A) A ∧
        (psubset (atoms A) (coveredBy (restrictToAtoms Γ A)) ∨
          PosUnsatisfiable K3.logic (restrictToAtoms Γ A)) := by
  rw [upentails_iff, pos_up_k3_is_k3]

theorem lp_upentails_iff (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails (logic LP3.logic) Γ A ↔
      mvFDE.entails (restrictToAtoms Γ A) A ∧
        (psubset (atoms A) (coveredBy (restrictToAtoms Γ A)) ∨
          PosUnsatisfiable LP3.logic (restrictToAtoms Γ A)) := by
  rw [upentails_iff, pos_up_lp_is_fde]

theorem fde_upentails_iff (Γ : MVLogic.Theory α) (A : Fm α) :
    upentails (logic mvFDE) Γ A ↔
      mvFDE.entails (restrictToAtoms Γ A) A ∧
        (psubset (atoms A) (coveredBy (restrictToAtoms Γ A)) ∨
          PosUnsatisfiable mvFDE (restrictToAtoms Γ A)) := by
  rw [upentails_iff, pos_up_fde_is_fde]

theorem classical_ineffable_singleton (X Y : Fm α) :
    (logic mvClassical).entails (singletonTheory X) Y ↔
      mvClassical.entails (singletonTheory X) Y ∧
        (psubset (atoms Y) (atoms X) ∨ ∀ w, ¬ mvClassical.sat w X) :=
  entails_singleton_iff mvClassical X Y

theorem k3_ineffable_singleton (X Y : Fm α) :
    (logic K3.logic).entails (singletonTheory X) Y ↔
      K3.logic.entails (singletonTheory X) Y ∧
        (psubset (atoms Y) (atoms X) ∨ ∀ w, ¬ K3.logic.sat w X) :=
  entails_singleton_iff K3.logic X Y

theorem lp_ineffable_singleton (X Y : Fm α) :
    (logic LP3.logic).entails (singletonTheory X) Y ↔
      LP3.logic.entails (singletonTheory X) Y ∧
        (psubset (atoms Y) (atoms X) ∨ ∀ w, ¬ LP3.logic.sat w X) :=
  entails_singleton_iff LP3.logic X Y

theorem fde_ineffable_singleton (X Y : Fm α) :
    (logic mvFDE).entails (singletonTheory X) Y ↔
      mvFDE.entails (singletonTheory X) Y ∧
        (psubset (atoms Y) (atoms X) ∨ ∀ w, ¬ mvFDE.sat w X) :=
  entails_singleton_iff mvFDE X Y

/-! ## The two provisos are observable -/

theorem classical_unsatisfiable_proviso_fires :
    (logic mvClassical).entails
      (singletonTheory (Fm.conj (atom Atom.p) (Fm.neg (atom Atom.p))))
      (atom Atom.q) := by
  apply (classical_ineffable_singleton _ _).2
  constructor
  · intro v hprem
    have hbad := hprem (Fm.conj (atom Atom.p) (Fm.neg (atom Atom.p))) rfl
    cases hp : v Atom.p <;>
      simp [MVLogic.sat, MVLogic.eval, mvClassical, mvEval, hp] at hbad
  · right
    intro v hbad
    cases hp : v Atom.p <;>
      simp [MVLogic.sat, MVLogic.eval, mvClassical, mvEval, hp] at hbad

def classicalCoverageWitness : Atom → PSet (WithIneff Bool)
  | .q => psingleton .ineff
  | _ => psingleton (.val true)

theorem classical_disjunction_introduction_blocked_by_ineffable_atom :
    ¬ pos_upentails (logic mvClassical)
      (singletonTheory (atom Atom.p))
      (Fm.disj (atom Atom.p) (atom Atom.q)) := by
  intro h
  have hpos : ∀ a, pnonempty (classicalCoverageWitness a) := by
    intro a
    cases a with
    | p => exact ⟨.val true, rfl⟩
    | q => exact ⟨.ineff, rfl⟩
    | r => exact ⟨.val true, rfl⟩
  have hp : upsat (logic mvClassical) classicalCoverageWitness
      (atom Atom.p) := by
    intro z hz
    change z = .val true at hz
    cases hz
    rfl
  have hout := h classicalCoverageWitness hpos
    (fun C hC => by cases hC; exact hp)
  have hi : peval (neg mvClassical) (conj mvClassical) (disj mvClassical)
      classicalCoverageWitness (Fm.disj (atom Atom.p) (atom Atom.q))
      .ineff := by
    exact ⟨.val true, .ineff, rfl, rfl, rfl⟩
  exact hout .ineff hi

end WithIneff

end BuddhistComparativeLogic
