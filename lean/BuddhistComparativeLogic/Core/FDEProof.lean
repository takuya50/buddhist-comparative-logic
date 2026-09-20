/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.UniversalDesignation
import BuddhistComparativeLogic.Core.Decide

/-!
# Proof theory for FDE and FDE5

This is the Lean counterpart of `isabelle/Core/FDEProofTheory.thy`.  It proves the
variable-sharing theorem for FDE, characterizes Priest's absorbing
five-valued logic as FDE plus atom containment, and gives an executable
signed-literal decision procedure for formulas over any decidable atom type.

The results use the shared `BuddhistComparativeLogic.atoms` predicate-set API from
`BuddhistComparativeLogic.Core.UniversalDesignation`.
-/

namespace BuddhistComparativeLogic.FDEProof

open BuddhistComparativeLogic
open BuddhistComparativeLogic.Fm
open BuddhistComparativeLogic.TV4

/-! ## Formula atoms and the two consequence relations -/

/-- Single-premise consequence for the absorbing five-valued matrix. -/
def entails5 (X Y : Fm α) : Prop :=
  ∀ v : α → TV5, des5 (eval5 v X) = true → des5 (eval5 v Y) = true

theorem atoms_nonempty (X : Fm α) : ∃ a, atoms X a := by
  induction X with
  | atom a => exact ⟨a, rfl⟩
  | neg X ih => exact ih
  | conj X Y ihX _ =>
      obtain ⟨a, ha⟩ := ihX
      exact ⟨a, Or.inl ha⟩
  | disj X Y ihX _ =>
      obtain ⟨a, ha⟩ := ihX
      exact ⟨a, Or.inl ha⟩

/-! ## The independent truth and falsity bits -/

@[simp] theorem tr_mk (t f : Bool) : tr (mk t f) = t := by
  cases t <;> cases f <;> rfl

@[simp] theorem fa_mk (t f : Bool) : fa (mk t f) = f := by
  cases t <;> cases f <;> rfl

@[simp] theorem tr_neg4 (x : TV4) : tr (neg4 x) = fa x := by
  cases x <;> rfl

@[simp] theorem fa_neg4 (x : TV4) : fa (neg4 x) = tr x := by
  cases x <;> rfl

@[simp] theorem tr_conj4 (x y : TV4) : tr (conj4 x y) = (tr x && tr y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem fa_conj4 (x y : TV4) : fa (conj4 x y) = (fa x || fa y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem tr_disj4 (x y : TV4) : tr (disj4 x y) = (tr x || tr y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem fa_disj4 (x y : TV4) : fa (disj4 x y) = (fa x && fa y) := by
  cases x <;> cases y <;> rfl

theorem eval4_const_B {v : α → TV4} {X : Fm α}
    (h : ∀ a, atoms X a → v a = B) : eval4 v X = B := by
  induction X with
  | atom a => exact h a rfl
  | neg X ih =>
      have hx : eval4 v X = B := ih (fun a ha => h a ha)
      simp [eval4, hx, neg4, mk, tr, fa]
  | conj X Y ihX ihY =>
      have hx : eval4 v X = B := ihX (fun a ha => h a (Or.inl ha))
      have hy : eval4 v Y = B := ihY (fun a ha => h a (Or.inr ha))
      simp [eval4, hx, hy, conj4, mk, tr, fa]
  | disj X Y ihX ihY =>
      have hx : eval4 v X = B := ihX (fun a ha => h a (Or.inl ha))
      have hy : eval4 v Y = B := ihY (fun a ha => h a (Or.inr ha))
      simp [eval4, hx, hy, disj4, mk, tr, fa]

theorem eval4_const_N {v : α → TV4} {X : Fm α}
    (h : ∀ a, atoms X a → v a = N) : eval4 v X = N := by
  induction X with
  | atom a => exact h a rfl
  | neg X ih =>
      have hx : eval4 v X = N := ih (fun a ha => h a ha)
      simp [eval4, hx, neg4, mk, tr, fa]
  | conj X Y ihX ihY =>
      have hx : eval4 v X = N := ihX (fun a ha => h a (Or.inl ha))
      have hy : eval4 v Y = N := ihY (fun a ha => h a (Or.inr ha))
      simp [eval4, hx, hy, conj4, mk, tr, fa]
  | disj X Y ihX ihY =>
      have hx : eval4 v X = N := ihX (fun a ha => h a (Or.inl ha))
      have hy : eval4 v Y = N := ihY (fun a ha => h a (Or.inr ha))
      simp [eval4, hx, hy, disj4, mk, tr, fa]

/-! ## Relevance -/

theorem fde_variable_sharing {X Y : Fm α} (h : entails4 X Y) :
    pintersects (atoms X) (atoms Y) := by
  classical
  apply Classical.byContradiction
  intro hn
  have hdisjoint : ∀ a, atoms X a → ¬ atoms Y a := by
    intro a hxa hya
    exact hn ⟨a, hxa, hya⟩
  let v : α → TV4 := fun a => if atoms X a then B else N
  have hx : eval4 v X = B := eval4_const_B (fun a ha => by simp [v, ha])
  have hy : eval4 v Y = N := eval4_const_N (fun a ha => by
    have hna : ¬ atoms X a := by
      intro hxa
      exact hdisjoint a hxa ha
    simp [v, hna])
  have hsx : sat4 v X = true := by simp [sat4, hx, tr]
  have hsy := h v hsx
  simp [sat4, hy, tr] at hsy

theorem sharing_not_sufficient :
    pintersects
        (atoms (conj (atom BuddhistComparativeLogic.Atom.p) (neg (atom BuddhistComparativeLogic.Atom.p))))
        (atoms (conj (atom BuddhistComparativeLogic.Atom.p) (atom BuddhistComparativeLogic.Atom.q))) ∧
      ¬ entails4
        (conj (atom BuddhistComparativeLogic.Atom.p) (neg (atom BuddhistComparativeLogic.Atom.p)))
        (conj (atom BuddhistComparativeLogic.Atom.p) (atom BuddhistComparativeLogic.Atom.q)) := by
  constructor
  · exact ⟨BuddhistComparativeLogic.Atom.p, Or.inl rfl, Or.inl rfl⟩
  · intro h
    have hprem : sat4 glut_p
        (conj (atom BuddhistComparativeLogic.Atom.p) (neg (atom BuddhistComparativeLogic.Atom.p))) = true := by
      decide
    have hconcl := h glut_p hprem
    have hfalse : sat4 glut_p
        (conj (atom BuddhistComparativeLogic.Atom.p) (atom BuddhistComparativeLogic.Atom.q)) = false := by
      decide
    exact Bool.noConfusion (hfalse.symm.trans hconcl)

theorem fde_no_valid_formula (X : Fm α) :
    ¬ (∀ v : α → TV4, sat4 v X = true) := by
  intro h
  have hx : eval4 (fun _ => N) X = N := eval4_const_N (fun _ _ => rfl)
  have := h (fun _ => N)
  simp [sat4, hx, tr] at this

/-! ## The absorbing value and atom containment -/

@[simp] theorem neg5_eq_E_iff (x : TV5) : neg5 x = .E ↔ x = .E := by
  cases x <;> simp [neg5]

@[simp] theorem conj5_eq_E_iff (x y : TV5) : conj5 x y = .E ↔ x = .E ∨ y = .E := by
  cases x <;> cases y <;> simp [conj5]

@[simp] theorem disj5_eq_E_iff (x y : TV5) : disj5 x y = .E ↔ x = .E ∨ y = .E := by
  cases x <;> cases y <;> simp [disj5]

theorem eval5_eq_E_iff {v : α → TV5} {X : Fm α} :
    eval5 v X = .E ↔ ∃ a, atoms X a ∧ v a = .E := by
  induction X with
  | atom a => simp [eval5, atoms, psingleton]
  | neg X ih => simpa [eval5, atoms] using ih
  | conj X Y ihX ihY =>
      simp only [eval5, conj5_eq_E_iff, ihX, ihY, atoms]
      constructor
      · rintro (⟨a, ha, hva⟩ | ⟨a, ha, hva⟩)
        · exact ⟨a, Or.inl ha, hva⟩
        · exact ⟨a, Or.inr ha, hva⟩
      · rintro ⟨a, ha | ha, hva⟩
        · exact Or.inl ⟨a, ha, hva⟩
        · exact Or.inr ⟨a, ha, hva⟩
  | disj X Y ihX ihY =>
      simp only [eval5, disj5_eq_E_iff, ihX, ihY, atoms]
      constructor
      · rintro (⟨a, ha, hva⟩ | ⟨a, ha, hva⟩)
        · exact ⟨a, Or.inl ha, hva⟩
        · exact ⟨a, Or.inr ha, hva⟩
      · rintro ⟨a, ha | ha, hva⟩
        · exact Or.inl ⟨a, ha, hva⟩
        · exact Or.inr ⟨a, ha, hva⟩

def proj5 : TV5 → TV4
  | .fin x => x
  | .E => N

theorem eval5_all_fin (w : α → TV4) (X : Fm α) :
    eval5 (fun a => TV5.fin (w a)) X = TV5.fin (eval4 w X) := by
  induction X with
  | atom a => rfl
  | neg X ih => simp [eval5, eval4, ih, neg5]
  | conj X Y ihX ihY => simp [eval5, eval4, ihX, ihY, conj5]
  | disj X Y ihX ihY => simp [eval5, eval4, ihX, ihY, disj5]

theorem eval5_clean {v : α → TV5} {X : Fm α}
    (h : ∀ a, atoms X a → v a ≠ .E) :
    eval5 v X = TV5.fin (eval4 (fun a => proj5 (v a)) X) := by
  induction X with
  | atom a =>
      have ha := h a rfl
      cases hva : v a with
      | fin x =>
          simp only [eval5, eval4]
          rw [hva]
          rfl
      | E => exact False.elim (ha hva)
  | neg X ih =>
      have hx := ih (fun a ha => h a ha)
      simp [eval5, eval4, hx, neg5]
  | conj X Y ihX ihY =>
      have hx := ihX (fun a ha => h a (Or.inl ha))
      have hy := ihY (fun a ha => h a (Or.inr ha))
      simp [eval5, eval4, hx, hy, conj5]
  | disj X Y ihX ihY =>
      have hx := ihX (fun a ha => h a (Or.inl ha))
      have hy := ihY (fun a ha => h a (Or.inr ha))
      simp [eval5, eval4, hx, hy, disj5]

theorem fde5_no_valid_formula (X : Fm α) :
    ¬ (∀ v : α → TV5, des5 (eval5 v X) = true) := by
  intro h
  obtain ⟨a, ha⟩ := atoms_nonempty X
  have he : eval5 (fun _ => TV5.E) X = .E :=
    eval5_eq_E_iff.mpr ⟨a, ha, rfl⟩
  have := h (fun _ => TV5.E)
  simp [he, des5] at this

theorem fde5_is_fde_plus_containment {X Y : Fm α} :
    entails5 X Y ↔ psubset (atoms Y) (atoms X) ∧ entails4 X Y := by
  constructor
  · intro h5
    constructor
    · intro a hya
      classical
      apply Classical.byContradiction
      intro hxa
      let v : α → TV5 := fun b => if b = a then .E else .fin B
      have hcleanX : ∀ b, atoms X b → v b ≠ .E := by
        intro b hxb
        have hba : b ≠ a := by
          intro e
          apply hxa
          simpa [e] using hxb
        simp [v, hba]
      have hprojB : ∀ b, atoms X b → proj5 (v b) = B := by
        intro b hxb
        have hba : b ≠ a := by
          intro e
          apply hxa
          simpa [e] using hxb
        simp [v, hba, proj5]
      have hx4 : eval4 (fun b => proj5 (v b)) X = B := eval4_const_B hprojB
      have hx5 : eval5 v X = .fin B := by
        rw [eval5_clean hcleanX, hx4]
      have hyaE : v a = .E := by simp [v]
      have hy5 : eval5 v Y = .E := eval5_eq_E_iff.mpr ⟨a, hya, hyaE⟩
      have hs := h5 v (by simp [hx5, des5, tr])
      simp [hy5, des5] at hs
    · intro w hx
      have hx5 : des5 (eval5 (fun a => .fin (w a)) X) = true := by
        simpa [eval5_all_fin, des5, sat4] using hx
      have hy5 := h5 (fun a => .fin (w a)) hx5
      simpa [eval5_all_fin, des5, sat4] using hy5
  · rintro ⟨hcont, h4⟩ v hx5
    have hcleanX : ∀ a, atoms X a → v a ≠ .E := by
      intro a hxa hva
      have he : eval5 v X = .E := eval5_eq_E_iff.mpr ⟨a, hxa, hva⟩
      simp [he, des5] at hx5
    have hcleanY : ∀ a, atoms Y a → v a ≠ .E := by
      intro a hya
      exact hcleanX a (hcont a hya)
    have ex := eval5_clean hcleanX
    have ey := eval5_clean hcleanY
    have hx4 : sat4 (fun a => proj5 (v a)) X = true := by
      simpa [sat4, ex, des5] using hx5
    have hy4 := h4 (fun a => proj5 (v a)) hx4
    simpa [sat4, ey, des5] using hy4

theorem fde5_variable_sharing {X Y : Fm α} (h : entails5 X Y) :
    pintersects (atoms X) (atoms Y) := by
  have h4 : entails4 X Y := (fde5_is_fde_plus_containment.mp h).2
  exact fde_variable_sharing h4

/-! ## Signed literals and branch expansion -/

inductive Sign where
  | tr
  | fl
  deriving DecidableEq, Repr

inductive SLit (α : Type) where
  | mk (polarity : Bool) (sign : Sign) (atom : α)
  deriving DecidableEq, Repr

def bitv : Sign → TV4 → Bool
  | .tr, x => tr x
  | .fl, x => fa x

def flipSign : Sign → Sign
  | .tr => .fl
  | .fl => .tr

@[simp] theorem bitv_neg4 (s : Sign) (x : TV4) :
    bitv s (neg4 x) = bitv (flipSign s) x := by
  cases s <;> simp [bitv, flipSign]

def holdsLit (v : α → TV4) : SLit α → Prop
  | .mk polarity sign a => bitv sign (v a) = polarity

def negLit : SLit α → SLit α
  | .mk polarity sign a => .mk (!polarity) sign a

def meetBranches (us ws : List (List (SLit α))) : List (List (SLit α)) :=
  us.flatMap fun u => ws.map fun w => u ++ w

abbrev meetl := @meetBranches

def satBranches (v : α → TV4) (branches : List (List (SLit α))) : Prop :=
  ∃ branch ∈ branches, ∀ literal ∈ branch, holdsLit v literal

abbrev satb := @satBranches

@[simp] theorem satBranches_single (v : α → TV4) (l : SLit α) :
    satBranches v [[l]] ↔ holdsLit v l := by
  simp [satBranches]

@[simp] theorem satBranches_append (v : α → TV4)
    (us ws : List (List (SLit α))) :
    satBranches v (us ++ ws) ↔ satBranches v us ∨ satBranches v ws := by
  simp only [satBranches, List.mem_append]
  constructor
  · rintro ⟨b, hb | hb, hall⟩
    · exact Or.inl ⟨b, hb, hall⟩
    · exact Or.inr ⟨b, hb, hall⟩
  · rintro (⟨b, hb, hall⟩ | ⟨b, hb, hall⟩)
    · exact ⟨b, Or.inl hb, hall⟩
    · exact ⟨b, Or.inr hb, hall⟩

@[simp] theorem satBranches_meet (v : α → TV4)
    (us ws : List (List (SLit α))) :
    satBranches v (meetBranches us ws) ↔ satBranches v us ∧ satBranches v ws := by
  constructor
  · rintro ⟨b, hb, hall⟩
    rw [meetBranches, List.mem_flatMap] at hb
    obtain ⟨u, hu, hb⟩ := hb
    rw [List.mem_map] at hb
    obtain ⟨w, hw, huw⟩ := hb
    subst b
    constructor
    · exact ⟨u, hu, fun l hl => hall l (List.mem_append.mpr (Or.inl hl))⟩
    · exact ⟨w, hw, fun l hl => hall l (List.mem_append.mpr (Or.inr hl))⟩
  · rintro ⟨⟨u, hu, hallu⟩, ⟨w, hw, hallw⟩⟩
    refine ⟨u ++ w, ?_, ?_⟩
    · rw [meetBranches, List.mem_flatMap]
      exact ⟨u, hu, List.mem_map.mpr ⟨w, hw, rfl⟩⟩
    · intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact hallu l hl
      · exact hallw l hl

def expand : Bool → Sign → Fm α → List (List (SLit α))
  | polarity, sign, .atom a => [[.mk polarity sign a]]
  | polarity, sign, .neg X => expand polarity (flipSign sign) X
  | true, .tr, .conj X Y => meetBranches (expand true .tr X) (expand true .tr Y)
  | false, .tr, .conj X Y => expand false .tr X ++ expand false .tr Y
  | true, .fl, .conj X Y => expand true .fl X ++ expand true .fl Y
  | false, .fl, .conj X Y => meetBranches (expand false .fl X) (expand false .fl Y)
  | true, .tr, .disj X Y => expand true .tr X ++ expand true .tr Y
  | false, .tr, .disj X Y => meetBranches (expand false .tr X) (expand false .tr Y)
  | true, .fl, .disj X Y => meetBranches (expand true .fl X) (expand true .fl Y)
  | false, .fl, .disj X Y => expand false .fl X ++ expand false .fl Y

abbrev expandl := @expand

@[simp] theorem bool_and_eq_false (a b : Bool) :
    ((a && b) = false) ↔ a = false ∨ b = false := by
  cases a <;> cases b <;> simp

@[simp] theorem bool_or_eq_false (a b : Bool) :
    ((a || b) = false) ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> simp

theorem expand_correct (v : α → TV4) (X : Fm α) (polarity : Bool) (sign : Sign) :
    bitv sign (eval4 v X) = polarity ↔ satBranches v (expand polarity sign X) := by
  induction X generalizing polarity sign with
  | atom a =>
      cases polarity <;> cases sign <;>
        simp [expand, eval4, satBranches, holdsLit, bitv]
  | neg X ih =>
      simpa [expand, eval4, bitv_neg4] using ih polarity (flipSign sign)
  | conj X Y ihX ihY =>
      cases polarity with
      | false =>
          cases sign with
          | tr =>
              simp only [bitv, eval4, tr_conj4, bool_and_eq_false,
                expand, satBranches_append]
              exact or_congr
                (by simpa only [bitv] using ihX false .tr)
                (by simpa only [bitv] using ihY false .tr)
          | fl =>
              simp only [bitv, eval4, fa_conj4, bool_or_eq_false,
                expand, satBranches_meet]
              exact and_congr
                (by simpa only [bitv] using ihX false .fl)
                (by simpa only [bitv] using ihY false .fl)
      | true =>
          cases sign with
          | tr =>
              simp only [bitv, eval4, tr_conj4, Bool.and_eq_true,
                expand, satBranches_meet]
              exact and_congr
                (by simpa only [bitv] using ihX true .tr)
                (by simpa only [bitv] using ihY true .tr)
          | fl =>
              simp only [bitv, eval4, fa_conj4, Bool.or_eq_true,
                expand, satBranches_append]
              exact or_congr
                (by simpa only [bitv] using ihX true .fl)
                (by simpa only [bitv] using ihY true .fl)
  | disj X Y ihX ihY =>
      cases polarity with
      | false =>
          cases sign with
          | tr =>
              simp only [bitv, eval4, tr_disj4, bool_or_eq_false,
                expand, satBranches_meet]
              exact and_congr
                (by simpa only [bitv] using ihX false .tr)
                (by simpa only [bitv] using ihY false .tr)
          | fl =>
              simp only [bitv, eval4, fa_disj4, bool_and_eq_false,
                expand, satBranches_append]
              exact or_congr
                (by simpa only [bitv] using ihX false .fl)
                (by simpa only [bitv] using ihY false .fl)
      | true =>
          cases sign with
          | tr =>
              simp only [bitv, eval4, tr_disj4, Bool.or_eq_true,
                expand, satBranches_append]
              exact or_congr
                (by simpa only [bitv] using ihX true .tr)
                (by simpa only [bitv] using ihY true .tr)
          | fl =>
              simp only [bitv, eval4, fa_disj4, Bool.and_eq_true,
                expand, satBranches_meet]
              exact and_congr
                (by simpa only [bitv] using ihX true .fl)
                (by simpa only [bitv] using ihY true .fl)

theorem expandl_correct (v : α → TV4) (X : Fm α)
    (polarity : Bool) (sign : Sign) :
    bitv sign (eval4 v X) = polarity ↔ satb v (expandl polarity sign X) :=
  expand_correct v X polarity sign

/-! ## Open branches -/

def closedLits [DecidableEq α] (branch : List (SLit α)) : Bool :=
  branch.any fun literal => branch.contains (negLit literal)

abbrev closed_lits := @closedLits

theorem closedLits_iff [DecidableEq α] {branch : List (SLit α)} :
    closedLits branch = true ↔ ∃ literal ∈ branch, negLit literal ∈ branch := by
  simp [closedLits]

theorem closed_unsat [DecidableEq α] {branch : List (SLit α)}
    (hclosed : closedLits branch = true) (v : α → TV4) :
    ¬ (∀ literal ∈ branch, holdsLit v literal) := by
  intro hall
  obtain ⟨literal, hl, hnl⟩ := closedLits_iff.mp hclosed
  have h1 := hall literal hl
  have h2 := hall (negLit literal) hnl
  rcases literal with ⟨polarity, sign, a⟩
  change bitv sign (v a) = polarity at h1
  change bitv sign (v a) = !polarity at h2
  cases polarity <;> simp_all

/-- The computable valuation already used in the open-branch argument. -/
def branchVal [DecidableEq α] (branch : List (SLit α)) (a : α) : TV4 :=
  mk (decide (SLit.mk true .tr a ∈ branch))
    (decide (SLit.mk true .fl a ∈ branch))

theorem branchVal_holds [DecidableEq α] {branch : List (SLit α)}
    (hopen : closedLits branch = false) :
    ∀ literal ∈ branch, holdsLit (branchVal branch) literal := by
  intro literal hl
  rcases literal with ⟨polarity, sign, a⟩
  cases polarity with
  | true =>
      cases sign <;> simp [holdsLit, bitv, branchVal, hl]
  | false =>
      have hpositive : SLit.mk true sign a ∉ branch := by
        intro hp
        have hc : closedLits branch = true := closedLits_iff.mpr
          ⟨SLit.mk true sign a, hp, by simpa [negLit] using hl⟩
        simp [hopen] at hc
      cases sign <;> simp [holdsLit, bitv, branchVal, hpositive]

theorem open_sat [DecidableEq α] {branch : List (SLit α)}
    (hopen : closedLits branch = false) :
    ∃ v : α → TV4, ∀ literal ∈ branch, holdsLit v literal :=
  ⟨branchVal branch, branchVal_holds hopen⟩

/-! ## Complete executable decision procedures -/

def fdeDec [DecidableEq α] (X Y : Fm α) : Bool :=
  (meetBranches (expand true .tr X) (expand false .tr Y)).all closedLits

abbrev fde_dec := @fdeDec

theorem fde_dec_correct [DecidableEq α] (X Y : Fm α) :
    entails4 X Y ↔ fdeDec X Y = true := by
  let branches := meetBranches (expand true .tr X) (expand false .tr Y)
  constructor
  · intro hentails
    rw [fdeDec, List.all_eq_true]
    intro branch hbranch
    apply Decidable.byContradiction
    intro hnclosed
    have hopen : closedLits branch = false := Bool.eq_false_iff.mpr hnclosed
    obtain ⟨v, hall⟩ := open_sat hopen
    have hs : satBranches v branches := ⟨branch, hbranch, hall⟩
    have hsxy : satBranches v (expand true .tr X) ∧
        satBranches v (expand false .tr Y) := by
      simpa [branches] using hs
    have hx : bitv .tr (eval4 v X) = true :=
      (expand_correct v X true .tr).mpr hsxy.1
    have hy : bitv .tr (eval4 v Y) = false :=
      (expand_correct v Y false .tr).mpr hsxy.2
    have hy' := hentails v (by simpa [sat4, bitv] using hx)
    change tr (eval4 v Y) = false at hy
    change tr (eval4 v Y) = true at hy'
    exact Bool.noConfusion (hy.symm.trans hy')
  · intro hall v hx
    rw [fdeDec, List.all_eq_true] at hall
    apply Decidable.byContradiction
    intro hny
    have hy : sat4 v Y = false := Bool.eq_false_iff.mpr hny
    have hsx : satBranches v (expand true .tr X) :=
      (expand_correct v X true .tr).mp (by simpa [sat4, bitv] using hx)
    have hsy : satBranches v (expand false .tr Y) :=
      (expand_correct v Y false .tr).mp (by simpa [sat4, bitv] using hy)
    have hs : satBranches v branches := by
      simpa [branches] using And.intro hsx hsy
    obtain ⟨branch, hbranch, hsatisfied⟩ := hs
    have hc : closedLits branch = true := by
      exact hall branch (by simpa [branches] using hbranch)
    exact closed_unsat hc v hsatisfied

def atomList : Fm α → List α
  | .atom a => [a]
  | .neg X => atomList X
  | .conj X Y => atomList X ++ atomList Y
  | .disj X Y => atomList X ++ atomList Y

abbrev atomsl := @atomList

theorem mem_atomList_iff [DecidableEq α] (a : α) (X : Fm α) :
    a ∈ atomList X ↔ atoms X a := by
  induction X with
  | atom b => simp [atomList, atoms, psingleton]
  | neg X ih => simpa [atomList, atoms] using ih
  | conj X Y ihX ihY => simp [atomList, atoms, ihX, ihY]
  | disj X Y ihX ihY => simp [atomList, atoms, ihX, ihY]

def atomContainmentDec [DecidableEq α] (X Y : Fm α) : Bool :=
  (atomList Y).all fun a => (atomList X).contains a

theorem atom_containment_dec_correct [DecidableEq α] (X Y : Fm α) :
    psubset (atoms Y) (atoms X) ↔ atomContainmentDec X Y = true := by
  rw [atomContainmentDec, List.all_eq_true]
  constructor
  · intro h a ha
    rw [List.contains_iff_mem, mem_atomList_iff]
    exact h a ((mem_atomList_iff a Y).mp ha)
  · intro h a ha
    have hay : a ∈ atomList Y := (mem_atomList_iff a Y).mpr ha
    have := h a hay
    exact (mem_atomList_iff a X).mp (List.contains_iff_mem.mp this)

def fde5Dec [DecidableEq α] (X Y : Fm α) : Bool :=
  atomContainmentDec X Y && fdeDec X Y

abbrev fde5_dec := @fde5Dec

theorem fde5_dec_correct [DecidableEq α] (X Y : Fm α) :
    entails5 X Y ↔ fde5Dec X Y = true := by
  rw [fde5_is_fde_plus_containment, fde5Dec, Bool.and_eq_true]
  exact and_congr (atom_containment_dec_correct X Y) (fde_dec_correct X Y)

theorem decide_agree (X Y : Fm BuddhistComparativeLogic.Atom) :
    entails4ListDec [X] Y = true ↔ fde_dec X Y = true := by
  calc
    entails4ListDec [X] Y = true ↔ entails4List [X] Y :=
      (entails4_correct [X] Y).symm
    _ ↔ entails4 X Y := by simp [entails4List, entails4]
    _ ↔ fde_dec X Y = true := fde_dec_correct X Y

/-! ## Executable finite countermodel certificates

The search reuses the signed-branch procedure above.  Its output is finite
data, not an existential proof or a function closure.  Tables may repeat an
atom (with the same value); unlisted atoms receive the stated default.
-/

/-- Read a finite assignment, using the first matching entry and a default. -/
def assignmentVal [DecidableEq α] (fallback : β) : List (α × β) → α → β
  | [], _ => fallback
  | (a, value) :: rest, b => if b = a then value else assignmentVal fallback rest b

theorem assignmentVal_map [DecidableEq α] (fallback : β) (as : List α)
    (v : α → β) {a : α} (ha : a ∈ as) :
    assignmentVal fallback (as.map fun b => (b, v b)) a = v a := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
      by_cases hab : a = b
      · simp [assignmentVal, hab]
      · simp only [List.mem_cons] at ha
        simp [assignmentVal, hab, ih (ha.resolve_left hab)]

theorem eval4_agree_on_atoms {v w : α → TV4} (X : Fm α)
    (h : ∀ a, atoms X a → v a = w a) : eval4 v X = eval4 w X := by
  induction X with
  | atom a => exact h a rfl
  | neg X ih => simp [eval4, ih h]
  | conj X Y ihX ihY =>
      simp [eval4, ihX (fun a ha => h a (Or.inl ha)),
        ihY (fun a ha => h a (Or.inr ha))]
  | disj X Y ihX ihY =>
      simp [eval4, ihX (fun a ha => h a (Or.inl ha)),
        ihY (fun a ha => h a (Or.inr ha))]

/-- Search for an open branch, then return the values of all input atoms. -/
def fdeCountermodel [DecidableEq α] (X Y : Fm α) : Option (List (α × TV4)) :=
  ((meetBranches (expand true .tr X) (expand false .tr Y)).find?
    fun b => !closedLits b).map fun b =>
      (atomList X ++ atomList Y).map fun a => (a, branchVal b a)

theorem fdeCountermodel_sound [DecidableEq α] {X Y : Fm α}
    {table : List (α × TV4)} (h : fdeCountermodel X Y = some table) :
    sat4 (assignmentVal N table) X = true ∧
      sat4 (assignmentVal N table) Y = false := by
  unfold fdeCountermodel at h
  cases hb : (meetBranches (expand true .tr X) (expand false .tr Y)).find?
      (fun b => !closedLits b) with
  | none => simp [hb] at h
  | some b =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst table
      have hopen : closedLits b = false := by simpa using List.find?_some hb
      have hs : satBranches (branchVal b)
          (meetBranches (expand true .tr X) (expand false .tr Y)) :=
        ⟨b, List.mem_of_find?_eq_some hb, branchVal_holds hopen⟩
      have hsxy := (satBranches_meet _ _ _).mp hs
      have hx := (expand_correct (branchVal b) X true .tr).mpr hsxy.1
      have hy := (expand_correct (branchVal b) Y false .tr).mpr hsxy.2
      have eqX : eval4 (assignmentVal N
          ((atomList X ++ atomList Y).map fun a => (a, branchVal b a))) X =
          eval4 (branchVal b) X := by
        apply eval4_agree_on_atoms
        intro a ha
        exact assignmentVal_map _ _ _ (List.mem_append.mpr
          (Or.inl ((mem_atomList_iff a X).mpr ha)))
      have eqY : eval4 (assignmentVal N
          ((atomList X ++ atomList Y).map fun a => (a, branchVal b a))) Y =
          eval4 (branchVal b) Y := by
        apply eval4_agree_on_atoms
        intro a ha
        exact assignmentVal_map _ _ _ (List.mem_append.mpr
          (Or.inr ((mem_atomList_iff a Y).mpr ha)))
      simpa only [sat4, eqX, eqY, bitv] using And.intro hx hy

theorem fdeCountermodel_none_iff [DecidableEq α] (X Y : Fm α) :
    fdeCountermodel X Y = none ↔ entails4 X Y := by
  rw [fde_dec_correct]
  simp [fdeCountermodel, fdeDec, List.find?_eq_none, List.all_eq_true]

theorem fdeCountermodel_complete [DecidableEq α] (X Y : Fm α) :
    (∃ table, fdeCountermodel X Y = some table) ↔ ¬ entails4 X Y := by
  rw [← fdeCountermodel_none_iff]
  cases fdeCountermodel X Y <;> simp

/-- Distinct causes of FDE5 failure, each represented by finite assignment data.
`atomEscape a` denotes the singleton assignment `a ↦ E`, default `fin B`;
`fdeWitness table` lifts the FDE assignment, default `fin N`. -/
inductive Countermodel5 (α : Type) where
  | atomEscape (a : α)
  | fdeWitness (table : List (α × TV4))
  deriving DecidableEq, Repr

def Countermodel5.table : Countermodel5 α → List (α × TV5)
  | .atomEscape a => [(a, .E)]
  | .fdeWitness table => table.map fun av => (av.1, .fin av.2)

def Countermodel5.fallback : Countermodel5 α → TV5
  | .atomEscape _ => .fin B
  | .fdeWitness _ => .fin N

def Countermodel5.valuation [DecidableEq α] (c : Countermodel5 α) : α → TV5 :=
  assignmentVal c.fallback c.table

theorem assignmentVal_lift [DecidableEq α] (table : List (α × TV4)) (a : α) :
    assignmentVal (TV5.fin N) (table.map fun av => (av.1, TV5.fin av.2)) a =
      TV5.fin (assignmentVal N table a) := by
  induction table with
  | nil => rfl
  | cons av rest ih => simp [assignmentVal, ih]; split <;> rfl

/-- Prefer a containment witness; otherwise extract an FDE countermodel. -/
def fde5Countermodel [DecidableEq α] (X Y : Fm α) : Option (Countermodel5 α) :=
  match (atomList Y).find? (fun a => !(atomList X).contains a) with
  | some a => some (.atomEscape a)
  | none => (fdeCountermodel X Y).map Countermodel5.fdeWitness

theorem fde5Countermodel_sound [DecidableEq α] {X Y : Fm α}
    {c : Countermodel5 α} (h : fde5Countermodel X Y = some c) :
    des5 (eval5 c.valuation X) = true ∧ des5 (eval5 c.valuation Y) = false := by
  unfold fde5Countermodel at h
  cases ha : (atomList Y).find? (fun a => !(atomList X).contains a) with
  | some a =>
      simp only [ha, Option.some.injEq] at h
      subst c
      have hya : atoms Y a := (mem_atomList_iff a Y).mp (List.mem_of_find?_eq_some ha)
      have hxa : ¬ atoms X a := by
        have := List.find?_some ha
        simpa [List.contains_iff_mem, mem_atomList_iff] using this
      have hclean : ∀ b, atoms X b → (Countermodel5.atomEscape a).valuation b ≠ .E := by
        intro b hb
        have hba : b ≠ a := by intro e; subst b; exact hxa hb
        simp [Countermodel5.valuation, Countermodel5.table, Countermodel5.fallback,
          assignmentVal, hba]
      have hx := eval5_clean hclean
      have hxB : eval4 (fun b => proj5 ((Countermodel5.atomEscape a).valuation b)) X = B := by
        apply eval4_const_B
        intro b hb
        have hba : b ≠ a := by intro e; subst b; exact hxa hb
        simp [Countermodel5.valuation, Countermodel5.table, Countermodel5.fallback,
          assignmentVal, hba, proj5]
      have hy : eval5 (Countermodel5.atomEscape a).valuation Y = .E :=
        eval5_eq_E_iff.mpr ⟨a, hya, by simp [Countermodel5.valuation,
          Countermodel5.table, Countermodel5.fallback, assignmentVal]⟩
      simp [hx, hxB, hy, des5, tr]
  | none =>
      simp only [ha] at h
      cases ht : fdeCountermodel X Y with
      | none => simp [ht] at h
      | some table =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst c
          have hv : (Countermodel5.fdeWitness table).valuation =
              (fun a => TV5.fin (assignmentVal N table a)) := by
            funext a
            exact assignmentVal_lift table a
          simpa [hv, eval5_all_fin, des5, sat4] using fdeCountermodel_sound ht

theorem fde5Countermodel_none_iff [DecidableEq α] (X Y : Fm α) :
    fde5Countermodel X Y = none ↔ entails5 X Y := by
  rw [fde5_is_fde_plus_containment]
  unfold fde5Countermodel
  cases ha : (atomList Y).find? (fun a => !(atomList X).contains a) with
  | none =>
      have hc : psubset (atoms Y) (atoms X) := by
        have h := List.find?_eq_none.mp ha
        intro a hay
        have := h a ((mem_atomList_iff a Y).mpr hay)
        simpa [List.contains_iff_mem, mem_atomList_iff] using this
      simp [hc, fdeCountermodel_none_iff]
  | some a =>
      have hya : atoms Y a := (mem_atomList_iff a Y).mp (List.mem_of_find?_eq_some ha)
      have hxa : ¬ atoms X a := by
        have := List.find?_some ha
        simpa [List.contains_iff_mem, mem_atomList_iff] using this
      have hc : ¬ psubset (atoms Y) (atoms X) := fun h => hxa (h a hya)
      simp [hc]

theorem fde5Countermodel_complete [DecidableEq α] (X Y : Fm α) :
    (∃ c, fde5Countermodel X Y = some c) ↔ ¬ entails5 X Y := by
  rw [← fde5Countermodel_none_iff]
  cases fde5Countermodel X Y <;> simp

/-! ## Executable examples -/

open BuddhistComparativeLogic.Atom

theorem dec_mp :
    fdeDec (conj (atom p) (disj (neg (atom p)) (atom q))) (atom q) = false := by
  decide

theorem dec_explosion :
    fdeDec (conj (atom p) (neg (atom p))) (atom q) = false := by
  decide

theorem dec_conj_elim :
    fdeDec (conj (atom p) (atom q)) (atom p) = true := by
  decide

theorem dec_disj_intro :
    fdeDec (atom p) (disj (atom p) (atom q)) = true := by
  decide

theorem dec_demorgan :
    fdeDec (neg (conj (atom p) (atom q)))
      (disj (neg (atom p)) (neg (atom q))) = true := by
  decide

theorem dec_double_neg :
    fdeDec (neg (neg (atom p))) (atom p) = true := by
  decide

theorem dec_distribution :
    fdeDec (conj (atom p) (disj (atom q) (atom r)))
      (disj (conj (atom p) (atom q)) (conj (atom p) (atom r))) = true := by
  decide

theorem dec5_disj_intro_fails :
    fde5Dec (atom p) (disj (atom p) (atom q)) = false := by
  decide

theorem dec5_conj_elim :
    fde5Dec (conj (atom p) (atom q)) (atom p) = true := by
  decide

theorem dec5_double_neg :
    fde5Dec (neg (neg (atom p))) (atom p) = true := by
  decide

theorem countermodel_explosion :
    fdeCountermodel (conj (atom p) (neg (atom p))) (atom q) =
      some [(p, B), (p, B), (q, N)] := by decide

theorem countermodel_conj_elim :
    fdeCountermodel (conj (atom p) (atom q)) (atom p) = none := by decide

theorem countermodel5_atom_escape :
    fde5Countermodel (atom p) (disj (atom p) (atom q)) =
      some (.atomEscape q) := by decide

theorem countermodel5_valid_conj :
    fde5Countermodel (conj (atom p) (neg (atom p))) (neg (atom p)) = none := by decide

theorem countermodel5_same_atoms :
    fde5Countermodel (atom p) (neg (atom p)) =
      some (.fdeWitness [(p, T), (p, T)]) := by decide

end BuddhistComparativeLogic.FDEProof
