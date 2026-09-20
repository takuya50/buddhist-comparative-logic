/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation
import BuddhistComparativeLogic.Core.MVLogic
import BuddhistComparativeLogic.Buddhist.HeartSutra.Dharma

/-!
# Emptiness, dependent origination, and readings of HS06--HS10

Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Emptiness.thy`.  As in the Isabelle development,
all doctrinal results are conditional on the fields of `Emptiness`; the
structure is a reconstruction of the sutra's claims, not evidence for
those claims.
-/

namespace BuddhistComparativeLogic

open Fm TV4 TV5 Atom

inductive Dharma where
  | sk : Skandha → Dharma
  | ay : Ayatana → Dharma
  | dh : Dhatu → Dharma
  | ni : Nidana → Dharma
  | niNirodha : Nidana → Dharma
  | sa : Satya → Dharma
  | jnana
  | prapti
  deriving DecidableEq, Repr

open Dharma

/-- The 65 items denied own-being in HS11--HS19. -/
def negated_dharmas : List Dharma :=
  skandhas.map sk ++ ayatanas.map ay ++ dhatus.map dh ++
    anuloma.map ni ++ anuloma.map niNirodha ++ satyas.map sa ++
    [jnana, prapti]

theorem negated_dharmas_length : negated_dharmas.length = 65 := by
  decide

theorem negated_dharmas_distinct : negated_dharmas.Nodup := by
  decide

/-- Membership form of Isabelle's equality with the whole finite carrier. -/
theorem negated_dharmas_covers (d : Dharma) : d ∈ negated_dharmas := by
  cases d with
  | sk s => cases s <;> decide
  | ay a =>
      cases a with
      | In i => cases i <;> decide
      | Vi o => cases o <;> decide
  | dh d =>
      rcases d with ⟨i, k⟩
      cases i <;> cases k <;> decide
  | ni n => cases n <;> decide
  | niNirodha n => cases n <;> decide
  | sa s => cases s <;> decide
  | jnana => decide
  | prapti => decide

/-- Data before doctrinal assumptions.  The truth-value logic retains its
nontriviality conditions, but none of the four emptiness premises is bundled
into this interface. -/
structure EmptinessData (V : Type u) where
  logic : MVLogic V
  sv : Dharma → V
  appears : Dharma → V
  dep : Dharma → Dharma → Prop

namespace EmptinessData

def MMK2418 (M : EmptinessData V) : Prop :=
  ∀ x, (∃ y, M.dep y x) → M.logic.designated (M.logic.neg (M.sv x))

def Pratitya (M : EmptinessData V) : Prop := ∀ x, ∃ y, M.dep y x

def Samvrti (M : EmptinessData V) : Prop :=
  ∀ x, M.logic.designated (M.appears x)

def NidanaDep (M : EmptinessData V) : Prop :=
  ∀ n m, nidanaNext n = some m → M.dep (ni n) (ni m)

def AllEmpty (M : EmptinessData V) : Prop :=
  ∀ x, M.logic.designated (M.logic.neg (M.sv x))

/-- Universal instantiation and modus ponens: neither `Samvrti` nor
`NidanaDep` occurs in this theorem's hypotheses. -/
theorem sarva_dharma_sunya_from_core (M : EmptinessData V)
    (hmmk : M.MMK2418) (hpratitya : M.Pratitya) : M.AllEmpty := by
  intro x
  exact hmmk x (hpratitya x)

end EmptinessData

/-- Explicit-record counterpart of Isabelle's `emptiness` locale. -/
structure Emptiness (V : Type u) where
  logic : MVLogic V
  sv : Dharma → V
  appears : Dharma → V
  dep : Dharma → Dharma → Prop
  mmk_24_18 : ∀ {x}, (∃ y, dep y x) → logic.designated (logic.neg (sv x))
  pratitya : ∀ x, ∃ y, dep y x
  samvrti : ∀ x, logic.designated (appears x)
  nidana_dep : ∀ {n m}, nidanaNext n = some m → dep (ni n) (ni m)

namespace Emptiness

variable (E : Emptiness V)

/-- Forget all four assumptions without changing the semantic data. -/
def toData : EmptinessData V :=
  ⟨E.logic, E.sv, E.appears, E.dep⟩

def sunya (x : Dharma) : V := E.logic.neg (E.sv x)

def emptyOf (x : Dharma) : Prop := E.logic.designated (E.sunya x)

/-- Value-identity reading of 色即是空. -/
def RIdentity (x : Dharma) : Prop := E.appears x = E.sunya x

/-- Mutual implication at the level of designation. -/
def RMutual (x : Dharma) : Prop :=
  E.logic.designated (E.appears x) ↔ E.logic.designated (E.sunya x)

/-- Attwood's "not separate from" reading. -/
def RNotsep (x : Dharma) : Prop :=
  ¬ E.logic.designated (E.logic.mconj (E.appears x) (E.sv x)) ∧
  ¬ E.logic.designated
    (E.logic.mconj (E.sunya x) (E.logic.neg (E.appears x)))

theorem sarva_dharma_sunya (x : Dharma) : E.emptyOf x := by
  exact E.toData.sarva_dharma_sunya_from_core (fun _ => E.mmk_24_18) E.pratitya x

theorem hs03_skandhas : ∀ s, E.emptyOf (sk s) := by
  intro s
  exact E.sarva_dharma_sunya (sk s)

theorem hs07_R_mutual (x : Dharma) : E.RMutual x := by
  constructor
  · intro _
    exact E.sarva_dharma_sunya x
  · intro _
    exact E.samvrti x

theorem hs08_generalize : ∀ s, E.RMutual (sk s) := by
  intro s
  exact E.hs07_R_mutual (sk s)

theorem hs11_18_enumeration :
    ∀ d, d ∈ negated_dharmas → E.emptyOf d := by
  intro d _
  exact E.sarva_dharma_sunya d

theorem hs15_16_chain_and_cessation :
    ∀ n, E.emptyOf (ni n) ∧ E.emptyOf (niNirodha n) := by
  intro n
  exact ⟨E.sarva_dharma_sunya _, E.sarva_dharma_sunya _⟩

theorem hs19_no_attainment : E.emptyOf prapti :=
  E.sarva_dharma_sunya prapti

end Emptiness

/-! ## Concrete models and comparison of the three readings -/

def classicalEmptiness : Emptiness Bool where
  logic := mvClassical
  sv _ := false
  appears _ := true
  dep _ _ := True
  mmk_24_18 _ := rfl
  pratitya _ := ⟨jnana, trivial⟩
  samvrti _ := rfl
  nidana_dep _ := trivial

/-! ## Relative independence of the two universal-emptiness premises

Both omissions reuse the classical model above and preserve its logic,
conventional appearances, and nidana-chain condition.  These are independence
results for this chosen four-premise signature, not absolute weakest-premise
claims or claims about doctrinal necessity.  The richer downstream pipeline
certificates remain in `PremiseCertificates`; no duplicate certificate system
is introduced here.
-/

/-- Keep universal dependence and make every own-being value true. -/
def emptinessWithoutMMK : EmptinessData Bool :=
  { classicalEmptiness.toData with sv := fun _ => true }

/-- Only `jnana` has own-being, and precisely that target lacks a dependency.
All nidana edges remain present. -/
def emptinessWithoutPratitya : EmptinessData Bool :=
  { classicalEmptiness.toData with
    sv := fun x => if x = jnana then true else false
    dep := fun _ x => x ≠ jnana }

theorem emptiness_without_mmk :
    emptinessWithoutMMK.logic = mvClassical ∧
      emptinessWithoutMMK.Samvrti ∧ emptinessWithoutMMK.NidanaDep ∧
      emptinessWithoutMMK.Pratitya ∧ ¬ emptinessWithoutMMK.MMK2418 ∧
      ¬ emptinessWithoutMMK.AllEmpty := by
  refine ⟨rfl, fun _ => rfl, fun _ _ _ => trivial,
    fun _ => ⟨jnana, trivial⟩, ?_, ?_⟩
  · intro h
    have bad := h jnana ⟨jnana, trivial⟩
    exact Bool.noConfusion bad
  · intro h
    exact Bool.noConfusion (h jnana)

theorem emptiness_without_pratitya :
    emptinessWithoutPratitya.logic = mvClassical ∧
      emptinessWithoutPratitya.Samvrti ∧ emptinessWithoutPratitya.NidanaDep ∧
      emptinessWithoutPratitya.MMK2418 ∧ ¬ emptinessWithoutPratitya.Pratitya ∧
      ¬ emptinessWithoutPratitya.AllEmpty := by
  refine ⟨rfl, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro n m _ h
    cases h
  · intro x hx
    obtain ⟨_, hne⟩ := hx
    change x ≠ jnana at hne
    simp [emptinessWithoutPratitya, Emptiness.toData, classicalEmptiness,
      mvClassical, hne]
  · intro h
    obtain ⟨_, impossible⟩ := h jnana
    exact impossible rfl
  · intro h
    have bad := h jnana
    simp [emptinessWithoutPratitya, Emptiness.toData, classicalEmptiness,
      mvClassical] at bad

/-- The selected two-premise set is deletion-minimal over the shared
classical base, even when the two unused auxiliary premises are retained. -/
theorem emptiness_core_relative_independence :
    (∃ M : EmptinessData Bool, M.logic = mvClassical ∧
      M.Samvrti ∧ M.NidanaDep ∧ M.Pratitya ∧
      ¬ M.MMK2418 ∧ ¬ M.AllEmpty) ∧
    (∃ M : EmptinessData Bool, M.logic = mvClassical ∧
      M.Samvrti ∧ M.NidanaDep ∧ M.MMK2418 ∧
      ¬ M.Pratitya ∧ ¬ M.AllEmpty) :=
  ⟨⟨emptinessWithoutMMK, emptiness_without_mmk⟩,
    ⟨emptinessWithoutPratitya, emptiness_without_pratitya⟩⟩

def fdeGlutEmptiness : Emptiness TV4 where
  logic := mvFDE
  sv _ := B
  appears _ := T
  dep _ _ := True
  mmk_24_18 _ := rfl
  pratitya _ := ⟨jnana, trivial⟩
  samvrti _ := rfl
  nidana_dep _ := trivial

def fdeAllGlutEmptiness : Emptiness TV4 where
  logic := mvFDE
  sv _ := B
  appears _ := B
  dep _ _ := True
  mmk_24_18 _ := rfl
  pratitya _ := ⟨jnana, trivial⟩
  samvrti _ := rfl
  nidana_dep _ := trivial

theorem cl_readings_coincide (E : Emptiness Bool)
    (hDes : ∀ b, E.logic.designated b ↔ b = true)
    (hNeg : ∀ b, E.logic.neg b = Bool.not b)
    (hConj : ∀ a b, E.logic.mconj a b = Bool.and a b)
    (x : Dharma) :
    (E.RIdentity x ↔ E.RMutual x) ∧
      (E.RMutual x ↔ E.RNotsep x) := by
  have happ : E.appears x = true := (hDes _).mp (E.samvrti x)
  have hemp : E.logic.neg (E.sv x) = true :=
    (hDes _).mp (E.sarva_dharma_sunya x)
  cases ha : E.appears x <;> cases hs : E.sv x <;>
    simp_all [Emptiness.RIdentity, Emptiness.RMutual, Emptiness.RNotsep,
      Emptiness.sunya]

theorem fde_R_mutual_not_identity (x : Dharma) :
    fdeGlutEmptiness.RMutual x ∧
      ¬ fdeGlutEmptiness.RIdentity (sk Skandha.rupa) := by
  simp [Emptiness.RMutual, Emptiness.RIdentity, Emptiness.sunya,
    fdeGlutEmptiness, mvFDE, neg4, mk, tr, fa]

theorem fde_R_identity_not_notsep (x : Dharma) :
    fdeAllGlutEmptiness.RIdentity x ∧
      ¬ fdeAllGlutEmptiness.RNotsep (sk Skandha.rupa) := by
  simp [Emptiness.RIdentity, Emptiness.RNotsep, Emptiness.sunya,
    fdeAllGlutEmptiness, mvFDE, neg4, conj4, mk, tr, fa]

theorem emptiness_consistent_cl : Nonempty (Emptiness Bool) :=
  ⟨classicalEmptiness⟩

theorem emptiness_consistent_fde : Nonempty (Emptiness TV4) :=
  ⟨fdeGlutEmptiness⟩

theorem cl_emptiness_nonvacuous : Nonempty (Emptiness Bool) :=
  emptiness_consistent_cl

/-! ## HS10: the six extremes and two meanings of "neither" -/

inductive Anta where
  | arise | cease | defiled | pure | increase | decrease
  deriving DecidableEq, Repr

open Anta

def anta_pairs : List (Anta × Anta) :=
  [(arise, cease), (defiled, pure), (increase, decrease)]

theorem anta_pairs_length : anta_pairs.length = 3 := by decide

theorem anta_pairs_distinct_members :
    ∀ p ∈ anta_pairs, p.1 ≠ p.2 := by decide

theorem anta_pairs_sides_disjoint :
    ∀ x, x ∈ anta_pairs.map Prod.fst → x ∉ anta_pairs.map Prod.snd := by
  decide

theorem anta_pairs_cover (x : Anta) :
    x ∈ anta_pairs.map Prod.fst ∨ x ∈ anta_pairs.map Prod.snd := by
  cases x <;> decide

def hs10Formula (a : Atom) : Fm Atom :=
  conj (neg (atom a)) (neg (neg (atom a)))

theorem hs10_cl_contradictory_unsat (v : Atom → Bool) (a : Atom) :
    ¬ mvClassical.sat v (hs10Formula a) := by
  cases h : v a <;>
    simp [MVLogic.sat, MVLogic.eval, mvClassical, mvEval, hs10Formula, h]

theorem hs10_fde_formula_iff_B (v : Atom → TV4) (a : Atom) :
    mvFDE.sat v (hs10Formula a) ↔ v a = B := by
  cases h : v a <;>
    simp [MVLogic.sat, MVLogic.eval, mvFDE, mvEval, hs10Formula,
      h, neg4, conj4, mk, tr, fa]

def hs10Neither (v : Atom → TV4) (a : Atom) : Prop :=
  ¬ mvFDE.designated (v a) ∧ ¬ mvFDE.designated (neg4 (v a))

theorem hs10_cl_neither_impossible (a : Atom) :
    ¬ ∃ v : Atom → Bool, v a = false ∧ Bool.not (v a) = false := by
  intro h
  rcases h with ⟨v, hv, hnv⟩
  simp [hv] at hnv

theorem hs10_fde_neither_iff_N (v : Atom → TV4) (a : Atom) :
    hs10Neither v a ↔ v a = N := by
  cases h : v a <;>
    simp [hs10Neither, mvFDE, h, neg4, mk, tr, fa]

def hs10Neither5 (v : Atom → TV5) (a : Atom) : Prop :=
  ¬ mvFDE5.designated (v a) ∧ ¬ mvFDE5.designated (neg5 (v a))

theorem hs10_fde5_neither_iff_N_or_E (v : Atom → TV5) (a : Atom) :
    hs10Neither5 v a ↔ v a = TV5.fin N ∨ v a = TV5.E := by
  cases h : v a with
  | fin x =>
      cases x <;>
        simp [hs10Neither5, mvFDE5, des5, h, neg5, neg4, mk, tr, fa]
  | E => simp [hs10Neither5, mvFDE5, des5, h, neg5]

end BuddhistComparativeLogic
