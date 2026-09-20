/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Jizang

/-!
# Standpoint semantics for Buddhist two-truths readings

Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_StandpointSemantics.thy`.  An assertion belongs to a
standpoint rather than receiving a global truth value.  This is the small
piece of structure used by the two-truths, Jizang, Vigrahavyāvartanī, and
long-recension modules.
-/

namespace BuddhistComparativeLogic

structure StandpointFrame (World Atom : Type) where
  accessible : World → World → Prop
  asserted : World → Fm Atom → Prop

namespace StandpointFrame

variable {World Atom : Type} (M : StandpointFrame World Atom)

def convTrue (w : World) (X : Fm Atom) : Prop := M.asserted w X

def ultDenies (w : World) (X : Fm Atom) : Prop :=
  ∀ w', M.accessible w w' → ¬ M.asserted w' X

def extNeg (w : World) (X : Fm Atom) : Prop := ¬ M.asserted w X

def mpClosed (w : World) : Prop :=
  ∀ X Y, M.asserted w X →
    M.asserted w (.disj (.neg X) Y) → M.asserted w Y

def prasangika (w : World) : Prop := ∀ X, ¬ M.asserted w X

theorem prasangika_extNeg {w : World} (h : M.prasangika w) (X : Fm Atom) :
    M.extNeg w X := h X

theorem ultDenies_vacuous {w : World} (h : ∀ w', ¬ M.accessible w w') (X : Fm Atom) :
    M.ultDenies w X := by
  intro w' hw
  exact (h w' hw).elim

theorem prasangika_no_thesis {w : World} (h : M.prasangika w) (X : Fm Atom) :
    M.extNeg w X :=
  M.prasangika_extNeg h X

theorem prasangika_mp_closed {w : World} (h : M.prasangika w) :
    M.mpClosed w := by
  intro X _ hX _
  exact (h X hX).elim

theorem terminal_denies {w : World} (h : ∀ w', ¬ M.accessible w w')
    (X : Fm Atom) : M.ultDenies w X :=
  M.ultDenies_vacuous h X

end StandpointFrame

inductive Satya2 where
  | samvrti
  | paramartha
  deriving DecidableEq, Repr

open Satya2

def twoTruthsAccess : Satya2 → Satya2 → Prop
  | .samvrti, .paramartha => True
  | _, _ => False

theorem twoTruthsAccess_iff (w w' : Satya2) :
    twoTruthsAccess w w' ↔ w = samvrti ∧ w' = paramartha := by
  cases w <;> cases w' <;> simp [twoTruthsAccess]

/-! ## Two standpoints reproduce the locally consistent two truths -/

inductive HAtom (Dharma : Type) where
  | appearance : Dharma → HAtom Dharma
  | ownBeing : Dharma → HAtom Dharma
  deriving Repr

def twoPointFrame (asserted : Satya2 → Fm (HAtom Dharma) → Prop) :
    StandpointFrame Satya2 (HAtom Dharma) :=
  ⟨twoTruthsAccess, asserted⟩

noncomputable def ttVal
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop)
    (t : Satya2) (x : Dharma) : TV4 :=
  @ite TV4 (asserted t (.atom (.appearance x)))
    (Classical.propDecidable _) .T .F

noncomputable def ttSv
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop)
    (t : Satya2) (x : Dharma) : TV4 :=
  @ite TV4 (asserted t (.atom (.ownBeing x)))
    (Classical.propDecidable _) .T .F

/-- The assumptions of Isabelle's `two_truths_fde`, unfolded for the
assertion-induced values above.  Keeping this predicate here avoids reversing
the existing `BuddhistComparativeLogic.Buddhist.Madhyamaka.TwoTruths` → `BuddhistComparativeLogic.Buddhist.Madhyamaka.Standpoints` dependency. -/
def twoPointsFDE
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop) : Prop :=
  (∀ x, mvFDE.designated (ttVal asserted .samvrti x)) ∧
  (∀ x, mvFDE.designated (neg4 (ttSv asserted .paramartha x))) ∧
  (∀ x, ¬ mvFDE.designated (neg4 (ttVal asserted .samvrti x))) ∧
  (∀ x, ¬ mvFDE.designated (ttSv asserted .paramartha x))

theorem ttVal_designated_iff
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop)
    (t : Satya2) (x : Dharma) :
    mvFDE.designated (ttVal asserted t x) ↔
      asserted t (.atom (.appearance x)) := by
  classical
  by_cases h : asserted t (.atom (.appearance x)) <;>
    simp [ttVal, h, mvFDE, tr]

theorem ttVal_consistent_iff
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop)
    (t : Satya2) (x : Dharma) :
    (¬ mvFDE.designated (neg4 (ttVal asserted t x))) ↔
      asserted t (.atom (.appearance x)) := by
  classical
  by_cases h : asserted t (.atom (.appearance x)) <;>
    simp [ttVal, h, mvFDE, neg4, mk, tr, fa]

theorem ttSv_empty_iff
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop)
    (t : Satya2) (x : Dharma) :
    mvFDE.designated (neg4 (ttSv asserted t x)) ↔
      ¬ asserted t (.atom (.ownBeing x)) := by
  classical
  by_cases h : asserted t (.atom (.ownBeing x)) <;>
    simp [ttSv, h, mvFDE, neg4, mk, tr, fa]

theorem ttSv_consistent_iff
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop)
    (t : Satya2) (x : Dharma) :
    (¬ mvFDE.designated (ttSv asserted t x)) ↔
      ¬ asserted t (.atom (.ownBeing x)) := by
  classical
  by_cases h : asserted t (.atom (.ownBeing x)) <;>
    simp [ttSv, h, mvFDE, tr]

theorem twoPoint_ultDenies_iff
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop) (x : Dharma) :
    (twoPointFrame asserted).ultDenies .samvrti (.atom (.ownBeing x)) ↔
      ¬ asserted .paramartha (.atom (.ownBeing x)) := by
  constructor
  · intro h hasserted
    exact h .paramartha trivial hasserted
  · intro h w hw
    have hw' := (twoTruthsAccess_iff .samvrti w).mp hw
    rcases hw' with ⟨_, rfl⟩
    exact h

theorem two_points_is_two_truths
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop) :
    twoPointsFDE asserted ↔
      (∀ x, (twoPointFrame asserted).convTrue .samvrti
        (.atom (.appearance x))) ∧
      (∀ x, (twoPointFrame asserted).ultDenies .samvrti
        (.atom (.ownBeing x))) := by
  constructor
  · rintro ⟨hconv, hult, _, _⟩
    constructor
    · intro x
      exact (ttVal_designated_iff asserted .samvrti x).mp (hconv x)
    · intro x
      apply (twoPoint_ultDenies_iff asserted x).mpr
      exact (ttSv_empty_iff asserted .paramartha x).mp (hult x)
  · rintro ⟨hconv, hult⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      apply (ttVal_designated_iff asserted .samvrti x).mpr
      exact hconv x
    · intro x
      apply (ttSv_empty_iff asserted .paramartha x).mpr
      exact (twoPoint_ultDenies_iff asserted x).mp (hult x)
    · intro x
      apply (ttVal_consistent_iff asserted .samvrti x).mpr
      exact hconv x
    · intro x
      apply (ttSv_consistent_iff asserted .paramartha x).mpr
      exact (twoPoint_ultDenies_iff asserted x).mp (hult x)

/-! ## Four standpoints separate Jizang's four tiers -/

def jzPositions (a : α) (k : Nat) : Fm α → Prop :=
  fun X => X = jzConv (.atom a) k ∨ X = jzUlt (.atom a) k

def jzAsserted (a : α) (k : Nat) : Fm α → Prop :=
  if k < 4 then jzPositions a k else fun _ => False

def jzAccess (k k' : Nat) : Prop := k' = k + 1

def jzFrame (a : α) : StandpointFrame Nat α :=
  ⟨jzAccess, jzAsserted a⟩

theorem conv_not_ult (a : α) (k k' : Nat) :
    jzConv (.atom a) k ≠ jzUlt (.atom a) k' := by
  cases k <;> simp [jzConv, jzUlt]

theorem conv_inj (a : α) {k k' : Nat}
    (h : jzConv (.atom a) k = jzConv (.atom a) k') : k = k' := by
  apply Classical.byContradiction
  intro hne
  have hs := congrArg fmSize h
  by_cases hlt : k < k'
  · exact (Nat.ne_of_lt (jz_conv_size_mono (.atom a) hlt)) hs
  · have hgt : k' < k := by omega
    exact (Nat.ne_of_lt (jz_conv_size_mono (.atom a) hgt)) hs.symm

theorem ult_inj (a : α) {k k' : Nat}
    (h : jzUlt (.atom a) k = jzUlt (.atom a) k') : k = k' := by
  apply Classical.byContradiction
  intro hne
  exact jz_tiers_distinct (.atom a) hne h

theorem jizang_tiers_separated (a : α) {k k' : Nat}
    (hk : k < 4) (hk' : k' < 4) (hne : k ≠ k') :
    jzAsserted a k ≠ jzAsserted a k' := by
  intro heq
  have hmem : jzAsserted a k (jzConv (.atom a) k) := by
    simp [jzAsserted, hk, jzPositions]
  have hmem' : jzAsserted a k' (jzConv (.atom a) k) := by
    rw [← heq]
    exact hmem
  have hcases :
      jzConv (.atom a) k = jzConv (.atom a) k' ∨
        jzConv (.atom a) k = jzUlt (.atom a) k' := by
    simpa [jzAsserted, hk', jzPositions] using hmem'
  rcases hcases with hconv | hult
  · exact hne (conv_inj a hconv)
  · exact conv_not_ult a k k' hult

theorem each_tier_denied (a : α) {k : Nat} {X : Fm α}
    (hX : jzAsserted a k X) : (jzFrame a).ultDenies k X := by
  intro k' hstep hX'
  change k' = k + 1 at hstep
  subst k'
  change jzAsserted a (k + 1) X at hX'
  by_cases hk : k < 4
  · have hhere : X = jzConv (.atom a) k ∨ X = jzUlt (.atom a) k := by
      simpa [jzAsserted, hk, jzPositions] using hX
    by_cases hnext : k + 1 < 4
    · have hthere :
          X = jzConv (.atom a) (k + 1) ∨
            X = jzUlt (.atom a) (k + 1) := by
        simpa [jzAsserted, hnext, jzPositions] using hX'
      rcases hhere with hhere | hhere
      · rcases hthere with hthere | hthere
        · have : k = k + 1 := conv_inj a (hhere.symm.trans hthere)
          omega
        · exact conv_not_ult a k (k + 1) (hhere.symm.trans hthere)
      · rcases hthere with hthere | hthere
        · exact conv_not_ult a (k + 1) k (hthere.symm.trans hhere)
        · have : k = k + 1 := ult_inj a (hhere.symm.trans hthere)
          omega
    · simp [jzAsserted, hnext] at hX'
  · simp [jzAsserted, hk] at hX

theorem final_silence (a : α) :
    jzAsserted a 4 = (fun _ => False) ∧ (jzFrame a).prasangika 4 := by
  constructor
  · funext X
    simp [jzAsserted]
  · change ∀ X, ¬ jzAsserted a 4 X
    intro X
    simp [jzAsserted]

theorem separation_beyond_values
    (v : α → TV4) (a : α) {n m : Nat}
    (hn : n + 1 < 4) (hm : m + 1 < 4) (hne : n ≠ m) :
    jzAsserted a (n + 1) ≠ jzAsserted a (m + 1) ∧
      ev4 v (jzUlt (.atom a) (n + 1)) =
        ev4 v (jzUlt (.atom a) (m + 1)) := by
  constructor
  · apply jizang_tiers_separated a hn hm
    omega
  · exact (jz_fde_ult_stabilizes v (.atom a) n).trans
      (jz_fde_ult_stabilizes v (.atom a) m).symm

inductive ThreeTruth where
  | empty
  | conventional
  | middle
  deriving DecidableEq, Repr

open ThreeTruth

def interfused (asserted : World → Fm ThreeTruth → Prop) : Prop :=
  ∀ w, asserted w (.atom .empty) ∧ asserted w (.atom .conventional) ∧
    asserted w (.atom .middle)

theorem interfused_no_ultimate_denial
    (M : StandpointFrame World ThreeTruth)
    (h : interfused M.asserted)
    (w : World) (s : ThreeTruth) :
    M.ultDenies w (.atom s) ↔ ∀ w', ¬ M.accessible w w' := by
  constructor
  · intro hd w' hr
    have hs : M.asserted w' (.atom s) := by
      rcases h w' with ⟨he, hc, hm⟩
      cases s
      · exact he
      · exact hc
      · exact hm
    exact hd w' hr hs
  · intro hn w' hr
    exact (hn w' hr).elim

abbrev yuanrong := @interfused

theorem yuanrong_no_ultimate_denial
    (M : StandpointFrame World ThreeTruth)
    (h : yuanrong M.asserted)
    (w : World) (s : ThreeTruth) :
    M.ultDenies w (.atom s) ↔ ∀ w', ¬ M.accessible w w' :=
  interfused_no_ultimate_denial M h w s

/-! ## Tiantai's separated three truths -/

inductive ThreeTruthStage where
  | conventional | empty | middle
  deriving DecidableEq, Repr

def gerekenAccess : ThreeTruthStage → ThreeTruthStage → Prop
  | .conventional, .empty => True
  | .empty, .middle => True
  | _, _ => False

def gerekenAsserted : ThreeTruthStage → Fm ThreeTruth → Prop
  | .conventional, .atom .conventional => True
  | .empty, .atom .empty => True
  | .middle, .atom .middle => True
  | _, _ => False

def gerekenFrame : StandpointFrame ThreeTruthStage ThreeTruth :=
  ⟨gerekenAccess, gerekenAsserted⟩

theorem gereki_hierarchical :
    gerekenFrame.convTrue .conventional (.atom .conventional) ∧
      gerekenFrame.ultDenies .conventional (.atom .conventional) ∧
      gerekenFrame.convTrue .empty (.atom .empty) ∧
      gerekenFrame.ultDenies .empty (.atom .empty) := by
  refine ⟨trivial, ?_, trivial, ?_⟩
  · intro w hw hasserted
    cases w with
    | conventional =>
        change False at hw
        exact hw.elim
    | empty =>
        change False at hasserted
        exact hasserted.elim
    | middle =>
        change False at hw
        exact hw.elim
  · intro w hw hasserted
    cases w with
    | conventional =>
        change False at hw
        exact hw.elim
    | empty =>
        change False at hw
        exact hw.elim
    | middle =>
        change False at hasserted
        exact hasserted.elim

theorem gereki_not_yuanrong : ¬ yuanrong gerekenAsserted := by
  intro h
  have hs := h .conventional
  simpa [gerekenAsserted] using hs.1

end BuddhistComparativeLogic
