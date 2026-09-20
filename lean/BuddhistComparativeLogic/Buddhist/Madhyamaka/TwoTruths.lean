/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.MMK
import BuddhistComparativeLogic.Buddhist.Madhyamaka.Standpoints

/-!
# The two truths as two evaluation points

Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_TwoTruths.thy`.  `Satya2` is shared with the
standpoint semantics so later modules can combine the truth-value and
assertion-level accounts without duplicate types.
-/

namespace BuddhistComparativeLogic

open TV4 Dharma Satya2

structure TwoTruths (V : Type u) where
  logic : MVLogic V
  val : Satya2 → Dharma → V
  svAt : Satya2 → Dharma → V
  conv_appears : ∀ x, logic.designated (val samvrti x)
  ult_empty : ∀ x, logic.designated (logic.neg (svAt paramartha x))

namespace TwoTruths

variable (T : TwoTruths V)

def sunyaAt (t : Satya2) (x : Dharma) : V :=
  T.logic.neg (T.svAt t x)

def XIdentity (x : Dharma) : Prop :=
  T.val samvrti x = T.sunyaAt paramartha x

def XMutual (x : Dharma) : Prop :=
  T.logic.designated (T.val samvrti x) ↔
    T.logic.designated (T.sunyaAt paramartha x)

def XNotsep (x : Dharma) : Prop :=
  ¬ T.logic.designated
      (T.logic.mconj (T.val samvrti x) (T.svAt paramartha x)) ∧
    ¬ T.logic.designated
      (T.logic.mconj (T.sunyaAt paramartha x)
        (T.logic.neg (T.val samvrti x)))

theorem X_mutual_always (x : Dharma) : T.XMutual x := by
  constructor
  · intro _
    exact T.ult_empty x
  · intro _
    exact T.conv_appears x

end TwoTruths

/-- Every one-level emptiness model gives a flat two-truths model. -/
def Emptiness.flat (E : Emptiness V) : TwoTruths V where
  logic := E.logic
  val _ := E.appears
  svAt _ := E.sv
  conv_appears := E.samvrti
  ult_empty := fun x => E.sarva_dharma_sunya x

/-- FDE two-truths semantics with local consistency at both points. -/
structure TwoTruthsFDE where
  val : Satya2 → Dharma → TV4
  svAt : Satya2 → Dharma → TV4
  conv_appears : ∀ x, mvFDE.designated (val samvrti x)
  ult_empty : ∀ x, mvFDE.designated (neg4 (svAt paramartha x))
  conv_consistent : ∀ x, ¬ mvFDE.designated (neg4 (val samvrti x))
  ult_consistent : ∀ x, ¬ mvFDE.designated (svAt paramartha x)

namespace TwoTruthsFDE

/-- Turn the assertion-induced conditions from `BuddhistComparativeLogic.Buddhist.Madhyamaka.Standpoints`
into the existing locally consistent two-truths record.  The value
functions are exactly `ttVal` and `ttSv`, rather than merely extensionally
related replacements. -/
noncomputable def ofStandpoint
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop)
    (h : twoPointsFDE asserted) : TwoTruthsFDE where
  val := ttVal asserted
  svAt := ttSv asserted
  conv_appears := h.1
  ult_empty := h.2.1
  conv_consistent := h.2.2.1
  ult_consistent := h.2.2.2

/-- Direct bridge between the predicate presentation used by standpoint
semantics and the record presentation used by the two-truths development.
The existential is over a record whose two semantic functions are fixed,
so this is equivalence of the four conditions, not just model existence. -/
theorem twoPointsFDE_iff_twoTruthsFDE_record
    (asserted : Satya2 → Fm (HAtom Dharma) → Prop) :
    twoPointsFDE asserted ↔
      ∃ T : TwoTruthsFDE,
        T.val = ttVal asserted ∧ T.svAt = ttSv asserted := by
  constructor
  · intro h
    exact ⟨ofStandpoint asserted h, rfl, rfl⟩
  · rintro ⟨T, hval, hsv⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hval]
      exact T.conv_appears
    · rw [← hsv]
      exact T.ult_empty
    · rw [← hval]
      exact T.conv_consistent
    · rw [← hsv]
      exact T.ult_consistent

variable (T : TwoTruthsFDE)

def toTwoTruths : TwoTruths TV4 where
  logic := mvFDE
  val := T.val
  svAt := T.svAt
  conv_appears := T.conv_appears
  ult_empty := T.ult_empty

theorem conv_T (x : Dharma) : T.val samvrti x = TV4.T := by
  have hp := T.conv_appears x
  have hn := T.conv_consistent x
  change tr (T.val samvrti x) = true at hp
  change ¬ tr (neg4 (T.val samvrti x)) = true at hn
  cases h : T.val samvrti x with
  | T => rfl
  | B =>
      exfalso
      apply hn
      rw [h]
      rfl
  | N =>
      exfalso
      rw [h] at hp
      exact Bool.noConfusion hp
  | F =>
      exfalso
      rw [h] at hp
      exact Bool.noConfusion hp

theorem ult_F (x : Dharma) : T.svAt paramartha x = TV4.F := by
  have hp := T.ult_empty x
  have hn := T.ult_consistent x
  change tr (neg4 (T.svAt paramartha x)) = true at hp
  change ¬ tr (T.svAt paramartha x) = true at hn
  cases h : T.svAt paramartha x with
  | T =>
      exfalso
      apply hn
      rw [h]
      rfl
  | B =>
      exfalso
      apply hn
      rw [h]
      rfl
  | N =>
      exfalso
      rw [h] at hp
      exact Bool.noConfusion hp
  | F => rfl

theorem hs06_two_truths (x : Dharma) : T.toTwoTruths.XNotsep x := by
  unfold TwoTruths.XNotsep TwoTruths.sunyaAt
  change
    (¬ mvFDE.designated (conj4 (T.val samvrti x) (T.svAt paramartha x))) ∧
    ¬ mvFDE.designated
      (conj4 (neg4 (T.svAt paramartha x)) (neg4 (T.val samvrti x)))
  rw [T.conv_T x, T.ult_F x]
  change (¬ tr (conj4 TV4.T TV4.F) = true) ∧
    ¬ tr (conj4 (neg4 TV4.F) (neg4 TV4.T)) = true
  decide

theorem hs07_two_truths (x : Dharma) : T.toTwoTruths.XIdentity x := by
  unfold TwoTruths.XIdentity TwoTruths.sunyaAt
  change T.val samvrti x = neg4 (T.svAt paramartha x)
  rw [T.conv_T x, T.ult_F x]
  rfl

theorem two_truths_readings_coincide (x : Dharma) :
    T.toTwoTruths.XIdentity x ∧ T.toTwoTruths.XMutual x ∧
      T.toTwoTruths.XNotsep x :=
  ⟨T.hs07_two_truths x, T.toTwoTruths.X_mutual_always x,
    T.hs06_two_truths x⟩

end TwoTruthsFDE

def ttConvGlut : TwoTruths TV4 where
  logic := mvFDE
  val _ _ := TV4.B
  svAt _ _ := TV4.F
  conv_appears _ := rfl
  ult_empty _ := rfl

theorem ult_glut_breaks_hs06 (x : Dharma) :
    ¬ fdeGlutEmptiness.flat.XNotsep x := by
  simp [TwoTruths.XNotsep, TwoTruths.sunyaAt, Emptiness.flat,
    fdeGlutEmptiness, mvFDE, neg4, conj4, mk, tr, fa]

theorem conv_glut_breaks_hs06 (x : Dharma) :
    ¬ ttConvGlut.XNotsep x := by
  simp [TwoTruths.XNotsep, TwoTruths.sunyaAt, ttConvGlut,
    mvFDE, neg4, conj4, mk, tr, fa]

def twoTruthsFDEConsistent : TwoTruthsFDE where
  val _ _ := TV4.T
  svAt _ _ := TV4.F
  conv_appears _ := rfl
  ult_empty _ := rfl
  conv_consistent _ := by
    change ¬ tr (neg4 TV4.T) = true
    decide
  ult_consistent _ := by
    change ¬ tr TV4.F = true
    decide

theorem two_truths_fde_consistent : Nonempty TwoTruthsFDE :=
  ⟨twoTruthsFDEConsistent⟩

def infoJoin (x y : TV4) : TV4 :=
  mk (tr x || tr y) (fa x || fa y)

theorem info_join_T_F : infoJoin TV4.T TV4.F = TV4.B := rfl

end BuddhistComparativeLogic
