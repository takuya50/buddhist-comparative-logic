/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation
import BuddhistComparativeLogic.Buddhist.Madhyamaka.Standpoints

/-!
# Vigrahavyāvartanī: empty statements and “I have no thesis”

Lean counterpart of `isabelle/Buddhist/Madhyamaka/Madhyamaka_Vigrahavyavartani.thy`.  The results remain conditional on
an explicit model.  Emptiness is applied to the statement itself without
turning it into a truth predicate, and the no-thesis claim is located at a
silent standpoint.
-/

namespace BuddhistComparativeLogic

inductive VDharma (δ : Type) where
  | dharma : δ → VDharma δ
  | statement
  | objection
  deriving DecidableEq, Repr

structure Vigraha (Val Dharma : Type) where
  designated : Val → Prop
  neg : Val → Val
  arisen : VDharma Dharma → Val
  works : VDharma Dharma → Prop
  negInvolutive : ∀ w, neg (neg w) = w
  arisenAll : ∀ x, designated (arisen x)

namespace Vigraha

variable (M : Vigraha Val Dharma)

def svabhava (x : VDharma Dharma) : Val := M.neg (M.arisen x)

def empty (x : VDharma Dharma) : Prop := M.designated (M.neg (M.svabhava x))

theorem all_empty (x : VDharma Dharma) : M.empty x := by
  unfold empty svabhava
  rw [M.negInvolutive]
  exact M.arisenAll x

theorem sunyata_sunyata : M.empty (.statement : VDharma Dharma) := M.all_empty _

def opponentPremise : Prop := ∀ x, M.works x → M.designated (M.svabhava x)

def nagarjunaPremise : Prop := ∀ x, M.designated (M.arisen x) → M.works x

theorem nagarjuna_reply (h : M.nagarjunaPremise) :
    M.works (.statement : VDharma Dharma) ∧ M.empty .statement := by
  exact ⟨h _ (M.arisenAll _), M.sunyata_sunyata⟩

end Vigraha

def classicalVigraha (Dharma : Type) (works : VDharma Dharma → Prop) :
    Vigraha Bool Dharma where
  designated b := b = true
  neg := Bool.not
  arisen _ := true
  works := works
  negInvolutive w := by cases w <;> rfl
  arisenAll _ := rfl

theorem classical_no_svabhava (works : VDharma Dharma → Prop) (x : VDharma Dharma) :
    ¬ (classicalVigraha Dharma works).designated
      ((classicalVigraha Dharma works).svabhava x) := by
  simp [classicalVigraha, Vigraha.svabhava]

theorem opponent_premise_self_refuting
    (works : VDharma Dharma → Prop)
    (h : (classicalVigraha Dharma works).opponentPremise)
    (x : VDharma Dharma) : ¬ works x := by
  intro hw
  exact classical_no_svabhava works x (h x hw)

theorem opponent_premise_kills_objection
    (works : VDharma Dharma → Prop)
    (h : (classicalVigraha Dharma works).opponentPremise) :
    ¬ works (.objection : VDharma Dharma) :=
  opponent_premise_self_refuting works h _

structure FDEVigraha (Dharma : Type) where
  arisen : VDharma Dharma → TV4
  works : VDharma Dharma → Prop
  arisenDesignated : ∀ x, tr (arisen x) = true

namespace FDEVigraha

variable (M : FDEVigraha Dharma)

private theorem designated_both_imp_B (x : TV4)
    (ht : tr x = true) (hf : tr (neg4 x) = true) : x = .B := by
  cases x <;> simp [tr, neg4, BuddhistComparativeLogic.mk, fa] at ht hf ⊢

def model : Vigraha TV4 Dharma where
  designated x := tr x = true
  neg := neg4
  arisen := M.arisen
  works := M.works
  negInvolutive w := by cases w <;> rfl
  arisenAll := M.arisenDesignated

theorem vv_fde_glut
    (hopp : M.model.opponentPremise) (x : VDharma Dharma) (hw : M.works x) :
    M.arisen x = .B := by
  have ha := M.arisenDesignated x
  have hs := hopp x hw
  have hs' : tr (neg4 (M.arisen x)) = true := by
    simpa [model, Vigraha.svabhava] using hs
  exact designated_both_imp_B (M.arisen x) ha hs'

end FDEVigraha

def glutVigraha (Dharma : Type) : FDEVigraha Dharma where
  arisen _ := .B
  works _ := True
  arisenDesignated _ := rfl

theorem vv_fde_glut_model (Dharma : Type) :
    (glutVigraha Dharma).model.opponentPremise ∧
    (glutVigraha Dharma).model.empty (.statement : VDharma Dharma) ∧
    (glutVigraha Dharma).works .statement := by
  simp [glutVigraha, FDEVigraha.model, Vigraha.opponentPremise,
    Vigraha.svabhava, Vigraha.empty, neg4, mk, tr, fa]

inductive VigrahaAtom where | thesis deriving DecidableEq, Repr

def vigrahaAsserted : Satya2 → Fm VigrahaAtom → Prop
  | .samvrti, .atom .thesis => True
  | _, _ => False

def vigrahaStandpoint : StandpointFrame Satya2 VigrahaAtom :=
  ⟨twoTruthsAccess, vigrahaAsserted⟩

theorem no_thesis_consistent :
    vigrahaStandpoint.convTrue .samvrti (.atom .thesis) ∧
    vigrahaStandpoint.ultDenies .samvrti (.atom .thesis) ∧
    vigrahaStandpoint.prasangika .paramartha ∧
    vigrahaStandpoint.extNeg .paramartha (.atom .thesis) := by
  constructor
  · trivial
  constructor
  · change ∀ w, twoTruthsAccess .samvrti w → ¬ vigrahaAsserted w (.atom .thesis)
    intro w hw
    cases w <;> simp [twoTruthsAccess, vigrahaAsserted] at hw ⊢
  constructor
  · change ∀ X, ¬ vigrahaAsserted .paramartha X
    intro X
    simp [vigrahaAsserted]
  · change ¬ vigrahaAsserted .paramartha (.atom .thesis)
    simp [vigrahaAsserted]

end BuddhistComparativeLogic
