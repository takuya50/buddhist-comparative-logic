/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation
import BuddhistComparativeLogic.Buddhist.HeartSutra.Dharma

/-!
# The mantra and its epithets

This is the Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Mantra.thy`.  Invocation is represented
as a distinct kind of utterance, so the model records explicitly that the
heart mantra is not a truth-apt formula.
-/

namespace BuddhistComparativeLogic

inductive MantraWord where
  | gate | paragate | parasamgate | bodhi_w | svaha
  deriving DecidableEq, Repr, Inhabited

open MantraWord

def heart_mantra : List MantraWord :=
  [gate, gate, paragate, parasamgate, bodhi_w, svaha]

theorem heart_mantra_shape :
    heart_mantra.length = 6 ∧
    heart_mantra.head? = some gate ∧
    heart_mantra.getLast? = some svaha := by
  decide

inductive Epithet where
  | MahaMantra | MahaVidyaMantra | AnuttaraMantra | AsamasamaMantra
  deriving DecidableEq, Repr, Inhabited

open Epithet

def epithets : List Epithet :=
  [MahaMantra, MahaVidyaMantra, AnuttaraMantra, AsamasamaMantra]

theorem epithets_univ : (∀ x : Epithet, x ∈ epithets) ∧ epithets.Nodup := by
  constructor
  · intro x
    cases x <;> decide
  · decide

theorem epithets_four : epithets.length = 4 := by
  decide

inductive Utterance (α : Type) where
  | Assert : Fm α → Utterance α
  | Invoke : List MantraWord → Utterance α
  deriving Repr

open Utterance

def truth_apt : Utterance α → Bool
  | Assert _ => true
  | Invoke _ => false

theorem hs29_mantra_not_truth_apt :
    truth_apt (Invoke heart_mantra : Utterance Atom) = false := by
  rfl

end BuddhistComparativeLogic
