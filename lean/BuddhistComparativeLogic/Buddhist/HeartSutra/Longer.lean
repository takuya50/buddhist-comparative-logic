/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation
import BuddhistComparativeLogic.Buddhist.Madhyamaka.Standpoints
import BuddhistComparativeLogic.Buddhist.HeartSutra.Coverage

/-!
# The longer Heart Sutra recension

Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_LongerRecension.thy`.  It records the six-part narrative
frame, separates speech acts from assertoric content, and realizes the silent
samādhi and the speaking scene as two standpoints.
-/

namespace BuddhistComparativeLogic

inductive FramePart where
  | nidana
  | enterSamadhi
  | question
  | answer
  | endorsement
  | rejoicing
  deriving DecidableEq, Repr

open FramePart

def longFrame : List FramePart :=
  [.nidana, .enterSamadhi, .question, .answer, .endorsement, .rejoicing]

theorem frame_length : longFrame.length = 6 := by decide
theorem frame_distinct : longFrame.Nodup := by decide
theorem frame_complete (f : FramePart) : f ∈ longFrame := by cases f <;> decide

inductive SpeechKind where
  | narration | silence | asking | instruction | approval | joy
  deriving DecidableEq, Repr

def kindOf : FramePart → SpeechKind
  | .nidana => .narration
  | .enterSamadhi => .silence
  | .question => .asking
  | .answer => .instruction
  | .endorsement => .approval
  | .rejoicing => .joy

theorem kindOf_injective : Function.Injective kindOf := by
  intro f g h
  cases f <;> cases g <;> simp [kindOf] at h ⊢

inductive LongAtom where | core deriving DecidableEq, Repr

def frameContent : FramePart → Option (Utterance LongAtom)
  | .answer => some (.Assert (.atom .core))
  | _ => none

def assertoric (f : FramePart) : Bool :=
  match frameContent f with
  | none => false
  | some u => truth_apt u

theorem only_answer_assertoric (f : FramePart) :
    assertoric f = true ↔ f = .answer := by cases f <;> decide

theorem answer_is_core :
    frameContent .answer = some (.Assert (.atom .core)) := rfl

def longRecension : List FramePart × List Clause := (longFrame, body)

theorem core_unchanged :
    longRecension.2 = body ∧ (longRecension.2.map char_count).sum = 262 := by
  exact ⟨rfl, body_262⟩

def frameStatus : FramePart → Status
  | .nidana => .Noted
  | .enterSamadhi => .Proved
  | .question => .Noted
  | .answer => .Proved
  | .endorsement => .Proved
  | .rejoicing => .Noted

theorem frame_coverage_complete (f : FramePart) : frameStatus f ≠ .Missing := by
  cases f <;> decide

theorem frame_proved_count :
    (longFrame.filter (frameStatus · == .Proved)).length = 3 := by decide

theorem frame_noted_count :
    (longFrame.filter (frameStatus · == .Noted)).length = 3 := by decide

inductive LongStandpoint where | inSamadhi | speaking
  deriving DecidableEq, Repr

def longAccess : LongStandpoint → LongStandpoint → Prop
  | .speaking, .inSamadhi => True
  | _, _ => False

def longAsserted : LongStandpoint → Fm LongAtom → Prop
  | .speaking, .atom .core => True
  | _, _ => False

def longStandpoint : StandpointFrame LongStandpoint LongAtom :=
  ⟨longAccess, longAsserted⟩

theorem samadhi_realizes_no_thesis :
    longStandpoint.convTrue .speaking (.atom .core) ∧
    longStandpoint.ultDenies .speaking (.atom .core) ∧
    longStandpoint.prasangika .inSamadhi ∧
    longStandpoint.extNeg .inSamadhi (.atom .core) := by
  constructor
  · change longAsserted .speaking (.atom .core)
    trivial
  constructor
  · change ∀ w, longAccess .speaking w → ¬ longAsserted w (.atom .core)
    intro w hw
    cases w <;> simp [longAccess, longAsserted] at hw ⊢
  constructor
  · change ∀ X, ¬ longAsserted .inSamadhi X
    intro X
    simp [longAsserted]
  · change ¬ longAsserted .inSamadhi (.atom .core)
    simp [longAsserted]

def assertedBy : FramePart → Fm LongAtom → Prop
  | .answer, .atom .core => True
  | .endorsement, .atom .core => True
  | _, _ => False

theorem endorsement_adds_nothing : assertedBy .endorsement = assertedBy .answer := by
  funext X
  cases X <;> simp [assertedBy]

theorem silence_asserts_nothing (X : Fm LongAtom) : ¬ assertedBy .enterSamadhi X := by
  cases X <;> simp [assertedBy]

/-- Predicate-set form of Isabelle's union theorem: a formula is asserted
by some part of the six-part frame exactly when it belongs to the assertion
set of the speaking standpoint. -/
theorem frame_assertions_are_the_speaking_standpoint :
    (fun X => ∃ f ∈ longFrame, assertedBy f X) =
      longAsserted .speaking := by
  funext X
  cases X with
  | atom a =>
      cases a
      simp [longFrame, assertedBy, longAsserted]
  | neg X => simp [longFrame, assertedBy, longAsserted]
  | conj X Y => simp [longFrame, assertedBy, longAsserted]
  | disj X Y => simp [longFrame, assertedBy, longAsserted]

end BuddhistComparativeLogic
