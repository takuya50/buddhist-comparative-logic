/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Dharmakirti

/-!
# The subject excluded from the comparison classes

Audit of the existing Hetucakra encoding, not a historical refutation of
Dignaga. Its similar and dissimilar classes exclude the subject. This file
shows exactly why their three marks do not by themselves decide that
subject: deleting its thesis preserves the marks. Under the marks, the
additional global pervasion premise is equivalent to the subject's thesis.
-/

namespace BuddhistComparativeLogic.InferenceScope

open Hetucakra

def Pervasion (a : Hetucakra.Anumana D) : Prop := ∀ x, a.reason x → a.sadhya x

theorem pervasion_splits_at_subject (a : Hetucakra.Anumana D) :
    Pervasion a ↔
      (∀ x, x ≠ a.paksa → a.reason x → a.sadhya x) ∧
      (a.reason a.paksa → a.sadhya a.paksa) := by
  constructor
  · exact fun h => ⟨fun x _ => h x, h a.paksa⟩
  · rintro ⟨off, atSubject⟩ x hx
    by_cases heq : x = a.paksa
    · subst x
      exact atSubject hx
    · exact off x heq hx

theorem pervasion_iff_thesis_under_marks (a : Hetucakra.Anumana D)
    (marks : a.trairupya) : Pervasion a ↔ a.sadhya a.paksa := by
  constructor
  · exact fun h => h a.paksa marks.1
  · intro thesis
    exact (pervasion_splits_at_subject a).mpr
      ⟨a.vyatireka_gives_vyapti_off_paksa marks.2.2, fun _ => thesis⟩

theorem uniformity_iff_thesis_under_marks (a : Hetucakra.Anumana D)
    (marks : a.trairupya) :
    ((∀ x, x ≠ a.paksa → a.reason x → a.sadhya x) →
      a.reason a.paksa → a.sadhya a.paksa) ↔ a.sadhya a.paksa := by
  exact ⟨a.sound_under_uniformity marks, fun h _ _ => h⟩

/-- Delete only the thesis at the disputed subject, leaving reasons and
all comparison subjects untouched. No decidable equality is required. -/
def eraseSubject (a : Hetucakra.Anumana D) : Hetucakra.Anumana D where
  paksa := a.paksa
  reason := a.reason
  sadhya x := x ≠ a.paksa ∧ a.sadhya x

theorem erase_preserves_marks (a : Hetucakra.Anumana D) (h : a.trairupya) :
    (eraseSubject a).trairupya := by
  refine ⟨h.1, ?_, ?_⟩
  · obtain ⟨y, hy, hr⟩ := h.2.1
    exact ⟨y, ⟨hy.1, hy.1, hy.2⟩, hr⟩
  · intro y hy hr
    apply h.2.2 y ⟨hy.1, ?_⟩ hr
    intro hs
    exact hy.2 ⟨hy.1, hs⟩

theorem erase_refutes_subject (a : Hetucakra.Anumana D) :
    ¬ (eraseSubject a).sadhya (eraseSubject a).paksa := fun h => h.1 rfl

/-- A systematic countermodel transformation, rather than a single
smoke/fire example. This diagnoses the quantifier scope of this encoding. -/
theorem marks_allow_false_subject (a : Hetucakra.Anumana D) (h : a.trairupya) :
    (eraseSubject a).paksa = a.paksa ∧
    (eraseSubject a).reason = a.reason ∧
    (eraseSubject a).trairupya ∧
    (eraseSubject a).wheelVerdict = .valid ∧
    ¬ (eraseSubject a).sadhya (eraseSubject a).paksa := by
  have marks := erase_preserves_marks a h
  exact ⟨rfl, rfl, marks, (eraseSubject a).wheel_valid_iff.mpr marks.2,
    erase_refutes_subject a⟩

end BuddhistComparativeLogic.InferenceScope
