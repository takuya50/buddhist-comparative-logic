/- SPDX-License-Identifier: Apache-2.0 -/

/-!
# Paired extension questions in the Yamaka style

This module formalizes a small, computational audit inspired by the paired
questions of the Pali *Yamaka*.  It checks the two directions `A ⊆ B` and
`B ⊆ A` separately on an explicitly enumerated finite domain, and classifies
their extensions as equal, left proper, right proper, or incomparable.

This is not a claim that the historical *Yamaka* is a four-valued
propositional logic.  The four constructors below classify the application
ranges of two terms.  The report also retains counterexample objects, so the
proper-subset and incomparable cases have inspectable boundaries rather than
being bare labels.
-/

namespace BuddhistComparativeLogic.Yamaka

universe u

/-! ## Finite extensions and directed counterexamples -/

/-- Two decidable term extensions over an explicitly complete finite domain.
The list is data used by the executable checker; `complete` prevents an
unlisted object from escaping the audit. -/
structure ExtensionAudit (Object : Type u) where
  domain : List Object
  complete : ∀ object, object ∈ domain
  nodup : domain.Nodup
  left : Object → Bool
  right : Object → Bool

namespace ExtensionAudit

variable {Object : Type u} (audit : ExtensionAudit Object)

def LeftApplies (object : Object) : Prop := audit.left object = true

def RightApplies (object : Object) : Prop := audit.right object = true

/-- The first object accepted by `positive` and rejected by `negative`, if
there is one in the supplied enumeration. -/
def firstDifference (domain : List Object)
    (positive negative : Object → Bool) : Option Object :=
  match domain with
  | [] => none
  | object :: rest =>
      if positive object && !negative object then
        some object
      else
        firstDifference rest positive negative

private theorem firstDifference_some_sound
    {domain : List Object} {positive negative : Object → Bool}
    {object : Object}
    (found : firstDifference domain positive negative = some object) :
    positive object = true ∧ negative object = false ∧ object ∈ domain := by
  induction domain with
  | nil => simp [firstDifference] at found
  | cons head tail ih =>
      cases positiveHead : positive head with
      | false =>
          cases negativeHead : negative head with
          | false =>
              have tailFound :
                  firstDifference tail positive negative = some object := by
                simpa [firstDifference, positiveHead, negativeHead] using found
              have result := ih tailFound
              exact ⟨result.1, result.2.1, by simp [result.2.2]⟩
          | true =>
              have tailFound :
                  firstDifference tail positive negative = some object := by
                simpa [firstDifference, positiveHead, negativeHead] using found
              have result := ih tailFound
              exact ⟨result.1, result.2.1, by simp [result.2.2]⟩
      | true =>
          cases negativeHead : negative head with
          | false =>
              have same : head = object := by
                simpa [firstDifference, positiveHead, negativeHead] using found
              subst object
              exact ⟨positiveHead, negativeHead, by simp⟩
          | true =>
              have result := ih (by
                simpa [firstDifference, positiveHead, negativeHead] using found)
              exact ⟨result.1, result.2.1, by simp [result.2.2]⟩

private theorem firstDifference_none_iff
    (domain : List Object) (positive negative : Object → Bool) :
    firstDifference domain positive negative = none ↔
      ∀ object ∈ domain, positive object = true → negative object = true := by
  induction domain with
  | nil => simp [firstDifference]
  | cons head tail ih =>
      cases positiveHead : positive head <;>
        cases negativeHead : negative head <;>
          simp [firstDifference, positiveHead, negativeHead, ih]

/-- A left-only object refutes `left ⊆ right`. -/
def leftOnly : Option Object :=
  firstDifference audit.domain audit.left audit.right

/-- A right-only object refutes `right ⊆ left`. -/
def rightOnly : Option Object :=
  firstDifference audit.domain audit.right audit.left

def LeftSubsetRight : Prop :=
  ∀ object, audit.LeftApplies object → audit.RightApplies object

def RightSubsetLeft : Prop :=
  ∀ object, audit.RightApplies object → audit.LeftApplies object

theorem leftOnly_some_sound {object : Object}
    (found : audit.leftOnly = some object) :
    audit.LeftApplies object ∧ ¬ audit.RightApplies object := by
  have result := firstDifference_some_sound found
  exact ⟨result.1, by simpa [RightApplies] using result.2.1⟩

theorem rightOnly_some_sound {object : Object}
    (found : audit.rightOnly = some object) :
    audit.RightApplies object ∧ ¬ audit.LeftApplies object := by
  have result := firstDifference_some_sound found
  exact ⟨result.1, by simpa [LeftApplies] using result.2.1⟩

theorem leftOnly_none_iff_subset :
    audit.leftOnly = none ↔ audit.LeftSubsetRight := by
  rw [leftOnly, firstDifference_none_iff]
  constructor
  · intro checked object leftObject
    exact checked object (audit.complete object) leftObject
  · intro included object _inDomain leftObject
    exact included object leftObject

theorem rightOnly_none_iff_subset :
    audit.rightOnly = none ↔ audit.RightSubsetLeft := by
  rw [rightOnly, firstDifference_none_iff]
  constructor
  · intro checked object rightObject
    exact checked object (audit.complete object) rightObject
  · intro included object _inDomain rightObject
    exact included object rightObject

theorem leftOnly_ne_none_iff_exists :
    audit.leftOnly ≠ none ↔
      ∃ object, audit.LeftApplies object ∧ ¬ audit.RightApplies object := by
  constructor
  · intro present
    cases found : audit.leftOnly with
    | none => exact False.elim (present found)
    | some object =>
        exact ⟨object, audit.leftOnly_some_sound found⟩
  · rintro ⟨object, leftObject, notRight⟩ absent
    exact notRight
      (audit.leftOnly_none_iff_subset.mp absent object leftObject)

theorem rightOnly_ne_none_iff_exists :
    audit.rightOnly ≠ none ↔
      ∃ object, audit.RightApplies object ∧ ¬ audit.LeftApplies object := by
  constructor
  · intro present
    cases found : audit.rightOnly with
    | none => exact False.elim (present found)
    | some object =>
        exact ⟨object, audit.rightOnly_some_sound found⟩
  · rintro ⟨object, rightObject, notLeft⟩ absent
    exact notLeft
      (audit.rightOnly_none_iff_subset.mp absent object rightObject)

/-! ## A classifier with retained boundary witnesses -/

inductive ExtensionRelation where
  | equal
  | leftProper
  | rightProper
  | incomparable
  deriving DecidableEq, Repr

/-- The report is computational data.  Its two optional objects are concrete
failures of the directed inclusions; the category is read from their joint
shape. -/
structure BoundaryReport (Object : Type u) where
  leftOnly : Option Object
  rightOnly : Option Object
  deriving Repr

def boundaryReport : BoundaryReport Object where
  leftOnly := audit.leftOnly
  rightOnly := audit.rightOnly

def BoundaryReport.relation (report : BoundaryReport Object) :
    ExtensionRelation :=
  match report.leftOnly, report.rightOnly with
  | none, none => .equal
  | none, some _ => .leftProper
  | some _, none => .rightProper
  | some _, some _ => .incomparable

/-- Executable four-way classification of the two extensions. -/
def classify : ExtensionRelation := audit.boundaryReport.relation

theorem classify_equal_iff :
    audit.classify = .equal ↔
      audit.LeftSubsetRight ∧ audit.RightSubsetLeft := by
  rw [← audit.leftOnly_none_iff_subset,
    ← audit.rightOnly_none_iff_subset]
  cases leftCase : audit.leftOnly <;>
    cases rightCase : audit.rightOnly <;>
      simp [classify, boundaryReport, BoundaryReport.relation,
        leftCase, rightCase]

theorem classify_leftProper_iff :
    audit.classify = .leftProper ↔
      audit.LeftSubsetRight ∧
        ∃ object, audit.RightApplies object ∧ ¬ audit.LeftApplies object := by
  rw [← audit.leftOnly_none_iff_subset,
    ← audit.rightOnly_ne_none_iff_exists]
  cases leftCase : audit.leftOnly <;>
    cases rightCase : audit.rightOnly <;>
      simp [classify, boundaryReport, BoundaryReport.relation,
        leftCase, rightCase]

theorem classify_rightProper_iff :
    audit.classify = .rightProper ↔
      audit.RightSubsetLeft ∧
        ∃ object, audit.LeftApplies object ∧ ¬ audit.RightApplies object := by
  rw [← audit.rightOnly_none_iff_subset,
    ← audit.leftOnly_ne_none_iff_exists]
  cases leftCase : audit.leftOnly <;>
    cases rightCase : audit.rightOnly <;>
      simp [classify, boundaryReport, BoundaryReport.relation,
        leftCase, rightCase]

theorem classify_incomparable_iff :
    audit.classify = .incomparable ↔
      (∃ object, audit.LeftApplies object ∧ ¬ audit.RightApplies object) ∧
        ∃ object, audit.RightApplies object ∧ ¬ audit.LeftApplies object := by
  rw [← audit.leftOnly_ne_none_iff_exists,
    ← audit.rightOnly_ne_none_iff_exists]
  cases leftCase : audit.leftOnly <;>
    cases rightCase : audit.rightOnly <;>
      simp [classify, boundaryReport, BoundaryReport.relation,
        leftCase, rightCase]

/-- The returned enum is total: every audit receives one of the four cases. -/
theorem classification_complete :
    audit.classify = .equal ∨ audit.classify = .leftProper ∨
      audit.classify = .rightProper ∨ audit.classify = .incomparable := by
  cases audit.classify <;> simp

/-- The four result constructors are pairwise exclusive. -/
theorem classification_exclusive {first second : ExtensionRelation}
    (firstResult : audit.classify = first)
    (secondResult : audit.classify = second) : first = second := by
  rw [← firstResult, ← secondResult]

/-- The classifier is a decision procedure for each named result. -/
instance classificationDecidable (relation : ExtensionRelation) :
    Decidable (audit.classify = relation) := inferInstance

end ExtensionAudit

/-! ## Finite separation of equality from one-way inclusion -/

inductive PairObject where
  | first
  | second
  deriving DecidableEq, Repr

open PairObject ExtensionAudit

def equalAudit : ExtensionAudit PairObject where
  domain := [.first, .second]
  complete := by intro object; cases object <;> simp
  nodup := by decide
  left := fun object => object == .first
  right := fun object => object == .first

/-- The left term applies only to `first`, while the right term applies to
both objects. -/
def properAudit : ExtensionAudit PairObject where
  domain := [.first, .second]
  complete := by intro object; cases object <;> simp
  nodup := by decide
  left := fun object => object == .first
  right := fun _ => true

/-- Reversing the preceding predicates realizes a proper left-side surplus. -/
def rightProperAudit : ExtensionAudit PairObject where
  domain := [.first, .second]
  complete := by intro object; cases object <;> simp
  nodup := by decide
  left := fun _ => true
  right := fun object => object == .first

/-- Each term accepts a different object, so both directed inclusions fail. -/
def incomparableAudit : ExtensionAudit PairObject where
  domain := [.first, .second]
  complete := by intro object; cases object <;> simp
  nodup := by decide
  left := fun object => object == .first
  right := fun object => object == .second

theorem reports_retain_proper_boundary :
    properAudit.boundaryReport.leftOnly = none ∧
      properAudit.boundaryReport.rightOnly = some .second ∧
      properAudit.RightApplies .second ∧
      ¬ properAudit.LeftApplies .second := by
  simp [ExtensionAudit.boundaryReport, ExtensionAudit.leftOnly,
    ExtensionAudit.rightOnly, ExtensionAudit.firstDifference,
    properAudit, ExtensionAudit.LeftApplies, ExtensionAudit.RightApplies]

/-- The remaining two categories also have inhabited finite reports.  The
incomparable report retains one concrete witness against each inclusion. -/
theorem right_proper_and_incomparable_boundaries_nonvacuous :
    rightProperAudit.classify = .rightProper /\
      rightProperAudit.boundaryReport.leftOnly = some .second /\
      rightProperAudit.boundaryReport.rightOnly = none /\
      incomparableAudit.classify = .incomparable /\
      incomparableAudit.boundaryReport.leftOnly = some .first /\
      incomparableAudit.boundaryReport.rightOnly = some .second /\
      (incomparableAudit.LeftApplies .first /\
        ¬ incomparableAudit.RightApplies .first) /\
      (incomparableAudit.RightApplies .second /\
        ¬ incomparableAudit.LeftApplies .second) := by
  simp [ExtensionAudit.classify, ExtensionAudit.boundaryReport,
    ExtensionAudit.BoundaryReport.relation, ExtensionAudit.leftOnly,
    ExtensionAudit.rightOnly, ExtensionAudit.firstDifference,
    rightProperAudit, incomparableAudit, ExtensionAudit.LeftApplies,
    ExtensionAudit.RightApplies]

/-- Both examples satisfy the same directed question `left ⊆ right`, but one
has equal extensions and the other has a strict right-side surplus.  Thus a
single Yamaka-style direction cannot distinguish equality from proper
inclusion. -/
theorem one_direction_does_not_distinguish_equality_from_proper_inclusion :
    equalAudit.LeftSubsetRight ∧ equalAudit.classify = .equal ∧
      properAudit.LeftSubsetRight ∧ properAudit.classify = .leftProper := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · intro object leftObject
    simpa [equalAudit, ExtensionAudit.LeftApplies,
      ExtensionAudit.RightApplies] using leftObject
  · intro object _leftObject
    simp [properAudit, ExtensionAudit.RightApplies]

end BuddhistComparativeLogic.Yamaka
