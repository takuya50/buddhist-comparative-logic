/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.EmptinessInference

/-!
# An argument from conditional variation to absence of own-being

Reconstruction motivated by MMK 15.1-2 and 24.18-19, not a textual identity
claim. Own-being is a primitive predicate. The interpretive premise says
that it entails invariance of presence across the admitted contexts. A
dependency is witnessed by two contexts differing in exactly one other
condition, with different presence of the subject. This derives the
previous audit's exclusion law rather than assuming that law directly.

The invariance premise and the choice of admitted contexts are still
modeling commitments. No universal dependency is assumed by ContextModel.
-/

namespace BuddhistComparativeLogic.DependentOrigination

structure ContextModel (C : Type u) (D : Type v) where
  enabled : C → D → Bool
  present : C → D → Bool
  own : D → Prop

namespace ContextModel

variable (M : ContextModel C D)

def InvariantOwn : Prop :=
  ∀ x, M.own x → ∀ c d, M.present c x = M.present d x

/-- A change of one other condition, keeping all remaining conditions fixed. -/
def depends (y x : D) : Prop :=
  y ≠ x ∧ ∃ c d,
    M.enabled c y ≠ M.enabled d y ∧
    (∀ z, z ≠ y → M.enabled c z = M.enabled d z) ∧
    M.present c x ≠ M.present d x

def toDependence : AssumptionAudit.Dependence D where
  dep := M.depends
  own := M.own

theorem variation_refutes_own (h : M.InvariantOwn) {x : D} {c d : C}
    (changes : M.present c x ≠ M.present d x) : ¬ M.own x := by
  intro own
  exact changes (h x own c d)

theorem dependence_excludes_own (h : M.InvariantOwn) : M.toDependence.Exclusion := by
  intro x y edge
  obtain ⟨_, c, d, _, _, changes⟩ := edge
  exact M.variation_refutes_own h changes

/-- Pointwise derivation: no universal emptiness or arising premise. -/
theorem empty_of_dependency (h : M.InvariantOwn) {x y : D}
    (edge : M.depends y x) : M.toDependence.emptyOf x :=
  M.toDependence.empty_of_arisen (M.dependence_excludes_own h) ⟨y, edge⟩

/-- Universalization is an extra premise, visibly separate from the
argument that excludes own-being for an individual dependent subject. -/
theorem all_empty_of_all_dependent (h : M.InvariantOwn)
    (all : ∀ x, ∃ y, M.depends y x) : ∀ x, M.toDependence.emptyOf x :=
  M.toDependence.all_empty (M.dependence_excludes_own h) all

/-- The resulting exclusion law is the pervasion of the existing inference
adapter, so the contextual argument feeds the actual reasoning interface. -/
theorem contextual_pervasion (h : M.InvariantOwn) (x : D) :
    (EmptinessInference.ofDependence M.toDependence x).vyapti :=
  M.dependence_excludes_own h

theorem contextual_inference (h : M.InvariantOwn) {x y : D}
    (edge : M.depends y x) :
    (EmptinessInference.ofDependence M.toDependence x).sadhya x :=
  EmptinessInference.empty_via_explicit_pervasion M.toDependence x
    (M.dependence_excludes_own h) ⟨y, edge⟩

end ContextModel

/-- false is the dependent subject, true is its condition. Presence and
enabled conditions have different roles; the condition itself stays present. -/
def switched : ContextModel Bool Bool where
  enabled c y := if y then c else true
  present c x := if x then true else c
  own x := x = true

theorem switched_invariance : switched.InvariantOwn := by
  intro x hx c d
  cases hx
  rfl

theorem switched_dependency : switched.depends true false := by
  refine ⟨by decide, false, true, ?_, ?_, ?_⟩
  · decide
  · intro z hz
    cases z with
    | false => rfl
    | true => exact False.elim (hz rfl)
  · decide

/-- Absence of own-being is compatible with actual presence. -/
theorem empty_yet_present :
    switched.toDependence.emptyOf false ∧ switched.present true false = true :=
  ⟨switched.empty_of_dependency switched_invariance switched_dependency, rfl⟩

/-- One dependent subject does not imply that every subject is empty. -/
theorem universalization_needs_a_premise :
    switched.InvariantOwn ∧ switched.depends true false ∧ switched.own true :=
  ⟨switched_invariance, switched_dependency, rfl⟩

def switchedWithOwn : ContextModel Bool Bool := { switched with own := fun _ => True }

/-- The observation of variation alone cannot settle an independent
own-being predicate; the invariance criterion really is used. -/
theorem invariance_needed :
    switchedWithOwn.depends true false ∧ switchedWithOwn.own false ∧
    ¬ switchedWithOwn.InvariantOwn := by
  refine ⟨switched_dependency, trivial, ?_⟩
  intro h
  have bad : false = true := h false trivial false true
  cases bad

def absent : ContextModel Unit Unit where
  enabled _ _ := false
  present _ _ := false
  own _ := False

/-- Emptiness alone supplies neither presence nor a causal witness. -/
theorem empty_does_not_supply_occurrence_or_dependence :
    absent.InvariantOwn ∧ absent.toDependence.emptyOf () ∧
    absent.present () () = false ∧ ¬ (∃ y, absent.depends y ()) := by
  refine ⟨fun _ h => False.elim h, fun h => h, rfl, ?_⟩
  rintro ⟨⟨⟩, h⟩
  exact h.1 rfl

end BuddhistComparativeLogic.DependentOrigination
