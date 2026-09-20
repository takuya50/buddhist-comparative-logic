/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceModes

/-!
# Coverage, universalization, and countermodels for dependence modes

The local inference from a witnessed variation to absence of own-being does
not by itself yield `all dharmas are empty`.  This module states the missing
coverage premise for any selected collection of modes, proves the scoped and
universal conclusions, and supplies finite countermodels for the converses
and for cross-mode identification.
-/

namespace BuddhistComparativeLogic.DependenceModes

namespace Model

variable (M : Model D)

/-- A subject is covered when an allowed dependence mode supplies an edge. -/
def CoveredBy (allowed : Mode → Prop) (x : D) : Prop :=
  ∃ m, allowed m ∧ ∃ y, M.DependsAt m y x

/-- Universal coverage is a separate premise about every subject. -/
def Covers (allowed : Mode → Prop) : Prop :=
  ∀ x, M.CoveredBy allowed x

def CoversAt (m : Mode) : Prop :=
  ∀ x, ∃ y, M.DependsAt m y x

def AllModes : Mode → Prop := fun _ => True

def UniversalCoverage : Prop := M.Covers AllModes

/-- The local conclusion has exactly the scope of the supplied coverage. -/
theorem empty_of_covered (criteria : M.OwnBeingCriteria)
    {allowed : Mode → Prop} {x : D} (covered : M.CoveredBy allowed x) :
    ¬ M.own x := by
  obtain ⟨m, _, y, edge⟩ := covered
  exact M.dependence_excludes_own_at m
    (OwnBeingCriteria.at M criteria m) x y edge

theorem empty_on_covered_domain (criteria : M.OwnBeingCriteria)
    (domain : D → Prop) (allowed : Mode → Prop)
    (coverage : ∀ x, domain x → M.CoveredBy allowed x) :
    ∀ x, domain x → ¬ M.own x :=
  fun x hx => M.empty_of_covered criteria (coverage x hx)

/-- Universal emptiness follows only after every subject is covered. -/
theorem all_empty_of_coverage (criteria : M.OwnBeingCriteria)
    {allowed : Mode → Prop} (coverage : M.Covers allowed) :
    ∀ x, ¬ M.own x :=
  fun x => M.empty_of_covered criteria (coverage x)

theorem all_empty_of_universal_coverage (criteria : M.OwnBeingCriteria)
    (coverage : M.UniversalCoverage) : ∀ x, ¬ M.own x :=
  M.all_empty_of_coverage criteria coverage

theorem coversAt_implies_coverage (m : Mode) (coverage : M.CoversAt m) :
    M.Covers (fun n => n = m) := by
  intro x
  obtain ⟨y, edge⟩ := coverage x
  exact ⟨m, rfl, y, edge⟩

theorem all_empty_of_single_mode_coverage (criteria : M.OwnBeingCriteria)
    (m : Mode) (coverage : M.CoversAt m) : ∀ x, ¬ M.own x :=
  M.all_empty_of_coverage criteria (M.coversAt_implies_coverage m coverage)

/-- Adding admitted modes preserves coverage. -/
theorem coverage_mono {small large : Mode → Prop}
    (hsub : ∀ m, small m → large m) (coverage : M.Covers small) :
    M.Covers large := by
  intro x
  obtain ⟨m, hm, y, edge⟩ := coverage x
  exact ⟨m, hsub m hm, y, edge⟩

end Model

end BuddhistComparativeLogic.DependenceModes

namespace BuddhistComparativeLogic.DependenceCoverage

open DependenceModes

/-! ## Mode-separating finite models -/

/-- Only `active` controls the manifestation of `false`; `true` is its
support and is itself invariant.  The same construction can isolate each of
the three modes. -/
def isolated (active : Mode) : DependenceModes.Model Bool where
  Context _ := Bool
  support m c y :=
    if m = active then
      if y then c else true
    else false
  manifest m c x :=
    if x then true
    else if m = active then c else false
  own x := x = true

theorem isolated_criteria (active : Mode) :
    (isolated active).OwnBeingCriteria := by
  constructor <;> intro x hx c d <;> cases hx <;> rfl

theorem isolated_active_edge (active : Mode) :
    (isolated active).DependsAt active true false := by
  refine ⟨by decide, false, true, ?_, ?_, ?_⟩
  · simp [isolated]
  · intro z hz
    cases z with
    | false => simp [isolated]
    | true => exact False.elim (hz rfl)
  · simp [isolated]

theorem isolated_no_edge_at_inactive (active m : Mode) (hm : m ≠ active) :
    ¬ (∃ y x, (isolated active).DependsAt m y x) := by
  rintro ⟨y, x, _, c, d, changed, _, _⟩
  exact changed (by simp [isolated, hm])

theorem isolated_no_edge_into_own_subject (active : Mode) :
    ¬ (∃ m y, (isolated active).DependsAt m y true) := by
  rintro ⟨m, y, _, c, d, _, _, changed⟩
  exact changed (by simp [isolated])

theorem causal_edge_is_not_mereological_or_conceptual :
    (isolated .causal).CausallyDepends true false ∧
    ¬ (isolated .causal).MereologicallyDepends true false ∧
    ¬ (isolated .causal).ConceptuallyDepends true false := by
  refine ⟨isolated_active_edge .causal, ?_, ?_⟩
  · intro edge
    exact isolated_no_edge_at_inactive .causal .mereological (by decide)
      ⟨true, false, edge⟩
  · intro edge
    exact isolated_no_edge_at_inactive .causal .conceptual (by decide)
      ⟨true, false, edge⟩

theorem mereological_edge_is_not_causal_or_conceptual :
    (isolated .mereological).MereologicallyDepends true false ∧
    ¬ (isolated .mereological).CausallyDepends true false ∧
    ¬ (isolated .mereological).ConceptuallyDepends true false := by
  refine ⟨isolated_active_edge .mereological, ?_, ?_⟩
  · intro edge
    exact isolated_no_edge_at_inactive .mereological .causal (by decide)
      ⟨true, false, edge⟩
  · intro edge
    exact isolated_no_edge_at_inactive .mereological .conceptual (by decide)
      ⟨true, false, edge⟩

theorem conceptual_edge_is_not_causal_or_mereological :
    (isolated .conceptual).ConceptuallyDepends true false ∧
    ¬ (isolated .conceptual).CausallyDepends true false ∧
    ¬ (isolated .conceptual).MereologicallyDepends true false := by
  refine ⟨isolated_active_edge .conceptual, ?_, ?_⟩
  · intro edge
    exact isolated_no_edge_at_inactive .conceptual .causal (by decide)
      ⟨true, false, edge⟩
  · intro edge
    exact isolated_no_edge_at_inactive .conceptual .mereological (by decide)
      ⟨true, false, edge⟩

/-- A mixed model covers `false` causally and `true` mereologically.  It
shows that family-level coverage need not come from one global mode. -/
def mixed : DependenceModes.Model Bool where
  Context _ := Bool
  support m c y :=
    match m with
    | .causal => if y then c else true
    | .mereological => if y then true else c
    | .conceptual => false
  manifest m c x :=
    match m with
    | .causal => if x then true else c
    | .mereological => if x then c else true
    | .conceptual => false
  own _ := False

theorem mixed_criteria : mixed.OwnBeingCriteria := by
  constructor <;> intro x hx <;> exact False.elim hx

theorem mixed_causal_edge : mixed.CausallyDepends true false := by
  refine ⟨by decide, false, true, ?_, ?_, ?_⟩
  · decide
  · intro z hz
    cases z with
    | false => rfl
    | true => exact False.elim (hz rfl)
  · decide

theorem mixed_mereological_edge :
    mixed.MereologicallyDepends false true := by
  refine ⟨by decide, false, true, ?_, ?_, ?_⟩
  · decide
  · intro z hz
    cases z with
    | false => exact False.elim (hz rfl)
    | true => rfl
  · decide

theorem mixed_universal_coverage : mixed.UniversalCoverage := by
  intro x
  cases x with
  | false => exact ⟨.causal, trivial, true, mixed_causal_edge⟩
  | true => exact ⟨.mereological, trivial, false, mixed_mereological_edge⟩

theorem mixed_all_empty_via_coverage : ∀ x, ¬ mixed.own x :=
  mixed.all_empty_of_universal_coverage mixed_criteria
    mixed_universal_coverage

/-- A local edge and all three own-being criteria leave an uncovered subject
with own-being.  This is the countermodel to automatic universalization. -/
theorem incomplete_coverage_allows_own (active : Mode) :
    (isolated active).OwnBeingCriteria ∧
    (isolated active).DependsAt active true false ∧
    (isolated active).own true ∧
    ¬ (isolated active).UniversalCoverage ∧
    ¬ (∀ x, ¬ (isolated active).own x) := by
  refine ⟨isolated_criteria active, isolated_active_edge active, rfl, ?_, ?_⟩
  · intro coverage
    obtain ⟨m, _, y, edge⟩ := coverage true
    exact isolated_no_edge_into_own_subject active ⟨m, y, edge⟩
  · intro allEmpty
    exact allEmpty true rfl

/-! ## Independence of primitive own-being from the edge relation -/

/-- An inert model can independently assign either truth value to primitive
own-being while keeping every mode observationally constant. -/
def inert (ownValue : Prop) : DependenceModes.Model Unit where
  Context _ := Unit
  support _ _ _ := false
  manifest _ _ _ := false
  own _ := ownValue

theorem inert_criteria (ownValue : Prop) :
    (inert ownValue).OwnBeingCriteria := by
  constructor <;> intro x hx c d <;> rfl

theorem inert_has_no_edges (ownValue : Prop) :
    ¬ (∃ m y x, (inert ownValue).DependsAt m y x) := by
  rintro ⟨m, y, x, _, c, d, changed, _, _⟩
  exact changed rfl

/-- Identical empty dependence families satisfy the criteria with and
without primitive own-being.  Hence the criteria do not define `own` as
the complement of dependence. -/
theorem independence_does_not_decide_own :
    (inert True).OwnBeingCriteria ∧ (inert True).own () ∧
    ¬ (∃ m y x, (inert True).DependsAt m y x) ∧
    (inert False).OwnBeingCriteria ∧ ¬ (inert False).own () ∧
    ¬ (∃ m y x, (inert False).DependsAt m y x) :=
  ⟨inert_criteria True, trivial, inert_has_no_edges True,
    inert_criteria False, (fun h => h), inert_has_no_edges False⟩

/-- If own-being is instead assigned to every subject, the active variation
still exists but the appropriate invariance criterion fails. -/
def permissive (active : Mode) : DependenceModes.Model Bool :=
  { isolated active with own := fun _ => True }

theorem permissive_active_edge (active : Mode) :
    (permissive active).DependsAt active true false := by
  simpa [permissive, DependenceModes.Model.DependsAt] using
    isolated_active_edge active

theorem invariance_criteria_are_substantive (active : Mode) :
    (permissive active).DependsAt active true false ∧
    (permissive active).own false ∧
    ¬ (permissive active).OwnBeingCriteria := by
  refine ⟨permissive_active_edge active, trivial, ?_⟩
  intro criteria
  have fixed := DependenceModes.Model.OwnBeingCriteria.at
    (permissive active) criteria active false trivial false true
  simp [permissive, isolated] at fixed

/-- Universal emptiness can hold in an inert model with no coverage.  Thus
coverage is sufficient for the dependence argument, not a definition of
emptiness and not a logically necessary condition for it. -/
theorem emptiness_does_not_imply_coverage :
    (∀ x, ¬ (inert False).own x) ∧
    ¬ (inert False).UniversalCoverage := by
  constructor
  · exact fun _ h => h
  · intro coverage
    obtain ⟨m, _, y, edge⟩ := coverage ()
    exact inert_has_no_edges False ⟨m, y, (), edge⟩

end BuddhistComparativeLogic.DependenceCoverage
