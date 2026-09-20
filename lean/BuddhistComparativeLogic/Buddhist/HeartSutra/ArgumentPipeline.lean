/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.BeliefRevision
import BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceCoverage
import BuddhistComparativeLogic.Buddhist.Madhyamaka.FourfoldCausation

/-!
# Composing the philosophical and practical arguments

The earlier modules prove the stages separately.  This file states the two
bridges required to compose them: recognition turns a proved absence of
own-being into an initial cognitive insight, and a revision policy turns that
insight into a bounded change of grasping, fear and suffering.  Keeping both
bridges as fields prevents an ontological conclusion from silently becoming a
psychological law.
-/

namespace BuddhistComparativeLogic.ArgumentPipeline

open DependenceModes
open BeliefRevision

/-- A local dependence argument connected to an evidence-sensitive path. -/
structure DependencePracticeBridge
    (M : DependenceModes.Model D) (E : EvidenceProcess S)
    (subject : D) (initial : S) : Prop where
  criteria : M.OwnBeingCriteria
  release : E.ReleaseConditions
  recognizes : ¬ M.own subject → E.insight initial

theorem dependence_to_bounded_release
    {M : DependenceModes.Model D} {E : EvidenceProcess S}
    {subject source : D} {initial : S}
    (bridge : DependencePracticeBridge M E subject initial)
    (mode : Mode) (edge : M.DependsAt mode source subject)
    (n : Nat) (bound : E.grasp initial + 2 ≤ n) :
    ¬ M.own subject ∧
      E.grasp (E.toPath.run initial n) = 0 ∧
      E.fear (E.toPath.run initial n) = 0 ∧
      E.suffering (E.toPath.run initial n) = 0 := by
  have empty : ¬ M.own subject :=
    M.empty_of_mode_dependency mode
      (DependenceModes.Model.OwnBeingCriteria.at M bridge.criteria mode) edge
  exact ⟨empty,
    E.eventual_release_from_revision bridge.release
      (bridge.recognizes empty) n bound⟩

theorem covered_domain_to_bounded_release
    {M : DependenceModes.Model D} {E : EvidenceProcess S}
    {initial : D → S} {allowed : Mode → Prop}
    (criteria : M.OwnBeingCriteria) (coverage : M.Covers allowed)
    (release : E.ReleaseConditions)
    (recognizes : ∀ x, ¬ M.own x → E.insight (initial x))
    (n : D → Nat) (bound : ∀ x, E.grasp (initial x) + 2 ≤ n x) :
    ∀ x, ¬ M.own x ∧
      E.grasp (E.toPath.run (initial x) (n x)) = 0 ∧
      E.fear (E.toPath.run (initial x) (n x)) = 0 ∧
      E.suffering (E.toPath.run (initial x) (n x)) = 0 := by
  intro x
  have empty := M.empty_of_covered criteria (coverage x)
  exact ⟨empty,
    E.eventual_release_from_revision release
      (recognizes x empty) (n x) (bound x)⟩

/-! ## The fourfold production argument can feed the same path -/

structure FourfoldPracticeBridge
    (M : FourfoldCausation.Model Event Kind Time)
    (E : EvidenceProcess S) (event : Event) (initial : S) : Prop where
  laws : M.Laws
  release : E.ReleaseConditions
  recognizes : ¬ M.intrinsic event → E.insight initial

theorem fourfold_to_bounded_release
    {M : FourfoldCausation.Model Event Kind Time}
    {E : EvidenceProcess S} {event : Event} {initial : S}
    (bridge : FourfoldPracticeBridge M E event initial)
    (n : Nat) (bound : E.grasp initial + 2 ≤ n) :
    ¬ M.intrinsic event ∧
      E.grasp (E.toPath.run initial n) = 0 ∧
      E.fear (E.toPath.run initial n) = 0 ∧
      E.suffering (E.toPath.run initial n) = 0 := by
  have nonIntrinsic := M.no_intrinsic_by_four_cases bridge.laws event
  exact ⟨nonIntrinsic,
    E.eventual_release_from_revision bridge.release
      (bridge.recognizes nonIntrinsic) n bound⟩

/-! ## Executable witnesses and separation results -/

theorem calibratedDependenceBridge :
    DependencePracticeBridge
      (DependenceCoverage.isolated .causal) calibrated false calibratedStart where
  criteria := DependenceCoverage.isolated_criteria .causal
  release := calibrated_conditions
  recognizes _ := rfl

theorem concrete_dependence_argument_releases :
    ¬ (DependenceCoverage.isolated .causal).own false ∧
      calibrated.grasp (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.fear (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.suffering (calibrated.toPath.run calibratedStart 5) = 0 := by
  exact dependence_to_bounded_release calibratedDependenceBridge .causal
    (DependenceCoverage.isolated_active_edge .causal) 5 (by decide)

theorem calibratedFourfoldBridge :
    FourfoldPracticeBridge FourfoldCausation.chain calibrated true calibratedStart where
  laws := FourfoldCausation.chain_laws
  release := calibrated_conditions
  recognizes _ := rfl

theorem concrete_fourfold_argument_releases :
    ¬ FourfoldCausation.chain.intrinsic true ∧
      calibrated.grasp (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.fear (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.suffering (calibrated.toPath.run calibratedStart 5) = 0 := by
  exact fourfold_to_bounded_release calibratedFourfoldBridge 5 (by decide)

/-- Correct recognition without evidence assimilation does not force the
practical conclusion. -/
theorem insight_without_revision_does_not_release :
    ¬ (DependenceCoverage.isolated .causal).own false ∧
      ignored.insight () ∧
      ∀ n, ignored.suffering (ignored.toPath.run () n) = 1 := by
  have empty :=
    (DependenceCoverage.isolated .causal).empty_of_mode_dependency .causal
      (DependenceModes.Model.OwnBeingCriteria.at
        (DependenceCoverage.isolated .causal)
        (DependenceCoverage.isolated_criteria .causal) .causal)
      (DependenceCoverage.isolated_active_edge .causal)
  exact ⟨empty, observation_without_assimilation.2.2.2.2.1,
    observation_without_assimilation.2.2.2.2.2⟩

/-- A successful cognitive trajectory does not, by itself, establish the
ontological premise for an unrelated subject. -/
theorem release_does_not_prove_universal_emptiness :
    calibrated.suffering (calibrated.toPath.run calibratedStart 5) = 0 ∧
      (DependenceCoverage.isolated .causal).own true :=
  ⟨calibrated_releases_by_five.2.2, rfl⟩

end BuddhistComparativeLogic.ArgumentPipeline
