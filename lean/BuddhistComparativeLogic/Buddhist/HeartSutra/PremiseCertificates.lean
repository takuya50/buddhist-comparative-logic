/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.ArgumentPipeline

/-!
# Premise certificates for the argument-to-practice pipeline

The end-to-end arguments deliberately leave historical, philosophical, and
empirical premises exposed.  This module adds a provenance-bearing interface
without pretending that a citation establishes its claim.  `CitedClaim P`
stores only metadata and is inhabited even when `P` is false.  `Certified P`
also contains a Lean proof of `P`; only certified premises enter the soundness
theorems below.

External locators remain unchecked textual annotations.  Internal locators
instead store a `Lean.Name`; every internal witness shipped below uses Lean's
quoted-name syntax, so a misspelled or absent declaration fails elaboration.
The locator and proof payload remain deliberately separate: traceability does
not turn the referenced declaration into the proof of the claim.

The dependence certificate records a witnessed edge, the matching
mode-specific own-being criterion, recognition, revision, and the numerical
release bound separately.  The fourfold certificate records event occurrence
and all five causal laws separately rather than hiding them in one opaque
bundle.  The resulting theorems connect these auditable inputs to the existing
bounded-release results.
-/

namespace BuddhistComparativeLogic.PremiseCertificates

open DependenceModes
open BeliefRevision

/-- A coarse evidence category.  It is metadata, not a truth predicate. -/
inductive EvidenceKind where
  | textual
  | philosophical
  | empirical
  | formalModel
  deriving DecidableEq, Repr

/-- A locator is either external free text or the name of a Lean declaration. -/
inductive EvidenceLocator where
  | external (description : String)
  | leanDeclaration (declaration : Lean.Name)
  deriving DecidableEq, Repr

/-- A source and typed locator annotation for one premise. -/
structure EvidenceRef where
  kind : EvidenceKind
  source : String
  locator : EvidenceLocator
  deriving DecidableEq, Repr

/-- A referenced assertion with no proof payload. -/
structure CitedClaim (_P : Prop) where
  evidence : EvidenceRef

/-- A referenced assertion that also carries the proof consumed by Lean. -/
structure Certified (P : Prop) extends CitedClaim P where
  fact : P

def internalRef (declaration : Lean.Name) : EvidenceRef where
  kind := .formalModel
  source := "lean"
  locator := .leanDeclaration declaration

def certifyInternal (declaration : Lean.Name) (fact : P) : Certified P where
  evidence := internalRef declaration
  fact := fact

/-! ## Metadata does not discharge a premise -/

def citedFalse : CitedClaim False where
  evidence :=
    { kind := .textual
      source := "an arbitrary source label"
      locator := .external "an arbitrary locator" }

theorem citation_metadata_can_accompany_a_false_claim :
    Nonempty (CitedClaim False) :=
  ⟨citedFalse⟩

theorem certified_false_is_uninhabited : ¬ Nonempty (Certified False) := by
  rintro ⟨certificate⟩
  exact certificate.fact

/-! ## Mode-specific dependence certificates -/

/-- Every premise used by one local dependence-to-release argument.  Requiring
only `InvariantOwnAt mode` avoids claiming criteria for unused modes. -/
structure DependenceReleaseCertificate
    (M : DependenceModes.Model D) (E : EvidenceProcess S)
    (subject source : D) (initial : S) where
  mode : Mode
  edge : Certified (M.DependsAt mode source subject)
  ownCriterion : Certified (M.InvariantOwnAt mode)
  recognition : Certified (¬ M.own subject → E.insight initial)
  revision : Certified E.ReleaseConditions

/-- A release bound is also a premise and receives its own provenance. -/
abbrev BoundCertificate (E : EvidenceProcess S) (initial : S) (n : Nat) :=
  Certified (E.grasp initial + 2 ≤ n)

/-- Soundness of the provenance-bearing dependence pipeline. -/
theorem dependence_certificate_sound
    {M : DependenceModes.Model D} {E : EvidenceProcess S}
    {subject source : D} {initial : S}
    (certificate : DependenceReleaseCertificate M E subject source initial)
    (n : Nat) (bound : BoundCertificate E initial n) :
    ¬ M.own subject ∧
      E.grasp (E.toPath.run initial n) = 0 ∧
      E.fear (E.toPath.run initial n) = 0 ∧
      E.suffering (E.toPath.run initial n) = 0 := by
  have empty : ¬ M.own subject :=
    M.empty_of_mode_dependency certificate.mode
      certificate.ownCriterion.fact certificate.edge.fact
  exact ⟨empty,
    E.eventual_release_from_revision certificate.revision.fact
      (certificate.recognition.fact empty) n bound.fact⟩

/-! ## Premise-by-premise fourfold certificates -/

/-- Event occurrence and each causal law have separate source references.  This
makes it possible to revise one interpretation without relabelling the other
premises. -/
structure FourfoldReleaseCertificate
    (M : FourfoldCausation.Model Event Kind Time)
    (E : EvidenceProcess S) (event : Event) (initial : S) where
  occurrence : Certified (M.occurs event)
  causalPriority : Certified M.CausalPriority
  strictEarlier : Certified M.StrictEarlier
  intrinsicOccurs : Certified M.IntrinsicOccurs
  intrinsicIndependence : Certified M.IntrinsicIndependence
  occurrenceConditioned : Certified M.OccurrenceConditioned
  recognition : Certified (¬ M.intrinsic event → E.insight initial)
  revision : Certified E.ReleaseConditions

theorem FourfoldReleaseCertificate.toLaws
    {M : FourfoldCausation.Model Event Kind Time}
    {E : EvidenceProcess S} {event : Event} {initial : S}
    (certificate : FourfoldReleaseCertificate M E event initial) : M.Laws where
  causalPriority := certificate.causalPriority.fact
  strictEarlier := certificate.strictEarlier.fact
  intrinsicOccurs := certificate.intrinsicOccurs.fact
  intrinsicIndependence := certificate.intrinsicIndependence.fact
  occurrenceConditioned := certificate.occurrenceConditioned.fact

/-- Soundness of the provenance-bearing fourfold pipeline. -/
theorem fourfold_certificate_sound
    {M : FourfoldCausation.Model Event Kind Time}
    {E : EvidenceProcess S} {event : Event} {initial : S}
    (certificate : FourfoldReleaseCertificate M E event initial)
    (n : Nat) (bound : BoundCertificate E initial n) :
    M.occurs event ∧
      ¬ M.intrinsic event ∧
      E.grasp (E.toPath.run initial n) = 0 ∧
      E.fear (E.toPath.run initial n) = 0 ∧
      E.suffering (E.toPath.run initial n) = 0 := by
  have nonIntrinsic : ¬ M.intrinsic event :=
    M.no_intrinsic_by_four_cases certificate.toLaws event
  exact ⟨certificate.occurrence.fact, nonIntrinsic,
    E.eventual_release_from_revision certificate.revision.fact
      (certificate.recognition.fact nonIntrinsic) n bound.fact⟩

/-! ## Executable certificate witnesses -/

open DependenceCoverage
open FourfoldCausation

/-! The small obligations below give each proof term used by an internal
certificate its own declaration.  The quoted locators in the witness records
therefore resolve during elaboration. -/

theorem isolated_causal_invariant :
    (isolated .causal).InvariantOwnAt .causal :=
  DependenceModes.Model.OwnBeingCriteria.at
    (isolated .causal) (isolated_criteria .causal) .causal

theorem calibrated_recognizes_isolated_causal :
    ¬ (isolated .causal).own false → calibrated.insight calibratedStart := by
  intro _
  rfl

theorem calibrated_bound_five :
    calibrated.grasp calibratedStart + 2 ≤ 5 := by
  decide

theorem chain_true_occurs : chain.occurs true := rfl

theorem chain_causal_priority : chain.CausalPriority :=
  chain_laws.causalPriority

theorem chain_strict_earlier : chain.StrictEarlier :=
  chain_laws.strictEarlier

theorem chain_intrinsic_occurs : chain.IntrinsicOccurs :=
  chain_laws.intrinsicOccurs

theorem chain_intrinsic_independence : chain.IntrinsicIndependence :=
  chain_laws.intrinsicIndependence

theorem chain_occurrence_conditioned : chain.OccurrenceConditioned :=
  chain_laws.occurrenceConditioned

theorem calibrated_recognizes_chain_true :
    ¬ chain.intrinsic true → calibrated.insight calibratedStart := by
  intro _
  rfl

def calibratedDependenceCertificate :
    DependenceReleaseCertificate
      (isolated .causal) calibrated false true calibratedStart where
  mode := .causal
  edge := certifyInternal
    ``BuddhistComparativeLogic.DependenceCoverage.isolated_active_edge
    (isolated_active_edge .causal)
  ownCriterion := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.isolated_causal_invariant
    isolated_causal_invariant
  recognition := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.calibrated_recognizes_isolated_causal
    calibrated_recognizes_isolated_causal
  revision := certifyInternal
    ``BuddhistComparativeLogic.BeliefRevision.calibrated_conditions calibrated_conditions

def calibratedBound : BoundCertificate calibrated calibratedStart 5 :=
  certifyInternal ``BuddhistComparativeLogic.PremiseCertificates.calibrated_bound_five
    calibrated_bound_five

theorem certified_dependence_example_releases :
    ¬ (isolated .causal).own false ∧
      calibrated.grasp (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.fear (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.suffering (calibrated.toPath.run calibratedStart 5) = 0 :=
  dependence_certificate_sound calibratedDependenceCertificate 5
    calibratedBound

def calibratedFourfoldCertificate :
    FourfoldReleaseCertificate chain calibrated true calibratedStart where
  occurrence := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.chain_true_occurs chain_true_occurs
  causalPriority := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.chain_causal_priority
    chain_causal_priority
  strictEarlier := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.chain_strict_earlier
    chain_strict_earlier
  intrinsicOccurs := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.chain_intrinsic_occurs
    chain_intrinsic_occurs
  intrinsicIndependence := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.chain_intrinsic_independence
    chain_intrinsic_independence
  occurrenceConditioned := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.chain_occurrence_conditioned
    chain_occurrence_conditioned
  recognition := certifyInternal
    ``BuddhistComparativeLogic.PremiseCertificates.calibrated_recognizes_chain_true
    calibrated_recognizes_chain_true
  revision := certifyInternal
    ``BuddhistComparativeLogic.BeliefRevision.calibrated_conditions calibrated_conditions

theorem certified_fourfold_example_releases :
    chain.occurs true ∧
      ¬ chain.intrinsic true ∧
      calibrated.grasp (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.fear (calibrated.toPath.run calibratedStart 5) = 0 ∧
      calibrated.suffering (calibrated.toPath.run calibratedStart 5) = 0 :=
  fourfold_certificate_sound calibratedFourfoldCertificate 5 calibratedBound

/-- The occurrence field prevents the same practice certificate from being
instantiated for a nonoccurring token in the finite chain model. -/
theorem nonoccurring_chain_event_has_no_release_certificate :
    ¬ Nonempty
      (FourfoldReleaseCertificate chain calibrated false calibratedStart) := by
  rintro ⟨certificate⟩
  exact Bool.noConfusion certificate.occurrence.fact

end BuddhistComparativeLogic.PremiseCertificates
