/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.InferenceScope
import BuddhistComparativeLogic.Buddhist.HeartSutra.PremiseCertificates
import BuddhistComparativeLogic.Comparative.Nyaya.Tattvacintamani

/-!
# Grounding definitions and extending observations

This module gives two bounded audits motivated by Jayarasi Bhatta's
*Tattvopaplavasiṃha*.  First, it distinguishes a definition's local adequacy
from the noncircular support used to qualify an epistemic method.  Support is
either an independently certified base or a finite rank that strictly falls
along every definitional dependency together with certified dependency-free
bases.  A two-node mutual dependency has neither kind of support.

Second, it separates agreement on a finite observation sample from global
reason-to-thesis pervasion.  An unseen finite counterexample blocks the
global inference; an explicit coverage certificate restores it.  The
formal results diagnose those two argument forms only.  They do not prove
wholesale scepticism, reconstruct every argument in the source, or establish
that any historical pramana is unreliable.
-/

namespace BuddhistComparativeLogic.Jayarasi

open BuddhistComparativeLogic.Hetucakra
open BuddhistComparativeLogic.PremiseCertificates

universe u

/-! ## Definitional dependence and finite grounding -/

/-- `adequate` is the local definition check, `dependsOn` exposes reliance on
another method, and `independentBase` states which methods may receive direct
evidence.  The three predicates are intentionally independent. -/
structure DefinitionSystem (Method : Type u) where
  adequate : Method -> Prop
  dependsOn : Method -> Method -> Prop
  independentBase : Method -> Prop

/-- A finite grounding ranks every dependency strictly below what depends on
it and provides a proof-bearing certificate at every dependency-free base.
The certificate type is reused from `PremiseCertificates`, so source metadata
alone cannot inhabit it. -/
structure RankedGrounding {Method : Type u}
    (system : DefinitionSystem Method) where
  rank : Method -> Nat
  descends : forall {method support},
    system.dependsOn method support -> rank support < rank method
  base : forall method,
    (¬ exists support, system.dependsOn method support) ->
      Certified (system.independentBase method)

/-- A method is qualified in this audit only after its local definition is
adequate and either its own independent base is certified or the whole
bounded dependency system has a decreasing grounding. -/
structure Qualification {Method : Type u}
    (system : DefinitionSystem Method) (method : Method) : Type u where
  adequate : system.adequate method
  support : Sum (Certified (system.independentBase method))
    (RankedGrounding system)

namespace Qualification

variable {Method : Type u} {system : DefinitionSystem Method}
    {method : Method}

theorem local_adequacy (qualification : Qualification system method) :
    system.adequate method :=
  qualification.adequate

end Qualification

inductive PramanaMethod where
  | perception
  | inference
  deriving DecidableEq, Repr

open PramanaMethod

/-- Perception is the independent base in this deliberately small positive
system; inference depends on it. -/
def pramanaSystem : DefinitionSystem PramanaMethod where
  adequate _ := True
  dependsOn
    | .inference, .perception => True
    | _, _ => False
  independentBase
    | .perception => True
    | .inference => False

theorem perception_is_independent_base :
    pramanaSystem.independentBase .perception := by
  trivial

def perceptionBaseCertificate :
    Certified (pramanaSystem.independentBase .perception) :=
  certifyInternal
    ``BuddhistComparativeLogic.Jayarasi.perception_is_independent_base
    perception_is_independent_base

def pramanaGrounding : RankedGrounding pramanaSystem where
  rank
    | .perception => 0
    | .inference => 1
  descends := by
    intro method support dependency
    cases method <;> cases support <;>
      simp [pramanaSystem] at dependency ⊢
  base := by
    intro method noDependency
    cases method with
    | perception => exact perceptionBaseCertificate
    | inference =>
        exfalso
        exact noDependency ⟨.perception, by simp [pramanaSystem]⟩

def perceptionQualification :
    Qualification pramanaSystem .perception where
  adequate := trivial
  support := Sum.inl perceptionBaseCertificate

def inferenceQualification :
    Qualification pramanaSystem .inference where
  adequate := trivial
  support := Sum.inr pramanaGrounding

/-- Both routes are inhabited: direct certification qualifies the base, and
the base-certified descending grounding qualifies the derived method. -/
theorem independent_and_ranked_routes_nonvacuous :
    Nonempty (Qualification pramanaSystem .perception) /\
      Nonempty (Qualification pramanaSystem .inference) :=
  ⟨⟨perceptionQualification⟩, ⟨inferenceQualification⟩⟩

/-! ## Mutual dependence alone supplies no qualification -/

inductive CircularMethod where
  | left
  | right
  deriving DecidableEq, Repr

open CircularMethod

/-- Both local definitions pass, but each method relies exclusively on the
other and neither is independently based. -/
def circularSystem : DefinitionSystem CircularMethod where
  adequate _ := True
  dependsOn
    | .left, .right => True
    | .right, .left => True
    | _, _ => False
  independentBase _ := False

theorem circular_dependencies :
    circularSystem.dependsOn .left .right /\
      circularSystem.dependsOn .right .left := by
  constructor <;> trivial

theorem circular_system_has_no_ranked_grounding :
    ¬ Nonempty (RankedGrounding circularSystem) := by
  rintro ⟨grounding⟩
  have rightBelowLeft : grounding.rank .right < grounding.rank .left :=
    grounding.descends circular_dependencies.1
  have leftBelowRight : grounding.rank .left < grounding.rank .right :=
    grounding.descends circular_dependencies.2
  exact Nat.lt_asymm rightBelowLeft leftBelowRight

theorem circular_system_has_no_independent_certificate
    (method : CircularMethod) :
    ¬ Nonempty (Certified (circularSystem.independentBase method)) := by
  cases method <;>
    exact certified_false_is_uninhabited

/-- Adequacy at both nodes plus mutual reference still supplies neither
permitted support route.  This theorem targets bare circular support, not all
mutually informative or coherent definitions. -/
theorem circularity_alone_does_not_qualify :
    circularSystem.adequate .left /\
      circularSystem.adequate .right /\
      circularSystem.dependsOn .left .right /\
      circularSystem.dependsOn .right .left /\
      (forall method, ¬ Nonempty (Qualification circularSystem method)) := by
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  intro method
  rintro ⟨qualification⟩
  cases qualification.support with
  | inl certificate =>
      exact circular_system_has_no_independent_certificate method
        ⟨certificate⟩
  | inr grounding =>
      exact circular_system_has_no_ranked_grounding ⟨grounding⟩

/-! ## Finite observations and global pervasion -/

/-- Agreement is restricted to an explicitly selected sample. -/
def SampleConsistent {L : Type u} (argument : Anumana L)
    (sample : L -> Prop) : Prop :=
  forall object, sample object -> argument.reason object ->
    argument.sadhya object

/-- Coverage is the missing bridge: every reason-bearing object must occur in
the checked sample. -/
def CoversReason {L : Type u} (argument : Anumana L)
    (sample : L -> Prop) : Prop :=
  forall object, argument.reason object -> sample object

/-- Both the observed agreement and its extrapolation bridge carry proof and
provenance. -/
structure CoverageCertificate {L : Type u} (argument : Anumana L)
    (sample : L -> Prop) where
  observations : Certified (SampleConsistent argument sample)
  coverage : Certified (CoversReason argument sample)

namespace CoverageCertificate

variable {L : Type u} {argument : Anumana L} {sample : L -> Prop}

/-- With coverage supplied, sample agreement extends to the global pervasion
audited by `InferenceScope` and reused by `Tattvacintamani`. -/
theorem toGlobalPervasion
    (certificate : CoverageCertificate argument sample) :
    BuddhistComparativeLogic.Tattvacintamani.Vyapti argument := by
  intro object reason
  exact certificate.observations.fact object
    (certificate.coverage.fact object reason) reason

/-- If the disputed subject bears the reason, the coverage certificate also
builds the existing reflective-application object. -/
theorem toParamarsa (certificate : CoverageCertificate argument sample)
    (subjectReason : argument.reason argument.paksa) :
    BuddhistComparativeLogic.Tattvacintamani.Paramarsa argument where
  subjectReason := subjectReason
  vyapti := certificate.toGlobalPervasion

end CoverageCertificate

inductive SurveySite where
  | first
  | second
  | hidden
  deriving DecidableEq, Repr

open SurveySite

def observed : SurveySite -> Prop
  | .first | .second => True
  | .hidden => False

/-- Every site bears the reason, but the thesis fails at the unobserved one. -/
def surveyArgument : Anumana SurveySite where
  paksa := .first
  reason _ := True
  sadhya
    | .first | .second => True
    | .hidden => False

theorem survey_observations_consistent :
    SampleConsistent surveyArgument observed := by
  intro site sampled _reason
  cases site <;> simp [observed, surveyArgument] at sampled ⊢

theorem survey_not_globally_pervaded :
    ¬ BuddhistComparativeLogic.Tattvacintamani.Vyapti surveyArgument := by
  intro global
  exact global .hidden trivial

/-- Two positive observed cases coexist with an unseen reason-bearing
counterexample.  Finite sample consistency therefore does not itself supply
the global quantifier. -/
theorem finite_sample_does_not_entail_global_pervasion :
    SampleConsistent surveyArgument observed /\
      observed .first /\ observed .second /\
      surveyArgument.reason .hidden /\
      ¬ surveyArgument.sadhya .hidden /\
      ¬ BuddhistComparativeLogic.InferenceScope.Pervasion surveyArgument := by
  exact ⟨survey_observations_consistent, trivial, trivial, trivial,
    by simp [surveyArgument], survey_not_globally_pervaded⟩

/-! ## A coverage bridge that does license the conclusion -/

/-- The repaired argument restricts its reason to the inspected sites.  The
hidden site remains in the domain as a genuine non-reason case. -/
def coveredArgument : Anumana SurveySite where
  paksa := .first
  reason := observed
  sadhya
    | .first | .second => True
    | .hidden => False

theorem covered_observations_consistent :
    SampleConsistent coveredArgument observed := by
  intro site sampled _reason
  cases site <;> simp [observed, coveredArgument] at sampled ⊢

theorem every_covered_reason_is_observed :
    CoversReason coveredArgument observed := by
  intro site reason
  exact reason

def coveredObservationCertificate :
    Certified (SampleConsistent coveredArgument observed) :=
  certifyInternal
    ``BuddhistComparativeLogic.Jayarasi.covered_observations_consistent
    covered_observations_consistent

def coveredReasonCertificate :
    Certified (CoversReason coveredArgument observed) :=
  certifyInternal
    ``BuddhistComparativeLogic.Jayarasi.every_covered_reason_is_observed
    every_covered_reason_is_observed

def coveredCertificate : CoverageCertificate coveredArgument observed where
  observations := coveredObservationCertificate
  coverage := coveredReasonCertificate

theorem coverage_bridge_yields_global_pervasion :
    BuddhistComparativeLogic.Tattvacintamani.Vyapti coveredArgument :=
  coveredCertificate.toGlobalPervasion

theorem coverage_bridge_yields_subject_conclusion :
    coveredArgument.sadhya coveredArgument.paksa := by
  exact (coveredCertificate.toParamarsa trivial).sound

/-- The positive model contains two sampled reason cases and an unsampled
non-reason case, so the global result is not obtained by empty predicates. -/
theorem coverage_bridge_nonvacuous :
    coveredArgument.reason .first /\
      coveredArgument.reason .second /\
      ¬ coveredArgument.reason .hidden /\
      coveredArgument.sadhya .first /\
      coveredArgument.sadhya .second /\
      ¬ coveredArgument.sadhya .hidden /\
      BuddhistComparativeLogic.Tattvacintamani.Vyapti coveredArgument := by
  exact ⟨trivial, trivial, by simp [coveredArgument, observed], trivial,
    trivial, by simp [coveredArgument], coverage_bridge_yields_global_pervasion⟩

end BuddhistComparativeLogic.Jayarasi
