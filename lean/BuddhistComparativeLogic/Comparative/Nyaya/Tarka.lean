/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.Prasanga
import BuddhistComparativeLogic.Comparative.Nyaya.Tattvacintamani
import BuddhistComparativeLogic.Buddhist.Madhyamaka.NegandumCalibration

/-!
# Tarka as auxiliary counterfactual reasoning

This module gives a deliberately small reconstruction of `tarka`.  The
opposite of a target `F` is provisionally admitted and is shown to undermine
an independently established proposition `G`.  The counterfactual step and
the evidence for `G` are separate proof objects.  Together they establish
`¬¬F` constructively; recovering `F` requires an explicit stability principle
such as `Decidable F`.

The reconstruction is bounded in two historical directions.  It models the
doubt-removing role attached to *Nyāyasūtra* 1.1.40, rather than treating that
sūtra as a complete natural-deduction rule.  The name `SupportingPramana`
records the later classificatory distinction between auxiliary `tarka` and an
independent source of warrant; it does not claim that the later taxonomies are
already stated in the sūtra.  Finite countermodels below show why neither
component alone is a proof of the target.

Source status (accessed 2026-09-19): *Nyāyasūtra* 1.1.40 is fixed in the
GRETIL Sanskrit text
<https://gretil.sub.uni-goettingen.de/gretil/1_sanskr/6_sastra/3_phil/nyaya/gaunys_u.htm>;
Kang's passage-specific study is <https://doi.org/10.1007/s10781-009-9078-8>.
No source translation is reproduced.  `CounterfactualStep`,
`SupportingPramana`, and their constructive double-negation result are
project-authored formal paraphrases.  The `NegandumCalibration` import is used
only by the final FDE API-boundary theorem; it supplies `MetaExclusive` and the
existing all-glut model, not a premise about historical tarka.
-/

namespace BuddhistComparativeLogic.Tarka

universe u

/-! ## Counterfactual step, independent support, and certification -/

/-- The specifically hypothetical part of the reconstruction: if the
opposite of `target` held, the supported proposition would fail. -/
structure CounterfactualStep (target supported : Prop) : Prop where
  underOpposite : Not target -> Not supported

/-- Evidence for the proposition used to reject the provisional opposite.
Keeping this separate prevents `tarka` from being counted as its own
independent source of the same evidence. -/
structure SupportingPramana (supported : Prop) : Prop where
  established : supported

/-- A complete local certificate contains a counterfactual step and a
separately supplied warrant.  It does not store either `¬¬target` or
`target`; both are derived below. -/
structure TarkaCertificate (target supported : Prop) : Prop where
  tarka : CounterfactualStep target supported
  support : SupportingPramana supported

namespace TarkaCertificate

variable {target supported : Prop}

/-- The constructive result of the auxiliary reasoning is rejection of the
opposite, i.e. double negation of the target. -/
theorem removes_doubt (certificate : TarkaCertificate target supported) :
    Not (Not target) := by
  intro opposite
  exact certificate.tarka.underOpposite opposite
    certificate.support.established

/-- The same derivation factors through the generic `Prasanga` preservation
rule.  Here the provisional proposition is `¬target`, its consequence is
`¬supported`, and established support rejects that consequence. -/
theorem removes_doubt_via_prasanga
    (certificate : TarkaCertificate target supported) : Not (Not target) := by
  exact BuddhistComparativeLogic.Prasanga.rejection_via_preservation
    (D := fun proposition : Prop => proposition)
    (p := Not target) (q := Not supported)
    certificate.tarka.underOpposite
    (fun notSupported => notSupported certificate.support.established)

/-- Decidability is one explicit bridge from the doubt-removing result to the
positive target. -/
theorem conclude_of_decidable [Decidable target]
    (certificate : TarkaCertificate target supported) : target := by
  by_cases holds : target
  · exact holds
  · exact False.elim (certificate.removes_doubt holds)

/-- A supplied double-negation elimination principle is a more general and
fully visible bridge to the positive target. -/
theorem conclude_of_stability
    (certificate : TarkaCertificate target supported)
    (stable : Not (Not target) -> target) : target :=
  stable certificate.removes_doubt

end TarkaCertificate

/-! ## Adapters to the shared inference interfaces -/

/-- A one-location inference whose reason is the independently supported
proposition and whose thesis is the disputed target. -/
def toAnumana (target supported : Prop) :
    BuddhistComparativeLogic.Hetucakra.Anumana Unit where
  paksa := ()
  reason := fun _ => supported
  sadhya := fun _ => target

theorem toAnumana_reason (target supported : Prop) :
    (toAnumana target supported).reason
      (toAnumana target supported).paksa <-> supported :=
  Iff.rfl

theorem toAnumana_thesis (target supported : Prop) :
    (toAnumana target supported).sadhya
      (toAnumana target supported).paksa <-> target :=
  Iff.rfl

/-- Once the explicit stability bridge has supplied the target, a tarka
certificate becomes reflective application in the existing
`Tattvacintamani` interface. -/
theorem TarkaCertificate.toParamarsa {target supported : Prop}
    [Decidable target] (certificate : TarkaCertificate target supported) :
    BuddhistComparativeLogic.Tattvacintamani.Paramarsa
      (toAnumana target supported) where
  subjectReason := certificate.support.established
  vyapti := by
    intro _ _
    exact certificate.conclude_of_decidable

theorem certified_inference_is_sound {target supported : Prop}
    [Decidable target] (certificate : TarkaCertificate target supported) :
    (toAnumana target supported).sadhya
      (toAnumana target supported).paksa :=
  certificate.toParamarsa.sound

/-! ## Inhabited finite countermodels -/

/-- In this one-point model both propositions are false.  The conditional
step `¬False -> ¬False` is inhabited, while the target remains false.  Thus a
counterfactual step without independent support is not a positive proof. -/
theorem conditionalOnly : CounterfactualStep False False where
  underOpposite := fun notFalse => notFalse

theorem counterfactual_alone_has_false_target :
    CounterfactualStep False False /\ Not False :=
  ⟨conditionalOnly, fun falseProof => falseProof⟩

/-- In the complementary one-point model the supported proposition is true
and the target is false.  The needed counterfactual fails, so evidence for
`G` alone cannot establish `F`. -/
theorem supportOnly : SupportingPramana True where
  established := trivial

theorem support_alone_lacks_the_counterfactual :
    SupportingPramana True /\ Not False /\
      Not (CounterfactualStep False True) := by
  refine ⟨supportOnly, (fun falseProof => falseProof), ?_⟩
  intro step
  exact step.underOpposite (fun falseProof => falseProof) trivial

/-- The two fields are jointly inhabited in a nonvacuous decidable case, and
the target is obtained by derivation rather than by record projection. -/
theorem sampleCertificate : TarkaCertificate True True where
  tarka :=
    { underOpposite := fun notTrue =>
        False.elim (notTrue trivial) }
  support := supportOnly

theorem sample_certificate_derives_target :
    Not (Not True) /\ True :=
  ⟨sampleCertificate.removes_doubt,
    sampleCertificate.conclude_of_decidable⟩

/-! ## FDE boundary -/

/-- Formula-level emptiness in the existing all-glut FDE model does not
supply the metalevel exclusion used by the `Not`-valued tarka rule.  This is
an API-level boundary, not a rejection of paraconsistent reasoning. -/
theorem fde_glut_does_not_supply_metalevel_exclusion
    (dharma : BuddhistComparativeLogic.Dharma) :
    Not (BuddhistComparativeLogic.NegandumCalibration.MetaExclusive
      BuddhistComparativeLogic.fdeAllGlutEmptiness) :=
  (BuddhistComparativeLogic.NegandumCalibration.fde_glut_blocks_meta_exclusion
    dharma).2.2.2

end BuddhistComparativeLogic.Tarka
