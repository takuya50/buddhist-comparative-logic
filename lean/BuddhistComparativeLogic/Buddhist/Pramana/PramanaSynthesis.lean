/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.SupportingArguments

/-!
# A common certificate interface for Buddhist inference

This module synthesizes the existing Dignaga, Dharmakirti and emptiness
developments without identifying their distinct proof obligations.  A
`DeductiveCertificate` contains exactly what derives the thesis at the
subject: possession of the reason and an explicit pervasion.  A
`DialecticalCertificate` additionally contains a positive comparison example;
that extra field completes the three marks and gives a valid cell in the wheel
of reasons.

The adapters below put identity, effect, perceptible non-apprehension and
dependence arguments through the same interface.  The final countermodels
record three invalid shortcuts: the wheel alone does not settle the subject,
pervasion without subject possession is vacuous, and a sound subject-level
inference need not have an agreed comparison example.
-/

namespace BuddhistComparativeLogic.PramanaSynthesis

open BuddhistComparativeLogic.Hetucakra

/-! ## The common deductive and dialectical layers -/

/-- The two independent obligations needed for a subject-level deduction. -/
structure DeductiveCertificate {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Model L) : Prop where
  subjectReason : m.toAnumana.paksadharmata
  pervasion : m.vyapti

/-- A public comparison example is additional to the deductive core. -/
structure DialecticalCertificate {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Model L) : Prop
    extends DeductiveCertificate m where
  comparison : m.toAnumana.anvaya

theorem deductive_sound {L : Type u}
    {m : BuddhistComparativeLogic.Dharmakirti.Model L}
    (certificate : DeductiveCertificate m) :
    m.sadhya m.paksa :=
  m.vyapti_sound certificate.pervasion certificate.subjectReason

/-- Pervasion supplies the negative comparison mark; the positive comparison
field supplies the remaining non-subject mark. -/
theorem dialectical_trairupya {L : Type u}
    {m : BuddhistComparativeLogic.Dharmakirti.Model L}
    (certificate : DialecticalCertificate m) :
    m.toAnumana.trairupya :=
  ⟨certificate.subjectReason, certificate.comparison,
    m.vyapti_gives_vyatireka certificate.pervasion⟩

theorem dialectical_wheel_valid {L : Type u}
    {m : BuddhistComparativeLogic.Dharmakirti.Model L}
    (certificate : DialecticalCertificate m) :
    m.toAnumana.wheelVerdict = .valid :=
  m.vyapti_gives_verdict certificate.pervasion certificate.comparison

theorem dialectical_sound {L : Type u}
    {m : BuddhistComparativeLogic.Dharmakirti.Model L}
    (certificate : DialecticalCertificate m) :
    m.sadhya m.paksa :=
  deductive_sound certificate.toDeductiveCertificate

/-- Once pervasion is supplied, wheel validity asks exactly for a positive
comparison example.  It still says nothing new about the subject. -/
theorem wheel_valid_iff_comparison_under_pervasion {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Model L) (pervasion : m.vyapti) :
    m.toAnumana.wheelVerdict = .valid ↔ m.toAnumana.anvaya := by
  constructor
  · intro verdict
    exact (m.toAnumana.wheel_valid_iff.mp verdict).1
  · intro comparison
    exact m.vyapti_gives_verdict pervasion comparison

/-- Under pervasion, the three marks separate into subject possession and a
positive comparison example. -/
theorem trairupya_iff_subject_and_comparison_under_pervasion {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Model L) (pervasion : m.vyapti) :
    m.toAnumana.trairupya ↔
      m.toAnumana.paksadharmata ∧ m.toAnumana.anvaya := by
  constructor
  · intro marks
    exact ⟨marks.1, marks.2.1⟩
  · rintro ⟨subjectReason, comparison⟩
    exact ⟨subjectReason, comparison, m.vyapti_gives_vyatireka pervasion⟩

/-- `Dharmakirti.Model.vyapti` denotes precisely the global pervasion used by
the inference-scope audit. -/
theorem vyapti_iff_global_pervasion {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Model L) :
    m.vyapti ↔ BuddhistComparativeLogic.InferenceScope.Pervasion m.toAnumana :=
  m.vyapti_iff

/-- If all three marks are already assumed, adding global pervasion has the
same strength as assuming the disputed thesis.  This theorem is an assumption
audit, not an independent proof of pervasion. -/
theorem vyapti_has_thesis_strength_under_marks {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Model L)
    (marks : m.toAnumana.trairupya) :
    m.vyapti ↔ m.sadhya m.paksa := by
  rw [vyapti_iff_global_pervasion]
  exact BuddhistComparativeLogic.InferenceScope.pervasion_iff_thesis_under_marks
    m.toAnumana marks

/-! ## Dharmakirti's three sources of pervasion -/

/-- An identity reason provides pervasion through predicate inclusion. -/
theorem ofSvabhavaHetu {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.SvabhavaHetu L)
    (subjectReason : m.toAnumana.paksadharmata) :
    DeductiveCertificate m.toModel where
  subjectReason := subjectReason
  pervasion := m.svabhavahetu_vyapti

/-- Regard an effect reason's causal law as the proposition naming its
pervasion; the law remains an explicit argument to the certificate below. -/
def karyaModel {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.KaryaHetu L) :
    BuddhistComparativeLogic.Dharmakirti.Model L where
  toAnumana := m.toAnumana
  vyapti := m.causalLaw
  vyapti_iff := m.causal_law_iff

theorem ofKaryaHetu {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.KaryaHetu L)
    (law : m.causalLaw) (subjectReason : m.toAnumana.paksadharmata) :
    DeductiveCertificate (karyaModel m) where
  subjectReason := subjectReason
  pervasion := law

/-- Non-apprehension is represented as a reason only when joined to the
object's perceptibility.  The thesis is metalevel absence of presence. -/
def anupalabdhiModel {O : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Anupalabdhi O) (subject : O) :
    BuddhistComparativeLogic.Dharmakirti.Model O where
  paksa := subject
  sadhya := fun x => ¬ m.present x
  reason := fun x => m.perceptible x ∧ ¬ m.perceived x
  vyapti := ∀ x, (m.perceptible x ∧ ¬ m.perceived x) → ¬ m.present x
  vyapti_iff := Iff.rfl

theorem anupalabdhi_pervasion {O : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Anupalabdhi O) (subject : O) :
    (anupalabdhiModel m subject).vyapti := by
  intro x reason
  exact m.drsyanupalabdhi_sound reason.1 reason.2

theorem ofAnupalabdhi {O : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Anupalabdhi O) (subject : O)
    (perceptible : m.perceptible subject)
    (unperceived : ¬ m.perceived subject) :
    DeductiveCertificate (anupalabdhiModel m subject) where
  subjectReason := ⟨perceptible, unperceived⟩
  pervasion := anupalabdhi_pervasion m subject

theorem svabhava_conclusion {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.SvabhavaHetu L)
    (subjectReason : m.toAnumana.paksadharmata) :
    m.sadhya m.paksa :=
  deductive_sound (ofSvabhavaHetu m subjectReason)

theorem karya_conclusion {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.KaryaHetu L)
    (law : m.causalLaw) (subjectReason : m.toAnumana.paksadharmata) :
    m.sadhya m.paksa :=
  deductive_sound (ofKaryaHetu m law subjectReason)

theorem anupalabdhi_conclusion {O : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Anupalabdhi O) (subject : O)
    (perceptible : m.perceptible subject)
    (unperceived : ¬ m.perceived subject) :
    ¬ m.present subject :=
  deductive_sound (ofAnupalabdhi m subject perceptible unperceived)

/-! ## Dependence and emptiness through the common interface -/

/-- A witnessed mode of dependence supplies subject possession, while the
mode-specific own-being criterion supplies pervasion. -/
theorem ofModeDependence {D : Type u}
    (M : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : M.InvariantOwnAt mode)
    {subject source : D} (edge : M.DependsAt mode source subject) :
    DeductiveCertificate
      (BuddhistComparativeLogic.SupportingArguments.modeInference M mode subject) := by
  have result := BuddhistComparativeLogic.SupportingArguments.local_dependence_inference
    M mode invariant edge
  exact ⟨result.1, result.2.1⟩

/-- A second, non-subject dependence witness supplies the comparison field
needed for a dialectical certificate. -/
theorem dialecticalOfModeDependence {D : Type u}
    (M : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : M.InvariantOwnAt mode)
    {subject source : D} (edge : M.DependsAt mode source subject)
    (comparison :
      BuddhistComparativeLogic.SupportingArguments.ComparisonWitness M mode subject) :
    DialecticalCertificate
      (BuddhistComparativeLogic.SupportingArguments.modeInference M mode subject) where
  toDeductiveCertificate := ofModeDependence M mode invariant edge
  comparison :=
    (BuddhistComparativeLogic.SupportingArguments.comparisonWitness_iff_anvaya
      M mode invariant subject).mp comparison

theorem mode_dependence_conclusion {D : Type u}
    (M : BuddhistComparativeLogic.DependenceModes.Model D)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : M.InvariantOwnAt mode)
    {subject source : D} (edge : M.DependsAt mode source subject) :
    ¬ M.own subject :=
  deductive_sound (ofModeDependence M mode invariant edge)

/-- The existing Madhyamaka adapter already assumes universal emptiness.  Its
certificate therefore records that premise through `madhyamaka_pervasion`;
this construction does not independently establish the bridge. -/
theorem ofMadhyamaka {V : Type u}
    (M : BuddhistComparativeLogic.Madhyamaka V) (subject : BuddhistComparativeLogic.Dharma) :
    DeductiveCertificate
      (BuddhistComparativeLogic.EmptinessInference.ofMadhyamaka M subject) where
  subjectReason := M.mmk_24_19 subject
  pervasion :=
    BuddhistComparativeLogic.EmptinessInference.madhyamaka_pervasion M subject

theorem madhyamaka_conclusion {V : Type u}
    (M : BuddhistComparativeLogic.Madhyamaka V) (subject : BuddhistComparativeLogic.Dharma) :
    M.toEmptiness.emptyOf subject :=
  deductive_sound (ofMadhyamaka M subject)

/-! ## Countermodels to invalid shortcuts -/

/-- The existing `nofire` inference has all three marks and a valid wheel
cell while its subject thesis is false. -/
theorem marks_and_valid_wheel_do_not_entail_subject :
    ∃ a : BuddhistComparativeLogic.Hetucakra.Anumana BuddhistComparativeLogic.Hetucakra.Locus,
      a.trairupya ∧ a.wheelVerdict = .valid ∧ ¬ a.sadhya a.paksa := by
  refine ⟨BuddhistComparativeLogic.Hetucakra.nofire,
    BuddhistComparativeLogic.Hetucakra.no_deductive_soundness.1,
    BuddhistComparativeLogic.Hetucakra.no_deductive_soundness.2.1, ?_⟩
  exact BuddhistComparativeLogic.Hetucakra.no_deductive_soundness.2.2

/-- A true but vacuous pervasion whose reason is absent at the subject. -/
def vacuousPervasion : BuddhistComparativeLogic.Dharmakirti.Model Unit where
  paksa := ()
  sadhya := fun _ => False
  reason := fun _ => False
  vyapti := True
  vyapti_iff := by simp

theorem pervasion_without_subject_reason_is_insufficient :
    vacuousPervasion.vyapti ∧
      ¬ vacuousPervasion.toAnumana.paksadharmata ∧
      ¬ vacuousPervasion.sadhya vacuousPervasion.paksa := by
  simp [vacuousPervasion, BuddhistComparativeLogic.Hetucakra.Anumana.paksadharmata]

/-- On a singleton domain the deductive obligations succeed, but no distinct
positive comparison subject can exist. -/
def singletonSound : BuddhistComparativeLogic.Dharmakirti.Model Unit where
  paksa := ()
  sadhya := fun _ => True
  reason := fun _ => True
  vyapti := True
  vyapti_iff := by simp

theorem singleton_has_no_comparison :
    ¬ singletonSound.toAnumana.anvaya := by
  rintro ⟨x, similar, _⟩
  exact similar.1 (Subsingleton.elim x singletonSound.paksa)

theorem sound_subject_inference_need_not_have_valid_wheel :
    DeductiveCertificate singletonSound ∧
      singletonSound.sadhya singletonSound.paksa ∧
      singletonSound.toAnumana.wheelVerdict ≠ .valid := by
  let certificate : DeductiveCertificate singletonSound :=
    ⟨trivial, trivial⟩
  refine ⟨certificate, deductive_sound certificate, ?_⟩
  intro verdict
  exact singleton_has_no_comparison
    ((singletonSound.toAnumana.wheel_valid_iff.mp verdict).1)

end BuddhistComparativeLogic.PramanaSynthesis
