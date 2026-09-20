/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis
import BuddhistComparativeLogic.Buddhist.Pramana.Apoha
import BuddhistComparativeLogic.Buddhist.HeartSutra.BeliefRevision

/-!
# A restrained Pramāṇavārttika synthesis

This module packages several proof obligations associated with Dharmakīrti's
epistemology without claiming to formalize a historical edition of the
`Pramāṇavārttika`.  A pramāṇa is represented here by an occurring, novel,
content-bearing and reliable cognition.  Reliability is operational: every
object presented by the cognition participates in a successful realization.
Causal efficacy is therefore obtained only through an occurring cognition
that both presents and realizes the object.

The inference layer keeps intrinsic (`svabhāva`) and extrinsic or effect-based
(`kārya`) grounds distinct while reusing their common pervasion certificate.
Subject-level deduction and a public proof with a comparison example remain
different interfaces.  Finite countermodels prevent four overextensions:
mere presentation is not reliability, reliability need not be novel, one
reliable cognition does not certify every object, and a valid comparison wheel
does not by itself establish its subject thesis.

The terms `intrinsic` and `extrinsic` below classify the source of the
pervasion premise.  They do not assert a general metaphysical division between
intrinsic and external entities.
-/

namespace BuddhistComparativeLogic.Pramanavarttika

open BuddhistComparativeLogic.Hetucakra

universe u v w

/-! ## Reliable cognition and causal efficacy -/

/-- A minimal operational account of cognition.  `realizes c o r` records a
successful result involving the object presented by cognition `c`. -/
structure CognitionModel (Cognition : Type u) (Object : Type v)
    (Result : Type w) where
  occurs : Cognition → Prop
  novel : Cognition → Prop
  presents : Cognition → Object → Prop
  realizes : Cognition → Object → Result → Prop

namespace CognitionModel

variable {Cognition : Type u} {Object : Type v} {Result : Type w}
    (M : CognitionModel Cognition Object Result)

/-- An object is causally efficacious in this model when an occurring
cognition presents it and has a successful realization involving it. -/
def CausallyEfficacious (o : Object) : Prop :=
  ∃ c r, M.occurs c ∧ M.presents c o ∧ M.realizes c o r

/-- Reliability is restricted to the objects that this cognition presents. -/
def Reliable (c : Cognition) : Prop :=
  ∀ {o}, M.presents c o → ∃ r, M.realizes c o r

/-- A content-bearing cognition presents at least one object. -/
def HasContent (c : Cognition) : Prop :=
  ∃ o, M.presents c o

/-- The present formal surrogate for a pramāṇa: occurrence, novelty, content,
and operational reliability are independent conjuncts. -/
def Pramana (c : Cognition) : Prop :=
  M.occurs c ∧ M.novel c ∧ M.HasContent c ∧ M.Reliable c

theorem pramana_occurs {c : Cognition} (h : M.Pramana c) : M.occurs c :=
  h.1

theorem pramana_is_novel {c : Cognition} (h : M.Pramana c) : M.novel c :=
  h.2.1

theorem pramana_has_content {c : Cognition} (h : M.Pramana c) :
    M.HasContent c :=
  h.2.2.1

theorem pramana_is_reliable {c : Cognition} (h : M.Pramana c) : M.Reliable c :=
  h.2.2.2

/-- Causal efficacy follows only for a presented object; this is the precise
scope of the operational reliability definition. -/
theorem pramana_tracks_causal_efficacy {c : Cognition} {o : Object}
    (h : M.Pramana c) (presented : M.presents c o) :
    M.CausallyEfficacious o := by
  obtain ⟨r, realized⟩ := h.2.2.2 presented
  exact ⟨c, r, h.1, presented, realized⟩

/-- Every formal pramāṇa has at least one presented object whose efficacy is
witnessed by that same occurring cognition. -/
theorem pramana_has_efficacious_content {c : Cognition}
    (h : M.Pramana c) :
    ∃ o, M.presents c o ∧ M.CausallyEfficacious o := by
  obtain ⟨o, presented⟩ := h.2.2.1
  exact ⟨o, presented, M.pramana_tracks_causal_efficacy h presented⟩

end CognitionModel

/-! ## Finite scope countermodels -/

/-- One cognition presents and realizes only `false`. -/
def selective : CognitionModel Unit Bool Unit where
  occurs _ := True
  novel _ := True
  presents _ o := o = false
  realizes _ o _ := o = false

theorem selective_is_pramana : selective.Pramana () := by
  refine ⟨trivial, trivial, ⟨false, rfl⟩, ?_⟩
  intro o presented
  exact ⟨(), presented⟩

theorem pramana_does_not_certify_every_object :
    selective.Pramana () ∧
      selective.CausallyEfficacious false ∧
      ¬ selective.CausallyEfficacious true := by
  refine ⟨selective_is_pramana, ⟨(), (), trivial, rfl, rfl⟩, ?_⟩
  rintro ⟨c, r, occurs, presented, realized⟩
  exact Bool.noConfusion presented

/-- A familiar successful cognition is reliable but fails the independent
novelty condition. -/
def familiar : CognitionModel Unit Unit Unit where
  occurs _ := True
  novel _ := False
  presents _ _ := True
  realizes _ _ _ := True

theorem reliability_and_efficacy_do_not_imply_pramana :
    familiar.occurs () ∧ familiar.Reliable () ∧
      familiar.CausallyEfficacious () ∧ ¬ familiar.Pramana () := by
  refine ⟨trivial, ?_, ⟨(), (), trivial, trivial, trivial⟩, ?_⟩
  · intro o presented
    exact ⟨(), trivial⟩
  · intro h
    exact h.2.1

/-- Presentation with no successful realization supplies neither reliability
nor a pramāṇa. -/
def deceptive : CognitionModel Unit Unit Unit where
  occurs _ := True
  novel _ := True
  presents _ _ := True
  realizes _ _ _ := False

theorem presentation_alone_is_not_reliability :
    deceptive.occurs () ∧ deceptive.novel () ∧ deceptive.presents () () ∧
      ¬ deceptive.Reliable () ∧ ¬ deceptive.Pramana () := by
  have notReliable : ¬ deceptive.Reliable () := by
    intro reliable
    obtain ⟨r, realized⟩ := reliable (o := ()) trivial
    exact realized
  refine ⟨trivial, trivial, trivial, notReliable, ?_⟩
  · intro h
    exact notReliable h.2.2.2

/-! ## Intrinsic and extrinsic grounds of inference -/

inductive ReasonKind where
  | intrinsic
  | extrinsic
  deriving DecidableEq, Repr

/-- An intrinsic argument carries an identity/inclusion reason and possession
of that reason at the disputed subject. -/
structure IntrinsicArgument (L : Type u) where
  reason : BuddhistComparativeLogic.Dharmakirti.SvabhavaHetu L
  subjectReason : reason.toAnumana.paksadharmata

/-- An extrinsic argument carries an effect reason, its explicit causal law,
and possession of the effect sign at the subject. -/
structure ExtrinsicArgument (L : Type u) where
  reason : BuddhistComparativeLogic.Dharmakirti.KaryaHetu L
  causalLaw : reason.causalLaw
  subjectReason : reason.toAnumana.paksadharmata

namespace IntrinsicArgument

variable {L : Type u} (argument : IntrinsicArgument L)

def kind : ReasonKind := .intrinsic

theorem certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
    argument.reason.toModel :=
  BuddhistComparativeLogic.PramanaSynthesis.ofSvabhavaHetu
    argument.reason argument.subjectReason

theorem establishes_pervasion : argument.reason.toModel.vyapti :=
  argument.certificate.pervasion

theorem intrinsic_argument_sound :
    argument.reason.sadhya argument.reason.paksa :=
  BuddhistComparativeLogic.PramanaSynthesis.deductive_sound argument.certificate

end IntrinsicArgument

namespace ExtrinsicArgument

variable {L : Type u} (argument : ExtrinsicArgument L)

def kind : ReasonKind := .extrinsic

theorem certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
    (BuddhistComparativeLogic.PramanaSynthesis.karyaModel argument.reason) :=
  BuddhistComparativeLogic.PramanaSynthesis.ofKaryaHetu
    argument.reason argument.causalLaw argument.subjectReason

theorem establishes_pervasion :
    (BuddhistComparativeLogic.PramanaSynthesis.karyaModel argument.reason).vyapti :=
  argument.certificate.pervasion

theorem extrinsic_argument_sound :
    argument.reason.sadhya argument.reason.paksa :=
  BuddhistComparativeLogic.PramanaSynthesis.deductive_sound argument.certificate

end ExtrinsicArgument

theorem intrinsic_and_extrinsic_are_distinct :
    ReasonKind.intrinsic ≠ ReasonKind.extrinsic := by
  decide

/-! ## Subject inference and public proof -/

/-- The subject-level proof contains subject possession and pervasion. -/
abbrev InferenceCertificate {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Model L) :=
  BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate m

/-- A public proof additionally supplies a positive comparison example. -/
abbrev PublicProof {L : Type u}
    (m : BuddhistComparativeLogic.Dharmakirti.Model L) :=
  BuddhistComparativeLogic.PramanaSynthesis.DialecticalCertificate m

theorem inference_certificate_sound {L : Type u}
    {m : BuddhistComparativeLogic.Dharmakirti.Model L}
    (certificate : InferenceCertificate m) : m.sadhya m.paksa :=
  BuddhistComparativeLogic.PramanaSynthesis.deductive_sound certificate

theorem public_proof_sound {L : Type u}
    {m : BuddhistComparativeLogic.Dharmakirti.Model L} (proof : PublicProof m) :
    m.sadhya m.paksa :=
  BuddhistComparativeLogic.PramanaSynthesis.dialectical_sound proof

theorem public_proof_has_three_marks {L : Type u}
    {m : BuddhistComparativeLogic.Dharmakirti.Model L} (proof : PublicProof m) :
    m.toAnumana.trairupya :=
  BuddhistComparativeLogic.PramanaSynthesis.dialectical_trairupya proof

theorem public_proof_has_valid_wheel {L : Type u}
    {m : BuddhistComparativeLogic.Dharmakirti.Model L} (proof : PublicProof m) :
    m.toAnumana.wheelVerdict = .valid :=
  BuddhistComparativeLogic.PramanaSynthesis.dialectical_wheel_valid proof

/-- The public comparison marks, even with a valid wheel cell, do not prove the
subject when the global pervasion premise is absent. -/
theorem comparison_marks_without_pervasion_do_not_settle_subject :
    ∃ a : BuddhistComparativeLogic.Hetucakra.Anumana BuddhistComparativeLogic.Hetucakra.Locus,
      a.trairupya ∧ a.wheelVerdict = .valid ∧ ¬ a.sadhya a.paksa :=
  BuddhistComparativeLogic.PramanaSynthesis.marks_and_valid_wheel_do_not_entail_subject

/-- Conversely, subject-level soundness does not manufacture a distinct
comparison example on a singleton domain. -/
theorem subject_inference_does_not_supply_public_example :
    InferenceCertificate BuddhistComparativeLogic.PramanaSynthesis.singletonSound ∧
      BuddhistComparativeLogic.PramanaSynthesis.singletonSound.sadhya
        BuddhistComparativeLogic.PramanaSynthesis.singletonSound.paksa ∧
      BuddhistComparativeLogic.PramanaSynthesis.singletonSound.toAnumana.wheelVerdict ≠
        .valid :=
  BuddhistComparativeLogic.PramanaSynthesis.sound_subject_inference_need_not_have_valid_wheel

/-! ## Conceptual exclusion and downstream revision remain separate -/

abbrev Concept (Object : Type u) := BuddhistComparativeLogic.Apoha.PredSet Object

def excludes {Object : Type u} (S : Concept Object) : Concept Object :=
  BuddhistComparativeLogic.Apoha.compl S

theorem every_concept_has_an_exclusion {Object : Type u}
    (S : Concept Object) :
    BuddhistComparativeLogic.Apoha.apohaPair S (excludes S) :=
  BuddhistComparativeLogic.Apoha.apoha_pair_underdetermined S

/-- Exclusion alone admits a complementary partner for every starting
extension; it does not select the starting extension. -/
theorem exclusion_is_extensionally_underdetermined
    {Object : Type u} [Nonempty Object] :
    (¬ ∃ S : Concept Object, S = excludes S) ∧
      (∀ S : Concept Object, ∃ N, BuddhistComparativeLogic.Apoha.apohaPair S N) :=
  BuddhistComparativeLogic.Apoha.circularity_is_underdetermination

/-- Even a pramāṇa in the operational model does not, by itself, impose a
policy for assimilating evidence in a later belief-revision process. -/
theorem pramana_does_not_force_belief_assimilation :
    selective.Pramana () ∧
      ¬ BuddhistComparativeLogic.BeliefRevision.ignored.ActiveAssimilation :=
  ⟨selective_is_pramana,
    BuddhistComparativeLogic.BeliefRevision.observation_without_assimilation.2.2.1⟩

end BuddhistComparativeLogic.Pramanavarttika
