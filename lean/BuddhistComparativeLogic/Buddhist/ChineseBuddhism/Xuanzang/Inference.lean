/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.Debate

/-!
# Acceptance scopes in paired Buddhist inferences

This module gives a small typed model for the acceptance conditions at issue
in discussions of Xuanzang's so-called "consciousness-only inference" and a
counter-inference associated with Wonhyo.  An argument records its subject,
reason, conclusion, pervasion, comparison witness, and the terms which both
parties accept for the exchange.  Soundness uses the semantic reason and
pervasion; shared terminology by itself does not establish the conclusion.

The source anchor is Mingjun Tang, “Materials for the Study of Xuanzang's
Inference of Consciousness-only,” *Wiener Zeitschrift für die Kunde
Südasiens* 56–57 (2015–2018), pp. 143–198, especially pp. 143–150 and the
edited materials labelled Texts 1.1, 1.9, and 5.2:
<https://www.austriaca.at/0xc1aa5572_0x003aa075.pdf>.  Tang prints the
thesis, reason, example, the three qualifications, and the opposed inference,
while also recording disputes about authenticity and interpretation.  The
formal fields below are a project-authored paraphrase of the argument roles;
no copyrighted translation is embedded here.

The historical three qualifications attached to Xuanzang's formulation, and
the exact force of Wonhyo's response, allow competing reconstructions.  The
formal `AcceptanceScope` below is an audit interface for such reconstructions,
not a claim that one interpretation is uniquely correct.  In particular, the
finite model at the end shows how two apparently opposed argument labels can
both pass after their domains and meanings have shifted.  A contradiction is
obtained only from an explicit common-domain consistency premise.
-/

namespace BuddhistComparativeLogic.XuanzangInference

universe u v

/-! ## Parties, vocabulary, and acceptance -/

inductive Party where
  | proponent
  | opponent
  deriving DecidableEq, Repr

/-- A public stance marker.  Polarity is syntactic until a shared semantic
consistency condition is supplied. -/
inductive Polarity where
  | thesis
  | counterthesis
  deriving DecidableEq, Repr

/-- Public names for the subject, reason, pervasion, and conclusion of an
exchange.  The names are kept apart from their semantic interpretation. -/
structure Vocabulary (L : Type u) (Claim : Type v) where
  subject : L
  subjectName : Claim
  reasonName : Claim
  pervasionName : Claim
  conclusionName : Claim

/-- A party-sensitive domain and commitment ledger.  Admission says that a
term may be used in the current exchange; it does not say that the named
claim is true. -/
structure AcceptanceScope (L : Type u) (Claim : Type v) where
  domain : L -> Prop
  accepts : Party -> Claim -> Prop
  interpretation : L -> Prop

namespace AcceptanceScope

variable {L : Type u} {Claim : Type v}

/-- The two parties accept the subject locus and all four pieces of public
argument vocabulary. -/
def JointlyEstablishes (scope : AcceptanceScope L Claim)
    (words : Vocabulary L Claim) : Prop :=
  scope.domain words.subject /\
    forall party,
      scope.accepts party words.subjectName /\
      scope.accepts party words.reasonName /\
      scope.accepts party words.pervasionName /\
      scope.accepts party words.conclusionName

/-- Read the public thesis positively or its counter-thesis negatively inside
one scope.  Opposite polarities can both hold only when their interpretations
or domains differ. -/
def reads (scope : AcceptanceScope L Claim) : Polarity -> L -> Prop
  | .thesis => scope.interpretation
  | .counterthesis => fun locus => ¬ scope.interpretation locus

end AcceptanceScope

/-! ## Qualified inference and soundness -/

/-- A nonvacuous inference relative to an explicit acceptance scope.  The
comparison field supplies a positive, non-subject locus in addition to the
subject-reason and domain-scoped pervasion obligations. -/
structure QualifiedAnumana (L : Type u) (Claim : Type v) where
  vocabulary : Vocabulary L Claim
  polarity : Polarity
  scope : AcceptanceScope L Claim
  reason : L -> Prop
  jointlyEstablished : scope.JointlyEstablishes vocabulary
  subjectReason : reason vocabulary.subject
  pervasion : forall x, scope.domain x -> reason x ->
    scope.reads polarity x
  comparison : exists x, x ≠ vocabulary.subject /\ scope.domain x /\
    reason x /\ scope.reads polarity x

namespace QualifiedAnumana

variable {L : Type u} {Claim : Type v}

def conclusion (argument : QualifiedAnumana L Claim) : L -> Prop :=
  argument.scope.reads argument.polarity

/-- Subject possession and pervasion yield the qualified argument's
conclusion.  No fact is extracted from lexical acceptance alone. -/
theorem sound (argument : QualifiedAnumana L Claim) :
    argument.conclusion argument.vocabulary.subject :=
  argument.pervasion argument.vocabulary.subject
    argument.jointlyEstablished.1 argument.subjectReason

/-- The public certificate exposes joint establishment together with the
semantic conclusion obtained from subject possession and pervasion.  The
first conjunct remains an audit of the exchange rather than a hidden truth
premise. -/
theorem joint_acceptance_reason_pervasion_conclusion
    (argument : QualifiedAnumana L Claim) :
    argument.scope.JointlyEstablishes argument.vocabulary /\
      argument.conclusion argument.vocabulary.subject :=
  ⟨argument.jointlyEstablished, argument.sound⟩

/-- The accepted semantic domain becomes the locus type of the repository
inference APIs.  This prevents a scoped pervasion from being silently read as
a global law over rejected loci. -/
abbrev Domain (argument : QualifiedAnumana L Claim) :=
  { locus : L // argument.scope.domain locus }

def subjectInDomain (argument : QualifiedAnumana L Claim) : argument.Domain :=
  ⟨argument.vocabulary.subject, argument.jointlyEstablished.1⟩

/-- Forget the dialectical names while retaining the exact semantic subject,
reason, and conclusion on the admitted subtype. -/
def toAnumana (argument : QualifiedAnumana L Claim) :
    BuddhistComparativeLogic.Hetucakra.Anumana argument.Domain where
  paksa := argument.subjectInDomain
  reason := fun locus => argument.reason locus.1
  sadhya := fun locus => argument.conclusion locus.1

@[simp] theorem toAnumana_paksadharmata
    (argument : QualifiedAnumana L Claim) :
    argument.toAnumana.paksadharmata :=
  argument.subjectReason

theorem toAnumana_anvaya (argument : QualifiedAnumana L Claim) :
    argument.toAnumana.anvaya := by
  rcases argument.comparison with
    ⟨x, distinct, inDomain, reason, conclusion⟩
  let comparison : argument.Domain := ⟨x, inDomain⟩
  have different : comparison ≠ argument.subjectInDomain := by
    intro equal
    exact distinct (congrArg Subtype.val equal)
  exact ⟨comparison, ⟨different, conclusion⟩, reason⟩

/-- The repository's Dharmakīrti model reads the stored pervasion literally
as global predicate inclusion. -/
def toDharmakirtiModel (argument : QualifiedAnumana L Claim) :
    BuddhistComparativeLogic.Dharmakirti.Model argument.Domain where
  toAnumana := argument.toAnumana
  vyapti := forall x : argument.Domain,
    argument.reason x.1 -> argument.conclusion x.1
  vyapti_iff := Iff.rfl

/-- A qualified argument supplies the repository's full dialectical
certificate, including its positive comparison example. -/
theorem toDialecticalCertificate (argument : QualifiedAnumana L Claim) :
    BuddhistComparativeLogic.PramanaSynthesis.DialecticalCertificate
      argument.toDharmakirtiModel where
  subjectReason := argument.subjectReason
  pervasion := fun locus reason =>
    argument.pervasion locus.1 locus.2 reason
  comparison := argument.toAnumana_anvaya

theorem sound_via_pramana (argument : QualifiedAnumana L Claim) :
    argument.conclusion argument.vocabulary.subject :=
  BuddhistComparativeLogic.PramanaSynthesis.dialectical_sound
    argument.toDialecticalCertificate

/-- The same semantic obligations instantiate the consequence used by the
Tibetan debate bridge.  This adapter does not identify truth with acceptance
in a party's ledger. -/
theorem debate_challenge_sound (argument : QualifiedAnumana L Claim) :
    BuddhistComparativeLogic.TibetanDebate.SoundUnder
      (BuddhistComparativeLogic.TibetanDebate.PramanaBridge.meaning
        argument.toDharmakirtiModel)
      BuddhistComparativeLogic.TibetanDebate.PramanaBridge.challenge :=
  BuddhistComparativeLogic.TibetanDebate.PramanaBridge.challenge_sound
    argument.toDharmakirtiModel

end QualifiedAnumana

/-! ## Counter-reasons and a shared-semantics boundary -/

/-- Two arguments presented as a thesis and counter-thesis.  Their shared
object-language type does not yet assert that their acceptance domains or
semantic predicates agree. -/
structure CounterReasonPair (L : Type u) (Claim : Type v) where
  thesis : QualifiedAnumana L Claim
  counter : QualifiedAnumana L Claim
  thesisPolarity : thesis.polarity = .thesis
  counterPolarity : counter.polarity = .counterthesis
  sameSubject : counter.vocabulary.subject = thesis.vocabulary.subject

namespace CounterReasonPair

variable {L : Type u} {Claim : Type v}

/-- The explicit conditions under which both members of a counter-reason pair
are read in one domain with one interpretation of their positive content.
Because the pair has opposite polarities, its second conclusion then reads as
the negation of the first content. -/
structure SharedSemantics (pair : CounterReasonPair L Claim) : Prop where
  sameDomain : forall x,
    pair.thesis.scope.domain x <-> pair.counter.scope.domain x
  sameInterpretation : forall x,
    pair.thesis.scope.domain x ->
    pair.counter.scope.domain x ->
    (pair.thesis.scope.interpretation x <->
      pair.counter.scope.interpretation x)

/-- The explicit consistency premise required to combine locally certified
opposite-polarity arguments. -/
def Consistent (pair : CounterReasonPair L Claim) : Prop :=
  forall x,
    pair.thesis.scope.domain x ->
    pair.counter.scope.domain x ->
    pair.thesis.conclusion x ->
    pair.counter.conclusion x -> False

/-- A common interpretation of opposite polarities supplies the consistency
condition, rather than merely assuming that two unrelated predicates clash. -/
theorem shared_semantics_consistent
    (pair : CounterReasonPair L Claim)
    (shared : pair.SharedSemantics) : pair.Consistent := by
  intro x thesisDomain counterDomain thesisConclusion counterConclusion
  have thesisMeaning : pair.thesis.scope.interpretation x := by
    simpa [QualifiedAnumana.conclusion, AcceptanceScope.reads,
      pair.thesisPolarity] using thesisConclusion
  have counterNegation : ¬ pair.counter.scope.interpretation x := by
    simpa [QualifiedAnumana.conclusion, AcceptanceScope.reads,
      pair.counterPolarity] using counterConclusion
  exact counterNegation
    ((shared.sameInterpretation x thesisDomain counterDomain).mp thesisMeaning)

/-- Sound opposed inferences cannot both inhabit one explicitly consistent
domain at their common subject. -/
theorem not_both_sound_under_shared_semantics
    (pair : CounterReasonPair L Claim)
    (shared : pair.SharedSemantics)
    (consistency : pair.Consistent) : False := by
  have thesisDomain := pair.thesis.jointlyEstablished.1
  have counterDomain :
      pair.counter.scope.domain pair.thesis.vocabulary.subject :=
    (shared.sameDomain pair.thesis.vocabulary.subject).mp thesisDomain
  have thesisConclusion := pair.thesis.sound
  have counterConclusionAtCounter := pair.counter.sound
  have counterConclusion :
      pair.counter.conclusion pair.thesis.vocabulary.subject := by
    simpa [pair.sameSubject] using counterConclusionAtCounter
  exact consistency pair.thesis.vocabulary.subject thesisDomain
    counterDomain thesisConclusion counterConclusion

theorem shared_interpretation_precludes_both
    (pair : CounterReasonPair L Claim)
    (shared : pair.SharedSemantics) : False :=
  pair.not_both_sound_under_shared_semantics shared
    (pair.shared_semantics_consistent shared)

end CounterReasonPair

/-! ## A finite shifted-scope countermodel -/

inductive DemoLocus where
  | disputed
  | positiveExample
  | counterExample
  deriving DecidableEq, Repr

inductive DemoClaim where
  | subject
  | positiveReason
  | positivePervasion
  | positiveConclusion
  | counterReason
  | counterPervasion
  | counterConclusion
  deriving DecidableEq, Repr

open DemoLocus DemoClaim

def thesisVocabulary : Vocabulary DemoLocus DemoClaim where
  subject := .disputed
  subjectName := .subject
  reasonName := .positiveReason
  pervasionName := .positivePervasion
  conclusionName := .positiveConclusion

def counterVocabulary : Vocabulary DemoLocus DemoClaim where
  subject := .disputed
  subjectName := .subject
  reasonName := .counterReason
  pervasionName := .counterPervasion
  conclusionName := .counterConclusion

/-- The thesis admits the disputed locus and its positive comparison locus. -/
def thesisScope : AcceptanceScope DemoLocus DemoClaim where
  domain := fun locus => locus ≠ .counterExample
  accepts := fun _ claim =>
    claim = .subject \/ claim = .positiveReason \/
      claim = .positivePervasion \/ claim = .positiveConclusion
  interpretation := fun locus => locus ≠ .counterExample

/-- The counter-scope admits the disputed locus and a different comparison
locus, with a separate public vocabulary. -/
def counterScope : AcceptanceScope DemoLocus DemoClaim where
  domain := fun locus => locus ≠ .positiveExample
  accepts := fun _ claim =>
    claim = .subject \/ claim = .counterReason \/
      claim = .counterPervasion \/ claim = .counterConclusion
  interpretation := fun locus => locus = .positiveExample

def thesisArgument : QualifiedAnumana DemoLocus DemoClaim where
  vocabulary := thesisVocabulary
  polarity := .thesis
  scope := thesisScope
  reason := fun locus => locus ≠ .counterExample
  jointlyEstablished := by
    constructor
    · simp [thesisScope, thesisVocabulary]
    · intro party
      exact ⟨Or.inl rfl, Or.inr (Or.inl rfl),
        Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl))⟩
  subjectReason := by simp [thesisVocabulary]
  pervasion := by
    intro locus _ reason
    exact reason
  comparison :=
    ⟨.positiveExample, by decide, by simp [thesisScope], by decide,
      by simp [AcceptanceScope.reads, thesisScope]⟩

def counterArgument : QualifiedAnumana DemoLocus DemoClaim where
  vocabulary := counterVocabulary
  polarity := .counterthesis
  scope := counterScope
  reason := fun locus => locus ≠ .positiveExample
  jointlyEstablished := by
    constructor
    · simp [counterScope, counterVocabulary]
    · intro party
      exact ⟨Or.inl rfl, Or.inr (Or.inl rfl),
        Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl))⟩
  subjectReason := by simp [counterVocabulary]
  pervasion := by
    intro locus _ reason positive
    exact reason positive
  comparison :=
    ⟨.counterExample, by decide, by simp [counterScope], by decide,
      by simp [AcceptanceScope.reads, counterScope]⟩

def shiftedPair : CounterReasonPair DemoLocus DemoClaim where
  thesis := thesisArgument
  counter := counterArgument
  thesisPolarity := rfl
  counterPolarity := rfl
  sameSubject := rfl

/-- The two finite scopes disagree on both comparison loci. -/
theorem finite_scopes_are_distinct :
    thesisScope.domain .positiveExample /\
      ¬ counterScope.domain .positiveExample /\
      counterScope.domain .counterExample /\
      ¬ thesisScope.domain .counterExample := by
  simp [thesisScope, counterScope]

/-- Both scoped inferences are inhabited and locally sound, but they cannot
be combined with the common-domain consistency certificate.  This is the
formal reason that changing an acceptance scope blocks the immediate
contradiction. -/
theorem shifted_scopes_allow_both_local_inferences :
    Nonempty (CounterReasonPair DemoLocus DemoClaim) /\
      thesisArgument.conclusion thesisArgument.vocabulary.subject /\
      counterArgument.conclusion counterArgument.vocabulary.subject /\
      thesisScope.domain .positiveExample /\
      ¬ counterScope.domain .positiveExample /\
      ¬ shiftedPair.SharedSemantics := by
  refine ⟨⟨shiftedPair⟩, thesisArgument.sound,
    counterArgument.sound, finite_scopes_are_distinct.1,
    finite_scopes_are_distinct.2.1, ?_⟩
  intro shared
  have thesisDomain : thesisScope.domain .disputed := by
    simp [thesisScope]
  have counterDomain : counterScope.domain .disputed := by
    simp [counterScope]
  have agreement :=
    shared.sameInterpretation .disputed thesisDomain counterDomain
  have positive : thesisScope.interpretation .disputed := by
    simp [thesisScope]
  have negative : ¬ counterScope.interpretation .disputed := by
    simp [counterScope]
  exact negative (agreement.mp positive)

end BuddhistComparativeLogic.XuanzangInference
