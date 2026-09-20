/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.RecensionAlignment
import BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.Definitions
import BuddhistComparativeLogic.Buddhist.HeartSutra.PremiseCertificates
import BuddhistComparativeLogic.Buddhist.Pramana.Tattvasamgraha

/-!
# Five-part commentary certificates inspired by the Vyākhyāyukti

This module gives a typed audit of five tasks associated with Vasubandhu's
*Vyākhyāyukti*: stating a purpose (`prayojana`), giving a synopsis
(`piṇḍārtha`), explaining words (`padārtha`), locating a passage in its
discourse (`anusandhi`), and answering objections (`codyaparihāra`).  The
formal certificate is a checklist whose witnesses remain visible.  It is not
an edition or translation of the treatise, and it does not claim that every
historical commentator formulates the five tasks in exactly this way.

Certification establishes coverage relative to a supplied framework.  It
does not establish that the framework selects a unique interpretation or
that its interpretation is true.  The finite model below has two distinct
readings that each meet all five obligations, and an independent truth
valuation accepts only one.  This is a boundary theorem about the formal
checklist, not a historical verdict about either reading.

Source mapping (accessed 2026-09-19): Jong Cheol Lee's *The Tibetan Text of
the Vyākhyāyukti of Vasubandhu: Critically Edited from the Cone, Derge,
Narthang and Peking Editions* (Sankibo Press, 2001) fixes the Tibetan edition.
Makio Ueno, “The Buddha's Words and Their Interpretations in Vasubandhu's
Vyākhyāyukti” (Ōtani University, 2021), pp. 95–96, reproduces and translates
the first *saṃgrahaśloka* listing purpose, synopsis, word meaning, connection,
and response to objections
(https://www.otani.ac.jp/news/2021/u10fi9000000q5jn-att/nab3mq000008ctlv.pdf).
The University of Virginia Mandala overview locates the five components at
Tibetan folio 30b (https://texts.mandala.library.virginia.edu/book_pubreader/15729).
The Sanskrit task names are retained, while the Lean predicates and their
English descriptions are project-authored paraphrases; the certificate is a
modern checklist, not a translation of the treatise.
-/

namespace BuddhistComparativeLogic.Vyakhyayukti

universe u v w x y z q

/-! ## The five auditable obligations -/

/-- A commentary framework keeps textual incidence, interpretive judgments,
discourse connection, and dialectical response as separate relations. -/
structure CommentaryFramework
    (Passage : Type u) (Term : Type v) (Meaning : Type w)
    (Claim : Type x) (Objection : Type y) (Reply : Type z) where
  termOccurs : Passage -> Term -> Prop
  purposeFits : Passage -> Claim -> Prop
  synopsisFits : Passage -> Claim -> Prop
  assignsMeaning : Passage -> Term -> Meaning -> Prop
  opens : Passage -> Prop
  connects : Passage -> Passage -> Prop
  raises : Passage -> Objection -> Prop
  replies : Passage -> Objection -> Reply -> Prop
  resolves : Objection -> Reply -> Prop

namespace CommentaryFramework

variable {Passage : Type u} {Term : Type v} {Meaning : Type w}
  {Claim : Type x} {Objection : Type y} {Reply : Type z}
  (framework : CommentaryFramework Passage Term Meaning Claim Objection Reply)

/-- The purpose task has at least one explicit, framework-approved witness. -/
def PrayojanaCovered (passage : Passage) : Prop :=
  exists claim, framework.purposeFits passage claim

/-- The synopsis task has at least one explicit, framework-approved witness. -/
def PindarthaCovered (passage : Passage) : Prop :=
  exists claim, framework.synopsisFits passage claim

/-- Every term which the framework says occurs receives a meaning witness. -/
def PadarthaCovered (passage : Passage) : Prop :=
  forall term, framework.termOccurs passage term ->
    exists meaning, framework.assignsMeaning passage term meaning

/-- A passage is placed in discourse either by being admitted as an opening
or by carrying a witnessed connection from an earlier passage. -/
def AnusandhiCovered (passage : Passage) : Prop :=
  framework.opens passage \/
    exists previous, framework.connects previous passage

/-- Every admitted objection receives a recorded reply which resolves it
according to the separately supplied resolution relation. -/
def CodyapariharaCovered (passage : Passage) : Prop :=
  forall objection, framework.raises passage objection ->
    exists reply, framework.replies passage objection reply /\
      framework.resolves objection reply

end CommentaryFramework

/-- A proof-bearing record of all five commentary tasks for one passage. -/
structure CommentaryCertificate
    {Passage : Type u} {Term : Type v} {Meaning : Type w}
    {Claim : Type x} {Objection : Type y} {Reply : Type z}
    (framework : CommentaryFramework Passage Term Meaning Claim Objection Reply)
    (passage : Passage) : Prop where
  prayojana : framework.PrayojanaCovered passage
  pindartha : framework.PindarthaCovered passage
  padartha : framework.PadarthaCovered passage
  anusandhi : framework.AnusandhiCovered passage
  codyaparihara : framework.CodyapariharaCovered passage

namespace CommentaryCertificate

variable {Passage : Type u} {Term : Type v} {Meaning : Type w}
  {Claim : Type x} {Objection : Type y} {Reply : Type z}
  {framework : CommentaryFramework Passage Term Meaning Claim Objection Reply}
  {passage : Passage}

/-- The word-meaning field can be consumed without unpacking the other four
parts of the certificate. -/
theorem meaningWitness (certificate : CommentaryCertificate framework passage)
    {term : Term} (occurs : framework.termOccurs passage term) :
    exists meaning, framework.assignsMeaning passage term meaning :=
  certificate.padartha term occurs

/-- The objection/reply field exposes both the recorded response and its
resolution judgment. -/
theorem replyWitness (certificate : CommentaryCertificate framework passage)
    {objection : Objection} (raised : framework.raises passage objection) :
    exists reply, framework.replies passage objection reply /\
      framework.resolves objection reply :=
  certificate.codyaparihara objection raised

/-- Reposition a locally certified passage after an explicitly connected
predecessor.  The other four witnesses are preserved, while `anusandhi` is
rebuilt from the boundary edge. -/
theorem after (certificate : CommentaryCertificate framework passage)
    {previous : Passage} (connection : framework.connects previous passage) :
    CommentaryCertificate framework passage where
  prayojana := certificate.prayojana
  pindartha := certificate.pindartha
  padartha := certificate.padartha
  anusandhi := Or.inr ⟨previous, connection⟩
  codyaparihara := certificate.codyaparihara

end CommentaryCertificate

/-! ## Adjacent composition and coverage -/

/-- A two-passage section stores both five-part certificates and the explicit
discourse connection between them.  Adjacency is not inferred merely from
the two local certificates. -/
structure AdjacentComposition
    {Passage : Type u} {Term : Type v} {Meaning : Type w}
    {Claim : Type x} {Objection : Type y} {Reply : Type z}
    (framework : CommentaryFramework Passage Term Meaning Claim Objection Reply)
    (left right : Passage) : Prop where
  leftCertificate : CommentaryCertificate framework left
  rightCertificate : CommentaryCertificate framework right
  connection : framework.connects left right

namespace AdjacentComposition

variable {Passage : Type u} {Term : Type v} {Meaning : Type w}
  {Claim : Type x} {Objection : Type y} {Reply : Type z}
  {framework : CommentaryFramework Passage Term Meaning Claim Objection Reply}
  {left right : Passage}

/-- Composition of adjacent certified passages preserves both complete local
certificates and records the additional `anusandhi` edge. -/
theorem composeAdjacent
    (leftCertificate : CommentaryCertificate framework left)
    (rightCertificate : CommentaryCertificate framework right)
    (connection : framework.connects left right) :
    AdjacentComposition framework left right where
  leftCertificate := leftCertificate
  rightCertificate := rightCertificate.after connection
  connection := connection

/-- Every member of the two-passage section is covered by a five-part
certificate. -/
theorem covers (composition : AdjacentComposition framework left right)
    {passage : Passage} (member : passage = left \/ passage = right) :
    CommentaryCertificate framework passage := by
  cases member with
  | inl isLeft => simpa [isLeft] using composition.leftCertificate
  | inr isRight => simpa [isRight] using composition.rightCertificate

/-- The composed section exposes all ten local obligations together with the
cross-passage connection. -/
theorem preservesFivePartCoverage
    (composition : AdjacentComposition framework left right) :
    framework.PrayojanaCovered left /\
      framework.PindarthaCovered left /\
      framework.PadarthaCovered left /\
      framework.AnusandhiCovered left /\
      framework.CodyapariharaCovered left /\
      framework.connects left right /\
      framework.PrayojanaCovered right /\
      framework.PindarthaCovered right /\
      framework.PadarthaCovered right /\
      framework.AnusandhiCovered right /\
      framework.CodyapariharaCovered right := by
  exact ⟨composition.leftCertificate.prayojana,
    composition.leftCertificate.pindartha,
    composition.leftCertificate.padartha,
    composition.leftCertificate.anusandhi,
    composition.leftCertificate.codyaparihara,
    composition.connection,
    composition.rightCertificate.prayojana,
    composition.rightCertificate.pindartha,
    composition.rightCertificate.padartha,
    composition.rightCertificate.anusandhi,
    composition.rightCertificate.codyaparihara⟩

/-- The composed section's right-hand `anusandhi` is furnished by the actual
boundary edge, independently of how the right passage was positioned before
composition. -/
theorem rightAnusandhiFromBoundary
    (composition : AdjacentComposition framework left right) :
    exists previous, previous = left /\
      framework.connects previous right :=
  ⟨left, rfl, composition.connection⟩

end AdjacentComposition

/-! ## Typed adapters to existing repository interfaces -/

/-- Structural recension coverage and commentary coverage remain separate
proofs.  This adapter joins them without identifying aligned source units
with target passages. -/
structure AlignedCommentary
    {Passage : Type} {Term : Type v} {Meaning : Type w}
    {Claim : Type x} {Objection : Type y} {Reply : Type z}
    (Source : Type) [DecidableEq Source] [DecidableEq Passage]
    (framework : CommentaryFramework Passage Term Meaning Claim Objection Reply) where
  alignment : BuddhistComparativeLogic.Alignment Source Passage
  alignmentValid : alignment.Valid
  certifiesRequired : forall passage, passage ∈ alignment.required ->
    CommentaryCertificate framework passage

namespace AlignedCommentary

variable {Passage : Type} {Term : Type v} {Meaning : Type w}
  {Claim : Type x} {Objection : Type y} {Reply : Type z}
  {Source : Type} [DecidableEq Source] [DecidableEq Passage]
  {framework : CommentaryFramework Passage Term Meaning Claim Objection Reply}

/-- A valid aligned commentary simultaneously exposes structural source and
required-target coverage from `RecensionAlignment`. -/
theorem structuralCoverage
    (adapter : AlignedCommentary Source framework) :
    adapter.alignment.SourceCovered /\
      adapter.alignment.RequiredCovered :=
  adapter.alignment.coverage_of_valid adapter.alignmentValid

/-- Any required aligned target carries the five-part certificate supplied
by the commentary layer. -/
theorem requiredTargetCovered
    (adapter : AlignedCommentary Source framework)
    {passage : Passage} (required : passage ∈ adapter.alignment.required) :
    CommentaryCertificate framework passage :=
  adapter.certifiesRequired passage required

end AlignedCommentary

/-- Package certificates for all six target frame-parts with the checked
longer-recension alignment. -/
def ofLongerRecension
    {Term : Type v} {Meaning : Type w} {Claim : Type x}
    {Objection : Type y} {Reply : Type z}
    (framework : CommentaryFramework BuddhistComparativeLogic.FramePart Term Meaning
      Claim Objection Reply)
    (certificates : forall passage, passage ∈ BuddhistComparativeLogic.longFrame ->
      CommentaryCertificate framework passage) :
    AlignedCommentary BuddhistComparativeLogic.LongerFrameUnit framework where
  alignment := BuddhistComparativeLogic.longerFrameAlignment
  alignmentValid := BuddhistComparativeLogic.longer_frame_alignment_valid
  certifiesRequired := certificates

/-- A definition certificate can discharge one `padārtha` obligation when
the commentary explicitly assigns the certified definiendum to the term.
The adapter preserves the definition standard and basis witness. -/
structure DefinitionPadarthaAdapter
    {Passage : Type u} {Term : Type v} {Object : Type w}
    {Claim : Type y} {Objection : Type z}
    {Reply : Type q}
    (Feature : Type x)
    (framework : CommentaryFramework Passage Term
      (BuddhistComparativeLogic.Apoha.PredSet Object) Claim Objection Reply)
    (passage : Passage) (term : Term) where
  standard : BuddhistComparativeLogic.TibetanDefinitions.DefinitionStandard Feature
  triad : BuddhistComparativeLogic.TibetanDefinitions.DefinitionTriad Object Feature
  certificate : BuddhistComparativeLogic.TibetanDefinitions.DefinitionCertificate
    standard triad
  occurs : framework.termOccurs passage term
  assignment : framework.assignsMeaning passage term triad.definiendum

namespace DefinitionPadarthaAdapter

variable {Passage : Type u} {Term : Type v} {Object : Type w}
  {Feature : Type x} {Claim : Type y} {Objection : Type z}
  {Reply : Type q}
  {framework : CommentaryFramework Passage Term
    (BuddhistComparativeLogic.Apoha.PredSet Object) Claim Objection Reply}
  {passage : Passage} {term : Term}

/-- The adapter is an actual word-meaning witness in the commentary API. -/
theorem suppliesMeaning
    (adapter : DefinitionPadarthaAdapter Feature framework passage term) :
    exists meaning, framework.assignsMeaning passage term meaning :=
  ⟨adapter.triad.definiendum, adapter.assignment⟩

/-- The assigned predicate is inhabited at the definition certificate's
basis, so the adapter does not supply an empty gloss by construction. -/
theorem classifiesBasis
    (adapter : DefinitionPadarthaAdapter Feature framework passage term) :
    adapter.triad.definiendum adapter.triad.basis :=
  adapter.certificate.basis_is_definiendum

end DefinitionPadarthaAdapter

/-- A scoped debate certificate supplies a typed objection and reply for the
commentary framework.  The final field keeps the framework's notion of
resolution separate from the debate registry's refutation theorem. -/
structure DebateReplyAdapter
    {Passage : Type u} {Term : Type v} {Meaning : Type w}
    {Claim : Type x} {D : Type y}
    (framework : CommentaryFramework Passage Term Meaning Claim
      (D -> Prop) (D -> Prop))
    (passage : Passage) (subject : D) where
  debate : BuddhistComparativeLogic.Tattvasamgraha.DebateCertificate D subject
  raised : framework.raises passage debate.opponentThesis
  recorded : framework.replies passage debate.opponentThesis debate.result
  resolution : framework.resolves debate.opponentThesis debate.result

namespace DebateReplyAdapter

variable {Passage : Type u} {Term : Type v} {Meaning : Type w}
  {Claim : Type x} {D : Type y}
  {framework : CommentaryFramework Passage Term Meaning Claim
    (D -> Prop) (D -> Prop)}
  {passage : Passage} {subject : D}

/-- The Tattvasaṃgraha adapter exposes a recorded resolving reply together
with its positive conclusion and rejection of the opponent thesis. -/
theorem suppliesResolvedReply
    (adapter : DebateReplyAdapter framework passage subject) :
    exists reply, framework.replies passage adapter.debate.opponentThesis reply /\
      framework.resolves adapter.debate.opponentThesis reply /\
      reply subject /\
      ¬ adapter.debate.opponentThesis subject :=
  ⟨adapter.debate.result, adapter.recorded, adapter.resolution,
    adapter.debate.result_at_subject, adapter.debate.rejects_opponent⟩

end DebateReplyAdapter

/-! ## A finite pair of distinct certified interpretations -/

inductive SamplePassage where
  | introduction
  | central
  deriving DecidableEq, Repr

inductive SampleTerm where
  | form
  | emptiness
  deriving DecidableEq, Repr

inductive SampleMeaning where
  | aggregate
  | absenceOfOwnBeing
  deriving DecidableEq, Repr

inductive RelationReading where
  | identity
  | nonSeparation
  deriving DecidableEq, Repr

structure SampleReading where
  relation : RelationReading
  deriving DecidableEq, Repr

inductive SampleClaim where
  | orientation
  | centralRelation (reading : RelationReading)
  deriving DecidableEq, Repr

inductive SampleObjection where
  | overstatement
  deriving DecidableEq, Repr

inductive SampleReply where
  | qualified (reading : RelationReading)
  deriving DecidableEq, Repr

open SamplePassage SampleTerm SampleMeaning RelationReading

def identityReading : SampleReading := ⟨.identity⟩
def nonSeparationReading : SampleReading := ⟨.nonSeparation⟩

def sampleTermMeaning : SampleTerm -> SampleMeaning
  | .form => .aggregate
  | .emptiness => .absenceOfOwnBeing

/-- The finite text inventory is fixed before a reading is selected. -/
def sampleTermOccurs : SamplePassage -> SampleTerm -> Prop
  | .introduction, .form => True
  | .introduction, .emptiness => False
  | .central, _ => True

/-- The opening has one admitted orienting claim.  The central passage admits
either of the two finite relation claims under one shared checklist. -/
def sampleClaimFits : SamplePassage -> SampleClaim -> Prop
  | .introduction, claim => claim = .orientation
  | .central, claim => exists relation,
      claim = .centralRelation relation

def sampleRaises : SamplePassage -> SampleObjection -> Prop
  | .introduction, _ => False
  | .central, objection => objection = .overstatement

def sampleReplies : SamplePassage -> SampleObjection -> SampleReply -> Prop
  | .introduction, _, _ => False
  | .central, objection, reply =>
      objection = .overstatement /\
        exists relation, reply = .qualified relation

def sampleResolves : SampleObjection -> SampleReply -> Prop
  | .overstatement, reply =>
      exists relation, reply = .qualified relation

/-- A single interpretation-independent checklist admits both candidate
synopses and both qualified replies.  Candidate-specific witnesses are stored
later in `InterpretationCertificate`; the framework itself never changes. -/
def sharedSampleFramework :
    CommentaryFramework SamplePassage SampleTerm SampleMeaning SampleClaim
      SampleObjection SampleReply where
  termOccurs := sampleTermOccurs
  purposeFits := sampleClaimFits
  synopsisFits := sampleClaimFits
  assignsMeaning := fun _ term meaning => meaning = sampleTermMeaning term
  opens := fun passage => passage = .introduction
  connects := fun left right =>
    left = .introduction /\ right = .central
  raises := sampleRaises
  replies := sampleReplies
  resolves := sampleResolves

/-- The proof term selects the synopsis and reply associated with `reading`,
but checks them against the one fixed `sharedSampleFramework`. -/
theorem sampleCertificate (reading : SampleReading) (passage : SamplePassage) :
    CommentaryCertificate sharedSampleFramework passage where
  prayojana := by
    cases passage with
    | introduction => exact ⟨.orientation, rfl⟩
    | central =>
        exact ⟨.centralRelation reading.relation,
          ⟨reading.relation, rfl⟩⟩
  pindartha := by
    cases passage with
    | introduction => exact ⟨.orientation, rfl⟩
    | central =>
        exact ⟨.centralRelation reading.relation,
          ⟨reading.relation, rfl⟩⟩
  padartha := by
    intro term _
    exact ⟨sampleTermMeaning term, rfl⟩
  anusandhi := by
    cases passage with
    | introduction => exact Or.inl rfl
    | central => exact Or.inr ⟨.introduction, rfl, rfl⟩
  codyaparihara := by
    cases passage with
    | introduction =>
        intro _ raised
        exact False.elim raised
    | central =>
        intro objection raised
        refine ⟨.qualified reading.relation, ?_, ?_⟩
        · exact ⟨raised, ⟨reading.relation, rfl⟩⟩
        · subst objection
          exact ⟨reading.relation, rfl⟩

/-- A candidate interpretation identifies the particular synopsis and reply
it uses inside the fixed framework.  The generic five-part certificate alone
would hide those existential witnesses. -/
structure InterpretationCertificate (reading : SampleReading) : Prop where
  fivePart : CommentaryCertificate sharedSampleFramework .central
  selectedSynopsis : sharedSampleFramework.synopsisFits .central
    (.centralRelation reading.relation)
  selectedReply : sharedSampleFramework.replies .central .overstatement
    (.qualified reading.relation)
  selectedResolution : sharedSampleFramework.resolves .overstatement
    (.qualified reading.relation)

theorem sampleInterpretationCertificate (reading : SampleReading) :
    InterpretationCertificate reading where
  fivePart := sampleCertificate reading .central
  selectedSynopsis := ⟨reading.relation, rfl⟩
  selectedReply := ⟨rfl, ⟨reading.relation, rfl⟩⟩
  selectedResolution := ⟨reading.relation, rfl⟩

theorem identityCentralCertificate :
    CommentaryCertificate sharedSampleFramework .central :=
  (sampleInterpretationCertificate identityReading).fivePart

theorem nonSeparationCentralCertificate :
    CommentaryCertificate sharedSampleFramework .central :=
  (sampleInterpretationCertificate nonSeparationReading).fivePart

theorem identityInterpretationCertificate :
    InterpretationCertificate identityReading :=
  sampleInterpretationCertificate identityReading

theorem nonSeparationInterpretationCertificate :
    InterpretationCertificate nonSeparationReading :=
  sampleInterpretationCertificate nonSeparationReading

/-- The existing premise-certificate interface attaches a checked Lean name
to one five-part certificate without treating provenance metadata as proof. -/
def identityCentralEvidence :
    BuddhistComparativeLogic.PremiseCertificates.Certified
      (CommentaryCertificate sharedSampleFramework .central) :=
  BuddhistComparativeLogic.PremiseCertificates.certifyInternal
    ``BuddhistComparativeLogic.Vyakhyayukti.identityCentralCertificate
    identityCentralCertificate

theorem identityAdjacentSection :
    AdjacentComposition sharedSampleFramework
      .introduction .central :=
  AdjacentComposition.composeAdjacent
    (sampleCertificate identityReading .introduction)
    identityCentralEvidence.fact
    ⟨rfl, rfl⟩

/-- The positive composition is nonvacuous: both passages are certified and
the declared introduction-to-central connection is present. -/
theorem adjacent_sample_preserves_five_part_coverage :
    CommentaryCertificate sharedSampleFramework .introduction /\
      CommentaryCertificate sharedSampleFramework .central /\
      sharedSampleFramework.connects .introduction .central /\
      (exists previous, previous = SamplePassage.introduction /\
        sharedSampleFramework.connects previous .central) :=
  ⟨identityAdjacentSection.leftCertificate,
    identityAdjacentSection.rightCertificate,
    identityAdjacentSection.connection,
    identityAdjacentSection.rightAnusandhiFromBoundary⟩

def Certifiable (reading : SampleReading) : Prop :=
  InterpretationCertificate reading

def DistinctReading (left right : SampleReading) : Prop :=
  left.relation ≠ right.relation

/-- Truth is deliberately external to the five-part checklist.  This tiny
valuation chooses the identity reading solely to exhibit the logical
non-entailment; it makes no historical claim that identity is correct. -/
def TrueInSampleValuation (reading : SampleReading) : Prop :=
  reading = identityReading

theorem sample_relation_readings_distinct :
    DistinctReading identityReading nonSeparationReading := by
  change RelationReading.identity ≠ RelationReading.nonSeparation
  decide

theorem sample_readings_distinct :
    identityReading ≠ nonSeparationReading := by
  intro equality
  exact sample_relation_readings_distinct
    (congrArg SampleReading.relation equality)

/-- Both interpretation records discharge exactly the same framework type;
their selected synopsis and reply witnesses differ with their readings. -/
theorem distinct_candidates_share_one_checklist :
    CommentaryCertificate sharedSampleFramework .central /\
      CommentaryCertificate sharedSampleFramework .central /\
      identityReading ≠ nonSeparationReading /\
      DistinctReading identityReading nonSeparationReading :=
  ⟨identityInterpretationCertificate.fivePart,
    nonSeparationInterpretationCertificate.fivePart,
    sample_readings_distinct, sample_relation_readings_distinct⟩

/-- An inhabited finite model contains two distinct readings, each with a
complete certificate, while the independent valuation rejects one of them. -/
theorem two_distinct_interpretations_are_certified :
    Nonempty SampleReading /\
      Certifiable identityReading /\
      Certifiable nonSeparationReading /\
      DistinctReading identityReading nonSeparationReading /\
      TrueInSampleValuation identityReading /\
      ¬ TrueInSampleValuation nonSeparationReading := by
  exact ⟨⟨identityReading⟩, identityInterpretationCertificate,
    nonSeparationInterpretationCertificate, sample_relation_readings_distinct,
    rfl, by
      change nonSeparationReading ≠ identityReading
      intro equality
      have relationEquality := congrArg SampleReading.relation equality
      exact RelationReading.noConfusion relationEquality⟩

/-- Five-part certification alone cannot be a uniqueness principle. -/
theorem certification_does_not_entail_uniqueness :
    ¬ (forall left right, Certifiable left -> Certifiable right ->
      left = right) := by
  intro unique
  have equality := unique identityReading nonSeparationReading
    identityInterpretationCertificate nonSeparationInterpretationCertificate
  exact sample_relation_readings_distinct
    (congrArg SampleReading.relation equality)

/-- Five-part certification alone cannot entail an independently specified
truth valuation. -/
theorem certification_does_not_entail_truth :
    ¬ (forall reading, Certifiable reading ->
      TrueInSampleValuation reading) := by
  intro sound
  exact two_distinct_interpretations_are_certified.2.2.2.2.2
    (sound nonSeparationReading nonSeparationInterpretationCertificate)

/-! ## Executable instances of the typed adapters -/

inductive FrameTerm where
  | setting
  | samadhi
  | inquiry
  | teaching
  | approval
  | joy
  deriving DecidableEq, Repr

inductive FrameClaim where
  | purpose (passage : BuddhistComparativeLogic.FramePart)
  | synopsis (passage : BuddhistComparativeLogic.FramePart)
  deriving DecidableEq, Repr

inductive FrameObjection where
  | roleUnclear (passage : BuddhistComparativeLogic.FramePart)
  deriving DecidableEq, Repr

inductive FrameReply where
  | roleExplained (passage : BuddhistComparativeLogic.FramePart)
  deriving DecidableEq, Repr

def frameTermFor : BuddhistComparativeLogic.FramePart -> FrameTerm
  | .nidana => .setting
  | .enterSamadhi => .samadhi
  | .question => .inquiry
  | .answer => .teaching
  | .endorsement => .approval
  | .rejoicing => .joy

/-- This frame-part framework carries a distinct term, speech-kind meaning,
purpose, synopsis, and objection/reply pair for each passage.  Its discourse
edge is the immediate-successor equation in the checked frame rank. -/
def frameFramework : CommentaryFramework BuddhistComparativeLogic.FramePart FrameTerm
    BuddhistComparativeLogic.SpeechKind FrameClaim FrameObjection FrameReply where
  termOccurs := fun passage term => term = frameTermFor passage
  purposeFits := fun passage claim => claim = .purpose passage
  synopsisFits := fun passage claim => claim = .synopsis passage
  assignsMeaning := fun passage term meaning =>
    term = frameTermFor passage /\ meaning = BuddhistComparativeLogic.kindOf passage
  opens := fun passage => passage = .nidana
  connects := fun left right =>
    BuddhistComparativeLogic.framePartEdition.rank left + 1 =
      BuddhistComparativeLogic.framePartEdition.rank right
  raises := fun passage objection => objection = .roleUnclear passage
  replies := fun passage objection reply =>
    objection = .roleUnclear passage /\ reply = .roleExplained passage
  resolves := fun objection reply => exists passage,
    objection = .roleUnclear passage /\ reply = .roleExplained passage

theorem frameCertificate (passage : BuddhistComparativeLogic.FramePart) :
    CommentaryCertificate frameFramework passage where
  prayojana := ⟨.purpose passage, rfl⟩
  pindartha := ⟨.synopsis passage, rfl⟩
  padartha := by
    intro term occurs
    exact ⟨BuddhistComparativeLogic.kindOf passage, occurs, rfl⟩
  anusandhi := by
    cases passage with
    | nidana => exact Or.inl rfl
    | enterSamadhi => exact Or.inr ⟨.nidana, rfl⟩
    | question => exact Or.inr ⟨.enterSamadhi, rfl⟩
    | answer => exact Or.inr ⟨.question, rfl⟩
    | endorsement => exact Or.inr ⟨.answer, rfl⟩
    | rejoicing => exact Or.inr ⟨.endorsement, rfl⟩
  codyaparihara := by
    intro objection raised
    refine ⟨.roleExplained passage, ⟨raised, rfl⟩, ?_⟩
    exact ⟨passage, raised, rfl⟩

theorem answer_frame_certificate_is_content_bearing :
    frameFramework.termOccurs .answer (frameTermFor .answer) /\
      frameFramework.assignsMeaning .answer (frameTermFor .answer)
        (BuddhistComparativeLogic.kindOf .answer) /\
      frameFramework.raises .answer (.roleUnclear .answer) /\
      frameFramework.connects .question .answer := by
  exact ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

def longerRecensionCommentary :
    AlignedCommentary BuddhistComparativeLogic.LongerFrameUnit frameFramework :=
  ofLongerRecension frameFramework (fun passage _ => frameCertificate passage)

theorem longer_recension_has_structural_and_commentary_coverage :
    longerRecensionCommentary.alignment.SourceCovered /\
      longerRecensionCommentary.alignment.RequiredCovered /\
      (forall passage,
        passage ∈ longerRecensionCommentary.alignment.required ->
          CommentaryCertificate frameFramework passage) := by
  exact ⟨longerRecensionCommentary.structuralCoverage.1,
    longerRecensionCommentary.structuralCoverage.2,
    longerRecensionCommentary.certifiesRequired⟩

/-- A full framework whose designated word meaning is the existing certified
red-feature definiendum. -/
def redDefinitionFramework : CommentaryFramework Unit Unit
    (BuddhistComparativeLogic.Apoha.PredSet BuddhistComparativeLogic.ApohaFeatures.SampleObject)
    Unit Unit Unit where
  termOccurs := fun _ _ => True
  purposeFits := fun _ _ => True
  synopsisFits := fun _ _ => True
  assignsMeaning := fun _ _ meaning =>
    meaning = BuddhistComparativeLogic.TibetanDefinitions.redTriad.definiendum
  opens := fun _ => True
  connects := fun _ _ => True
  raises := fun _ _ => False
  replies := fun _ _ _ => False
  resolves := fun _ _ => False

def redDefinitionPadartha :
    DefinitionPadarthaAdapter BuddhistComparativeLogic.ApohaFeatures.SampleFeature
      redDefinitionFramework () () where
  standard := BuddhistComparativeLogic.TibetanDefinitions.redStandard
  triad := BuddhistComparativeLogic.TibetanDefinitions.redTriad
  certificate := BuddhistComparativeLogic.TibetanDefinitions.redCertificate
  occurs := trivial
  assignment := rfl

theorem certified_definition_supplies_inhabited_padartha :
    (exists meaning, redDefinitionFramework.assignsMeaning () () meaning) /\
      BuddhistComparativeLogic.TibetanDefinitions.redTriad.definiendum
        BuddhistComparativeLogic.TibetanDefinitions.redTriad.basis :=
  ⟨redDefinitionPadartha.suppliesMeaning,
    redDefinitionPadartha.classifiesBasis⟩

/-- The generic debate adapter is instantiated with the repository's finite
appearance-underdetermination certificate. -/
def registryReplyFramework : CommentaryFramework Unit Unit Unit Unit
    (Unit -> Prop) (Unit -> Prop) where
  termOccurs := fun _ _ => True
  purposeFits := fun _ _ => True
  synopsisFits := fun _ _ => True
  assignsMeaning := fun _ _ _ => True
  opens := fun _ => True
  connects := fun _ _ => True
  raises := fun _ _ => True
  replies := fun _ _ _ => True
  resolves := fun objection reply => reply () /\ ¬ objection ()

def appearanceDebateReply :
    DebateReplyAdapter registryReplyFramework () () where
  debate := BuddhistComparativeLogic.Tattvasamgraha.ofAppearanceUnderdetermination
  raised := trivial
  recorded := trivial
  resolution :=
    ⟨BuddhistComparativeLogic.Tattvasamgraha.ofAppearanceUnderdetermination.result_at_subject,
      BuddhistComparativeLogic.Tattvasamgraha.ofAppearanceUnderdetermination.rejects_opponent⟩

theorem tattvasamgraha_debate_supplies_codyaparihara :
    exists reply,
      registryReplyFramework.replies ()
        appearanceDebateReply.debate.opponentThesis reply /\
      registryReplyFramework.resolves
        appearanceDebateReply.debate.opponentThesis reply /\
      reply () /\
      ¬ appearanceDebateReply.debate.opponentThesis () :=
  appearanceDebateReply.suppliesResolvedReply

end BuddhistComparativeLogic.Vyakhyayukti
