/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Grammar.Bhartrhari

/-!
# Two Mīmāṃsā sentence-meaning architectures

This module gives a bounded typed comparison inspired by the classical
contrast between `abhihitanvaya` and `anvitabhidhana`.  In the first
architecture, words independently supply lexical meanings which are then
composed with argument roles.  In the second, a context supplies connected
word occurrences before a sentence result is synthesized.

The two computations agree only through an explicit decoding and composition
bridge.  No claim is made here that either architecture is historically
correct, that all authors formulate the contrast alike, or that either one is
identical to a modern theory of formal semantics.  The Bhartṛhari bridge below
shares only the repository's stage-indexed expression type; it does not
identify Bhartṛhari's views with either Mīmāṃsā architecture.

Source status (accessed 2026-09-19): Śālikanātha's
*Vākyārthamātṛkā* I is available in the TextGrid/GRETIL
*Prakaraṇapañcikā* e-text
<https://www.textgridrep.org/browse/49nsk.0>.  Saxena's Cambridge study,
translation/paraphrase, and treatment of Sucarita's Bhāṭṭa response are at
<https://doi.org/10.17863/CAM.37004>.  No source text or translation is
reproduced.  The two typed architectures, `CompositionBridge`, and the
agreement theorem are project-authored formal paraphrases.
-/

namespace BuddhistComparativeLogic.MimamsaSentenceMeaning

universe u v w x y z

/-! ## Two distinct typed routes to sentence meaning -/

/-- A word occurrence carries its syntactic or semantic role separately from
the public word token. -/
structure Occurrence (Word : Type u) (Role : Type v) where
  word : Word
  role : Role
  deriving Repr

/-- The `abhihitanvaya` architecture used in this audit: independently
expressed lexical meanings are paired with occurrence roles and composed. -/
structure Abhihitanvaya (Word : Type u) (LexicalMeaning : Type v)
    (Role : Type w) (SentenceMeaning : Type x) where
  expresses : Word -> LexicalMeaning
  compose : List (LexicalMeaning × Role) -> SentenceMeaning

namespace Abhihitanvaya

variable {Word : Type u} {LexicalMeaning : Type v}
  {Role : Type w} {SentenceMeaning : Type x}
  (analysis : Abhihitanvaya Word LexicalMeaning Role SentenceMeaning)

def encodedOccurrences (sentence : List (Occurrence Word Role)) :
    List (LexicalMeaning × Role) :=
  sentence.map fun occurrence =>
    (analysis.expresses occurrence.word, occurrence.role)

def interpret (sentence : List (Occurrence Word Role)) : SentenceMeaning :=
  analysis.compose (analysis.encodedOccurrences sentence)

end Abhihitanvaya

/-- The `anvitabhidhana` architecture used here: a context first turns each
word occurrence into a connected meaning, and those connected meanings are
then synthesized.  `ConnectedMeaning` need not equal a lexical meaning/role
pair. -/
structure Anvitabhidhana (Word : Type u) (Role : Type v)
    (Context : Type w) (ConnectedMeaning : Type x)
    (SentenceMeaning : Type y) where
  connect : Context -> Occurrence Word Role -> ConnectedMeaning
  synthesize : List ConnectedMeaning -> SentenceMeaning

namespace Anvitabhidhana

variable {Word : Type u} {Role : Type v} {Context : Type w}
  {ConnectedMeaning : Type x} {SentenceMeaning : Type y}
  (analysis :
    Anvitabhidhana Word Role Context ConnectedMeaning SentenceMeaning)

def connectedOccurrences (context : Context)
    (sentence : List (Occurrence Word Role)) : List ConnectedMeaning :=
  sentence.map (analysis.connect context)

def interpret (context : Context)
    (sentence : List (Occurrence Word Role)) : SentenceMeaning :=
  analysis.synthesize (analysis.connectedOccurrences context sentence)

end Anvitabhidhana

/-! ## The bridge required for agreement -/

/-- A coherence witness has two independent duties.  It must decode every
context-connected occurrence into the lexical meaning/role pair used by the
first architecture, and it must show that both composition operations agree
after decoding. -/
structure CompositionBridge
    {Word : Type u} {LexicalMeaning : Type v} {Role : Type w}
    {Context : Type x} {ConnectedMeaning : Type y}
    {SentenceMeaning : Type z}
    (abhihita :
      Abhihitanvaya Word LexicalMeaning Role SentenceMeaning)
    (anvita :
      Anvitabhidhana Word Role Context ConnectedMeaning SentenceMeaning) where
  decode : ConnectedMeaning -> LexicalMeaning × Role
  occurrenceCoherence : forall context occurrence,
    decode (anvita.connect context occurrence) =
      (abhihita.expresses occurrence.word, occurrence.role)
  compositionCoherence : forall connected,
    anvita.synthesize connected =
      abhihita.compose (connected.map decode)

namespace CompositionBridge

variable {Word : Type u} {LexicalMeaning : Type v} {Role : Type w}
  {Context : Type x} {ConnectedMeaning : Type y}
  {SentenceMeaning : Type z}
  {abhihita : Abhihitanvaya Word LexicalMeaning Role SentenceMeaning}
  {anvita :
    Anvitabhidhana Word Role Context ConnectedMeaning SentenceMeaning}

/-- Agreement is a theorem from the bridge, rather than a definitional
identification of the two architectures. -/
theorem interpretationsAgree (bridge : CompositionBridge abhihita anvita)
    (context : Context) (sentence : List (Occurrence Word Role)) :
    abhihita.interpret sentence = anvita.interpret context sentence := by
  have decoded :
      (anvita.connectedOccurrences context sentence).map bridge.decode =
        abhihita.encodedOccurrences sentence := by
    induction sentence with
    | nil => rfl
    | cons occurrence tail inductionHypothesis =>
        change bridge.decode (anvita.connect context occurrence) ::
            (anvita.connectedOccurrences context tail).map bridge.decode =
          (abhihita.expresses occurrence.word, occurrence.role) ::
            abhihita.encodedOccurrences tail
        rw [bridge.occurrenceCoherence, inductionHypothesis]
  calc
    abhihita.interpret sentence =
        abhihita.compose (abhihita.encodedOccurrences sentence) := rfl
    _ = abhihita.compose
        ((anvita.connectedOccurrences context sentence).map bridge.decode) :=
      congrArg abhihita.compose decoded.symm
    _ = anvita.synthesize
        (anvita.connectedOccurrences context sentence) :=
      (bridge.compositionCoherence
        (anvita.connectedOccurrences context sentence)).symm
    _ = anvita.interpret context sentence := rfl

end CompositionBridge

/-! ## A typed bridge to staged expression -/

/-- At one chosen vocabulary stage, every independently expressed lexical
meaning is witnessed by the existing Bhartṛhari-inspired staged-language
interface. -/
structure StagedLexicalBridge
    {Stage : Type u} {Word : Type v} {LexicalMeaning : Type w}
    {Role : Type x} {SentenceMeaning : Type y}
    (language :
      BuddhistComparativeLogic.Bhartrhari.StagedLanguage Stage Word LexicalMeaning)
    (analysis :
      Abhihitanvaya Word LexicalMeaning Role SentenceMeaning) where
  stage : Stage
  expressesLexicon : forall word,
    language.SuccessfullyExpresses stage word (analysis.expresses word)

namespace StagedLexicalBridge

variable {Stage : Type u} {Word : Type v} {LexicalMeaning : Type w}
  {Role : Type x} {SentenceMeaning : Type y}
  {language :
    BuddhistComparativeLogic.Bhartrhari.StagedLanguage Stage Word LexicalMeaning}
  {analysis : Abhihitanvaya Word LexicalMeaning Role SentenceMeaning}

theorem occurrenceMeaningIsSignifiable
    (bridge : StagedLexicalBridge language analysis)
    (occurrence : Occurrence Word Role) :
    language.SignifiableAt bridge.stage
      (analysis.expresses occurrence.word) :=
  language.successful_is_signifiable
    (bridge.expressesLexicon occurrence.word)

end StagedLexicalBridge

/-! ## A finite coherent model -/

inductive SampleWord where
  | alice
  | loves
  | bob
  deriving DecidableEq, Repr

inductive SampleLexicalMeaning where
  | alicePerson
  | lovingRelation
  | bobPerson
  deriving DecidableEq, Repr

inductive SampleRole where
  | subject
  | predicate
  | object
  deriving DecidableEq, Repr

inductive SampleSentenceMeaning where
  | aliceLovesBob
  | bobLovesAlice
  | malformed
  deriving DecidableEq, Repr

inductive SampleContext where
  | ordinary
  deriving DecidableEq, Repr

open SampleWord SampleLexicalMeaning SampleRole SampleSentenceMeaning

def sampleLexicon : SampleWord -> SampleLexicalMeaning
  | .alice => .alicePerson
  | .loves => .lovingRelation
  | .bob => .bobPerson

/-- This deliberately tiny composer recognizes two argument structures.  The
second and third successful patterns demonstrate that roles and order remain
inputs after lexical extensions have been fixed. -/
def composeSample :
    List (SampleLexicalMeaning × SampleRole) -> SampleSentenceMeaning
  | [(.alicePerson, .subject), (.lovingRelation, .predicate),
      (.bobPerson, .object)] => .aliceLovesBob
  | [(.alicePerson, .object), (.lovingRelation, .predicate),
      (.bobPerson, .subject)] => .bobLovesAlice
  | [(.bobPerson, .subject), (.lovingRelation, .predicate),
      (.alicePerson, .object)] => .bobLovesAlice
  | _ => .malformed

def sampleAbhihita :
    Abhihitanvaya SampleWord SampleLexicalMeaning SampleRole
      SampleSentenceMeaning where
  expresses := sampleLexicon
  compose := composeSample

abbrev SampleConnectedMeaning := SampleLexicalMeaning × SampleRole

def sampleAnvita :
    Anvitabhidhana SampleWord SampleRole SampleContext
      SampleConnectedMeaning SampleSentenceMeaning where
  connect := fun _context occurrence =>
    (sampleLexicon occurrence.word, occurrence.role)
  synthesize := composeSample

def sampleCompositionBridge :
    CompositionBridge sampleAbhihita sampleAnvita where
  decode := id
  occurrenceCoherence := by
    intro context occurrence
    cases context
    rfl
  compositionCoherence := by
    intro connected
    simp [sampleAnvita, sampleAbhihita]

def aliceLovesBobSentence : List (Occurrence SampleWord SampleRole) :=
  [⟨.alice, .subject⟩, ⟨.loves, .predicate⟩, ⟨.bob, .object⟩]

theorem coherent_positive_model :
    sampleAbhihita.interpret aliceLovesBobSentence =
        .aliceLovesBob /\
      sampleAnvita.interpret .ordinary aliceLovesBobSentence =
        .aliceLovesBob /\
      sampleAbhihita.interpret aliceLovesBobSentence =
        sampleAnvita.interpret .ordinary aliceLovesBobSentence := by
  exact ⟨rfl, rfl,
    sampleCompositionBridge.interpretationsAgree
      .ordinary aliceLovesBobSentence⟩

/-- Keeping the same connected occurrences while changing the synthesis rule
can make the two architectures disagree.  The generic agreement theorem then
rules out a coherence bridge for this particular pair. -/
def discordantAnvita :
    Anvitabhidhana SampleWord SampleRole SampleContext
      SampleConnectedMeaning SampleSentenceMeaning where
  connect := sampleAnvita.connect
  synthesize := fun connected =>
    match composeSample connected with
    | .aliceLovesBob => .bobLovesAlice
    | .bobLovesAlice => .aliceLovesBob
    | .malformed => .malformed

theorem without_composition_bridge_architectures_can_disagree :
    sampleAbhihita.interpret aliceLovesBobSentence = .aliceLovesBob /\
      discordantAnvita.interpret .ordinary aliceLovesBobSentence =
        .bobLovesAlice /\
      ¬ Nonempty (CompositionBridge sampleAbhihita discordantAnvita) := by
  refine ⟨rfl, rfl, ?_⟩
  rintro ⟨bridge⟩
  have agreement := bridge.interpretationsAgree
    .ordinary aliceLovesBobSentence
  exact SampleSentenceMeaning.noConfusion agreement

/-! ## The finite staged-language witness -/

inductive LexicalStage where
  | ordinary
  deriving DecidableEq, Repr

def sampleStagedLanguage :
    BuddhistComparativeLogic.Bhartrhari.StagedLanguage
      LexicalStage SampleWord SampleLexicalMeaning where
  available := fun _stage _word => true
  denotes := fun _stage word meaning => decide (meaning = sampleLexicon word)
  denotationAvailable := by
    intro stage word meaning _denotes
    rfl

def sampleStagedLexicalBridge :
    StagedLexicalBridge sampleStagedLanguage sampleAbhihita where
  stage := .ordinary
  expressesLexicon := by
    intro word
    constructor
    · rfl
    · simp [sampleStagedLanguage, sampleAbhihita]

theorem coherent_model_has_staged_lexical_witnesses :
    forall occurrence : Occurrence SampleWord SampleRole,
      sampleStagedLanguage.SignifiableAt
        sampleStagedLexicalBridge.stage
        (sampleAbhihita.expresses occurrence.word) := by
  intro occurrence
  exact sampleStagedLexicalBridge.occurrenceMeaningIsSignifiable occurrence

/-! ## Lexical extensions do not fix order or argument role -/

inductive SampleEntity where
  | alice
  | loving
  | bob
  deriving DecidableEq, Repr

/-- The extension of each lexical meaning is fixed independently of sentence
order and argument-role assignment. -/
def lexicalExtension : SampleLexicalMeaning -> SampleEntity -> Prop
  | .alicePerson, .alice => True
  | .lovingRelation, .loving => True
  | .bobPerson, .bob => True
  | _, _ => False

/-- The same words in the same order receive different argument roles. -/
def roleSwappedSentence : List (Occurrence SampleWord SampleRole) :=
  [⟨.alice, .object⟩, ⟨.loves, .predicate⟩, ⟨.bob, .subject⟩]

/-- The same three words are reordered together with their roles. -/
def reorderedSentence : List (Occurrence SampleWord SampleRole) :=
  [⟨.bob, .subject⟩, ⟨.loves, .predicate⟩, ⟨.alice, .object⟩]

/-- Forget roles but retain, in word order, the lexical extensions contributed
by a sentence. -/
def orderedLexicalExtensions
    (analysis :
      Abhihitanvaya SampleWord SampleLexicalMeaning SampleRole
        SampleSentenceMeaning)
    (sentence : List (Occurrence SampleWord SampleRole)) :
    List (SampleEntity -> Prop) :=
  sentence.map fun occurrence =>
    lexicalExtension (analysis.expresses occurrence.word)

theorem reordered_sentence_uses_same_lexical_inventory :
    List.Perm
      (orderedLexicalExtensions sampleAbhihita aliceLovesBobSentence)
      (orderedLexicalExtensions sampleAbhihita reorderedSentence) := by
  let aliceExtension := lexicalExtension .alicePerson
  let loveExtension := lexicalExtension .lovingRelation
  let bobExtension := lexicalExtension .bobPerson
  change List.Perm
    [aliceExtension, loveExtension, bobExtension]
    [bobExtension, loveExtension, aliceExtension]
  exact (List.Perm.swap aliceExtension loveExtension [bobExtension]).symm.trans
    ((List.Perm.cons loveExtension
      (List.Perm.swap aliceExtension bobExtension []).symm).trans
      (List.Perm.swap loveExtension bobExtension [aliceExtension]).symm)

/-- Role reassignment changes sentence meaning even though the ordered list
of words and their lexical extensions is exactly the same.  Reordering the
same lexical inventory supplies a second change of input with the same
resulting contrast. -/
theorem same_lexical_extensions_do_not_determine_sentence_meaning :
    orderedLexicalExtensions sampleAbhihita aliceLovesBobSentence =
        orderedLexicalExtensions sampleAbhihita roleSwappedSentence /\
      sampleAbhihita.interpret aliceLovesBobSentence = .aliceLovesBob /\
      sampleAbhihita.interpret roleSwappedSentence = .bobLovesAlice /\
      List.Perm
        (orderedLexicalExtensions sampleAbhihita aliceLovesBobSentence)
        (orderedLexicalExtensions sampleAbhihita reorderedSentence) /\
      sampleAbhihita.interpret reorderedSentence = .bobLovesAlice /\
      sampleAbhihita.interpret aliceLovesBobSentence ≠
        sampleAbhihita.interpret roleSwappedSentence /\
      sampleAbhihita.interpret aliceLovesBobSentence ≠
        sampleAbhihita.interpret reorderedSentence := by
  exact ⟨rfl, rfl, rfl, reordered_sentence_uses_same_lexical_inventory,
    rfl, by decide, by decide⟩

end BuddhistComparativeLogic.MimamsaSentenceMeaning
