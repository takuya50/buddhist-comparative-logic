/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Ineffable
import BuddhistComparativeLogic.Core.UniversalDesignation
import BuddhistComparativeLogic.Core.MVLogic

/-!
# Staged signification and avacya

This module gives a small formal reconstruction inspired by Bhartṛhari's
discussion of expressions for what is called inexpressible (`avācya`).  A
vocabulary is indexed by a stage, so failure of every expression in a base
vocabulary remains distinct from failure at every possible stage.  A later
extended vocabulary can therefore denote the target without contradiction.

The reconstruction is deliberately limited.  It does not identify
Bhartṛhari's language philosophy with a modern hierarchy of formal
languages, and it does not settle the interpretation of *Vākyapadīya*
3.3.26.  Utterance tokens, their times, and their vocabulary stages are kept
separate below solely to expose the premise that blocks naive simultaneous
self-reference.

Historical orientation:

* *Vākyapadīya* 3.3.26 and surrounding discussion:
  https://www.wisdomlib.org/hinduism/book/vakyapadiya-of-bhartrihari/d/doc1336996.html
* Stanford Encyclopedia of Philosophy, "The Literal-Nonliteral Distinction
  in Classical Indian Philosophy":
  https://plato.stanford.edu/entries/literal-nonliteral-india/
* GRETIL Sanskrit corpus catalogue:
  https://gretil.sub.uni-goettingen.de/gretil.html
-/

namespace BuddhistComparativeLogic.Bhartrhari

universe u v w

/-! ## Stage-indexed vocabularies -/

/-- `available` and `denotes` are Boolean so finite instances can be
executed.  A denoting token must belong to the vocabulary at that stage. -/
structure StagedLanguage (Stage : Type u) (Token : Type v)
    (Referent : Type w) where
  available : Stage -> Token -> Bool
  denotes : Stage -> Token -> Referent -> Bool
  denotationAvailable : forall {stage token referent},
    denotes stage token referent = true -> available stage token = true

namespace StagedLanguage

variable {Stage : Type u} {Token : Type v} {Referent : Type w}
    (language : StagedLanguage Stage Token Referent)

def SuccessfullyExpresses (stage : Stage) (token : Token)
    (referent : Referent) : Prop :=
  language.available stage token = true /\
    language.denotes stage token referent = true

/-- A predicate set of successful designators, reusing the carrier used by
the repository's universal-designation semantics. -/
def designatorsAt (stage : Stage) (referent : Referent) : PSet Token :=
  fun token => language.SuccessfullyExpresses stage token referent

def SignifiableAt (stage : Stage) (referent : Referent) : Prop :=
  ∃ token, language.SuccessfullyExpresses stage token referent

def UnsignifiableAt (stage : Stage) (referent : Referent) : Prop :=
  ¬ language.SignifiableAt stage referent

def AbsolutelyUnsignifiable (referent : Referent) : Prop :=
  forall stage, language.UnsignifiableAt stage referent

theorem signifiable_iff_designators_nonempty (stage : Stage)
    (referent : Referent) :
    language.SignifiableAt stage referent <->
      pnonempty (language.designatorsAt stage referent) := by
  rfl

theorem successful_is_signifiable {stage : Stage} {token : Token}
    {referent : Referent}
    (success : language.SuccessfullyExpresses stage token referent) :
    language.SignifiableAt stage referent :=
  ⟨token, success⟩

/-- Absolute unsignifiability is incompatible with one successful expression.
The contradiction uses the stage and token of that expression explicitly. -/
theorem absolute_unsignifiability_excludes_success
    {stage : Stage} {token : Token} {referent : Referent}
    (absolute : language.AbsolutelyUnsignifiable referent)
    (success : language.SuccessfullyExpresses stage token referent) : False :=
  absolute stage ⟨token, success⟩

theorem not_absolute_of_success
    {stage : Stage} {token : Token} {referent : Referent}
    (success : language.SuccessfullyExpresses stage token referent) :
    ¬ language.AbsolutelyUnsignifiable referent :=
  fun absolute =>
    language.absolute_unsignifiability_excludes_success absolute success

/-- A later stage preserves every available base token and every base
denotation.  It may add tokens and denotations. -/
def StageExtends (base extended : Stage) : Prop :=
  (forall token, language.available base token = true ->
      language.available extended token = true) /\
    (forall token referent, language.denotes base token referent = true ->
      language.denotes extended token referent = true)

end StagedLanguage

/-! ## A complete finite vocabulary and executable search -/

structure FiniteVocabulary (Stage : Type u) (Token : Type v)
    (Referent : Type w) extends StagedLanguage Stage Token Referent where
  tokens : List Token
  tokensComplete : forall token, token ∈ tokens
  tokensNodup : tokens.Nodup

namespace FiniteVocabulary

variable {Stage : Type u} {Token : Type v} {Referent : Type w}
    (vocabulary : FiniteVocabulary Stage Token Referent)

private def scan (tokens : List Token) (stage : Stage)
    (referent : Referent) : Option Token :=
  match tokens with
  | [] => none
  | token :: rest =>
      if vocabulary.toStagedLanguage.available stage token &&
          vocabulary.toStagedLanguage.denotes stage token referent then
        some token
      else scan rest stage referent

/-- The first successful designator in the complete token enumeration. -/
def firstSignifier (stage : Stage) (referent : Referent) : Option Token :=
  scan vocabulary vocabulary.tokens stage referent

private theorem scan_some_sound {tokens : List Token} {stage : Stage}
    {referent : Referent} {token : Token}
    (found : scan vocabulary tokens stage referent = some token) :
    vocabulary.toStagedLanguage.SuccessfullyExpresses
        stage token referent /\ token ∈ tokens := by
  induction tokens with
  | nil => simp [scan] at found
  | cons head tail ih =>
      cases available :
          vocabulary.toStagedLanguage.available stage head with
      | false =>
          have tailFound : scan vocabulary tail stage referent = some token := by
            simpa [scan, available] using found
          have sound := ih tailFound
          exact ⟨sound.1, by simp [sound.2]⟩
      | true =>
          cases denotes :
              vocabulary.toStagedLanguage.denotes stage head referent with
          | false =>
              have tailFound :
                  scan vocabulary tail stage referent = some token := by
                simpa [scan, available, denotes] using found
              have sound := ih tailFound
              exact ⟨sound.1, by simp [sound.2]⟩
          | true =>
              have same : head = token := by
                simpa [scan, available, denotes] using found
              subst token
              exact ⟨⟨available, denotes⟩, by simp⟩

private theorem scan_none_iff (tokens : List Token) (stage : Stage)
    (referent : Referent) :
    scan vocabulary tokens stage referent = none <->
      ∀ token ∈ tokens,
        ¬ vocabulary.toStagedLanguage.SuccessfullyExpresses
          stage token referent := by
  induction tokens with
  | nil => simp [scan]
  | cons head tail ih =>
      cases available : vocabulary.toStagedLanguage.available stage head <;>
        cases denotes : vocabulary.toStagedLanguage.denotes stage head referent <;>
          simp [scan, available, denotes, ih,
            StagedLanguage.SuccessfullyExpresses]

theorem firstSignifier_some_sound {stage : Stage} {referent : Referent}
    {token : Token}
    (found : vocabulary.firstSignifier stage referent = some token) :
    vocabulary.toStagedLanguage.SuccessfullyExpresses stage token referent :=
  (scan_some_sound vocabulary found).1

/-- Completeness of executable failure uses the vocabulary's explicit proof
that every token occurs in its finite enumeration. -/
theorem firstSignifier_none_iff_unsignifiable
    (stage : Stage) (referent : Referent) :
    vocabulary.firstSignifier stage referent = none <->
      vocabulary.toStagedLanguage.UnsignifiableAt stage referent := by
  rw [firstSignifier, scan_none_iff]
  constructor
  · intro misses
    rintro ⟨token, success⟩
    exact misses token (vocabulary.tokensComplete token) success
  · intro unsignifiable token _membership success
    exact unsignifiable ⟨token, success⟩

end FiniteVocabulary

/-! ## Finite nonvacuous model -/

inductive SampleStage where
  | base
  | extended
  deriving DecidableEq, Repr

inductive SampleToken where
  | ordinaryName
  | avacyaName
  | quotePrior
  deriving DecidableEq, Repr

inductive Entity where
  | pot
  | target
  deriving DecidableEq, Repr

inductive UtteranceId where
  | first
  | second
  deriving DecidableEq, Repr

inductive Referent where
  | entity (value : Entity)
  | utterance (id : UtteranceId)
  deriving DecidableEq, Repr

open SampleStage SampleToken Entity UtteranceId Referent

/-- The base vocabulary names only the pot.  The extended vocabulary
preserves that denotation, adds `avacyaName` for the target, and lets
`quotePrior` refer to the first utterance.  The stage relation alone does not
assert a formal object-language/metalanguage typing discipline. -/
def sampleLanguage :
    StagedLanguage SampleStage SampleToken Referent where
  available
    | .base, .ordinaryName => true
    | .base, _ => false
    | .extended, _ => true
  denotes
    | .base, .ordinaryName, .entity .pot => true
    | .extended, .ordinaryName, .entity .pot => true
    | .extended, .avacyaName, .entity .target => true
    | .extended, .quotePrior, .utterance .first => true
    | _, _, _ => false
  denotationAvailable := by
    intro stage token referent denotation
    cases stage <;> cases token <;> cases referent
    all_goals rename_i payload
    all_goals cases payload <;> simp_all

def sampleVocabulary :
    FiniteVocabulary SampleStage SampleToken Referent where
  toStagedLanguage := sampleLanguage
  tokens := [.ordinaryName, .avacyaName, .quotePrior]
  tokensComplete := by intro token; cases token <;> simp
  tokensNodup := by decide

/-- Both outcomes are computed over an inhabited, explicitly complete
three-token vocabulary. -/
theorem finite_search_finds_exact_stage_boundary :
    sampleVocabulary.firstSignifier .base (.entity .target) = none /\
      sampleVocabulary.firstSignifier .extended (.entity .target) =
        some .avacyaName := by
  exact ⟨rfl, rfl⟩

theorem base_extends_to_later_stage :
    sampleLanguage.StageExtends .base .extended := by
  constructor
  · intro token available
    cases token <;> simp_all [sampleLanguage]
  · intro token referent denotation
    cases token <;> cases referent
    all_goals rename_i payload
    all_goals cases payload <;> simp_all [sampleLanguage]

theorem target_unsignifiable_in_base :
    sampleLanguage.UnsignifiableAt .base (.entity .target) := by
  rintro ⟨token, available, denotes⟩
  cases token <;> simp_all [sampleLanguage]

theorem target_signifiable_in_extension :
    sampleLanguage.SignifiableAt .extended (.entity .target) := by
  exact ⟨.avacyaName, ⟨rfl, rfl⟩⟩

/-- Base-vocabulary unsignifiability and later successful denotation are
jointly inhabited.  Hence the base-relative claim is weaker than the
absolute claim. -/
theorem base_unsignifiability_compatible_with_later_denotation :
    sampleLanguage.StageExtends .base .extended /\
      sampleLanguage.UnsignifiableAt .base (.entity .target) /\
      sampleLanguage.SuccessfullyExpresses
        .extended .avacyaName (.entity .target) /\
      ¬ sampleLanguage.AbsolutelyUnsignifiable (.entity .target) := by
  refine ⟨base_extends_to_later_stage, target_unsignifiable_in_base,
    ⟨rfl, rfl⟩, ?_⟩
  apply sampleLanguage.not_absolute_of_success
    (stage := .extended) (token := .avacyaName)
  exact ⟨rfl, rfl⟩

/-! ## A small bridge to the existing absorbing ineffable value -/

/-- This status records failure to find a designator as `ineff`; it does not
assign an FDE truth value to the historical notion of `avācya`. -/
noncomputable def expressionStatus
    (language : StagedLanguage Stage Token Referent)
    (stage : Stage) (referent : Referent) : WithIneff Bool := by
  classical
  exact if language.SignifiableAt stage referent then .val true else .ineff

theorem base_and_extension_have_distinct_expression_status :
    expressionStatus sampleLanguage .base (.entity .target) = .ineff /\
      expressionStatus sampleLanguage .extended (.entity .target) =
        .val true := by
  classical
  constructor
  · have absent :
        ¬ sampleLanguage.SignifiableAt .base (.entity .target) :=
      target_unsignifiable_in_base
    simp [expressionStatus, absent]
  · simp [expressionStatus, target_signifiable_in_extension]

/-! ## Utterance token, time, and stage -/

structure Utterance (Stage : Type u) (Token : Type v) where
  stage : Stage
  token : Token
  time : Nat
  deriving DecidableEq, Repr

/-- A discourse supplies one token occurrence for each utterance identifier.
The temporal discipline applies only to utterance-reference denotations; it
does not constrain denotation of ordinary entities. -/
structure Discourse (Stage : Type u) (Token : Type v)
    (Entity : Type w) (Id : Type) where
  language : StagedLanguage Stage Token (Sum Entity Id)
  utterance : Id -> Utterance Stage Token
  referenceEarlier : forall {source target},
    language.denotes (utterance source).stage (utterance source).token
        (.inr target) = true ->
      (utterance target).time < (utterance source).time

namespace Discourse

variable {Stage : Type u} {Token : Type v} {Entity : Type w} {Id : Type}
    (discourse : Discourse Stage Token Entity Id)

def RefersTo (source target : Id) : Prop :=
  discourse.language.denotes
    (discourse.utterance source).stage
    (discourse.utterance source).token (.inr target) = true

def SelfRefers (id : Id) : Prop := discourse.RefersTo id id

/-- A temporally disciplined discourse has no simultaneous self-reference.
This is the precise formal safeguard; no claim is made that all natural
language reference must obey it. -/
theorem no_self_reference (id : Id) : ¬ discourse.SelfRefers id := by
  intro selfReference
  have earlier := discourse.referenceEarlier selfReference
  exact (Nat.lt_irrefl (discourse.utterance id).time) earlier

theorem reference_has_available_source {source target : Id}
    (reference : discourse.RefersTo source target) :
    discourse.language.available
      (discourse.utterance source).stage
      (discourse.utterance source).token = true :=
  discourse.language.denotationAvailable reference

end Discourse

/-- The sum-valued version of the sample language used by `Discourse`. -/
def discourseLanguage :
    StagedLanguage SampleStage SampleToken (Sum Entity UtteranceId) where
  available := sampleLanguage.available
  denotes
    | .base, .ordinaryName, .inl .pot => true
    | .extended, .ordinaryName, .inl .pot => true
    | .extended, .avacyaName, .inl .target => true
    | .extended, .quotePrior, .inr .first => true
    | _, _, _ => false
  denotationAvailable := by
    intro stage token referent denotation
    cases stage <;> cases token <;> cases referent <;>
      simp_all [sampleLanguage]
    all_goals cases val <;> simp_all [sampleLanguage]

def sampleUtterance : UtteranceId -> Utterance SampleStage SampleToken
  | .first => ⟨.base, .ordinaryName, 0⟩
  | .second => ⟨.extended, .quotePrior, 1⟩

def finiteDiscourse :
    Discourse SampleStage SampleToken Entity UtteranceId where
  language := discourseLanguage
  utterance := sampleUtterance
  referenceEarlier := by
    intro source target reference
    cases source <;> cases target <;>
      simp_all [discourseLanguage, sampleUtterance]

/-- The later utterance refers to the earlier one, both source tokens are
available, and neither token occurrence refers to itself. -/
theorem finite_discourse_is_nonvacuous_and_nonselfreferential :
    finiteDiscourse.RefersTo .second .first /\
      finiteDiscourse.language.available
        (finiteDiscourse.utterance .second).stage
        (finiteDiscourse.utterance .second).token = true /\
      ¬ finiteDiscourse.SelfRefers .first /\
      ¬ finiteDiscourse.SelfRefers .second /\
      (finiteDiscourse.utterance .first).time <
        (finiteDiscourse.utterance .second).time := by
  refine ⟨rfl, ?_, finiteDiscourse.no_self_reference .first,
    finiteDiscourse.no_self_reference .second, by decide⟩
  exact finiteDiscourse.reference_has_available_source
    (source := .second) (target := .first) rfl

/-! ## A modern matrix comparison, not a historical identification -/

/-- The fixed-point equation generated by a naive self-negating semantic
clause. -/
def NegationFixedPoint (negation : Value -> Value) (value : Value) : Prop :=
  negation value = value

/-- Classical Boolean negation offers no value satisfying the equation. -/
theorem bivalent_negation_has_no_fixed_point :
    forall value : Bool, ¬ NegationFixedPoint Bool.not value := by
  intro value
  cases value <;> simp [NegationFixedPoint]

/-- In FDE both the glut and the gap are fixed by negation.  The second
conjunct matters: the existence of an FDE fixed point alone does not select a
dialetheic reading.  This is a comparison of matrices only and attributes no
FDE semantics to Bhartṛhari. -/
theorem fde_negation_has_glut_and_gap_fixed_points :
    NegationFixedPoint neg4 TV4.B /\
      NegationFixedPoint neg4 TV4.N /\ TV4.B ≠ TV4.N := by
  exact ⟨rfl, rfl, by decide⟩

end BuddhistComparativeLogic.Bhartrhari
