/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Mimamsa.MimamsaEpistemology

/-!
# Qualified absence in a Navya-Nyaya-inspired audit

This module gives a bounded modern reconstruction inspired by Navya-Nyaya
analyses of absence.  A putative absence is indexed separately by a locus, a
counterpositive, a delimiter, and a relation.  The formal result is therefore
only a qualified absence at the supplied indices; it is not an unqualified
claim that an object does not exist.

Perceptibility, exhaustive search, and non-cognition are independent fields.
Their connection to absence is carried by an explicit detection law and an
`AbsenceCertificate`.  The reconstruction is not an exhaustive translation
of Navya-Nyaya terminology or of the historical debates about `abhava`.
The bridge to the repository's Mīmāṃsā non-cognition API records a common
proof shape without identifying the two traditions' accounts of knowledge.

Historical orientation and formal mapping (sources accessed 2026-09-19):

* Prabal Kumar Sen and Amita Chatterjee, "Navya-Nyaya Logic," *Journal of
  the Indian Council of Philosophical Research* 27.2 (2010), 77-99,
  especially 83-85, identifies a locus (`anuyogin`), a counterpositive or
  negatum (`pratiyogin`), delimiters (`avacchedaka`), and the relation that
  delimits counterpositiveness.  The full article is available from the
  University of Oxford at
  https://www.cs.ox.ac.uk/people/michael.wooldridge/pubs/icpr2011.pdf.
* Jonardon Ganeri, "Towards a Formal Regimentation of the Navya-Nyaya
  Technical Language I," in *Logic, Navya-Nyaya & Applications* (2008),
  109-124, especially 111-121, provides the locus, delimiter,
  counterpositive, relation, and negation vocabulary used for formal
  orientation:
  https://www.columbia.edu/itc/mealac/pollock/sks/papers/Ganeri%28Matilal%20vol%29.pdf.
* Jonardon Ganeri, "Analytic Philosophy in Early Modern India," *Stanford
  Encyclopedia of Philosophy*, sections 11.2-11.3, distinguishes locus,
  counterpositive, relation, and `pratiyogitavacchedaka`:
  https://plato.stanford.edu/entries/early-modern-india/.

Accordingly, the types `Locus`, `Counterpositive`, `Delimiter`, and
`Relation` are separately typed counterparts of those four kinds of
qualification.  `Model.relates` and `Model.delimits` are deliberately
simplified modern predicates; they do not reproduce the nested historical
technical language.  `QualifiedPresence` and its negation are the formalizer's
four-index audit, not a translated Navya-Nyaya four-place formula.  The
perceptibility, exhaustive-search, cognition, and detection fields are modern
certificate machinery and have no claimed textual counterpart.  English
labels follow the cited scholarship, with Sanskrit terms retained where they
disambiguate the mapping; no uncited Sanskrit passage is translated here.
-/

namespace BuddhistComparativeLogic.NavyaNyayaAbsence

universe u v w x

/-! ## A four-index model -/

/-- The types of loci, counterpositives, delimiters, and relations remain
distinct.  `relates` supplies relation-indexed presence, while `delimits`
records which counterpositive falls under a supplied delimiter. -/
structure Model (Locus : Type u) (Counterpositive : Type v)
    (Delimiter : Type w) (Relation : Type x) where
  relates : Relation -> Locus -> Counterpositive -> Prop
  delimits : Delimiter -> Counterpositive -> Prop
  perceptible : Relation -> Locus -> Counterpositive -> Delimiter -> Prop
  exhaustivelySearched :
    Relation -> Locus -> Counterpositive -> Delimiter -> Prop
  cognized : Relation -> Locus -> Counterpositive -> Delimiter -> Prop
  detection : forall {relation locus counterpositive delimiter},
    relates relation locus counterpositive ->
      delimits delimiter counterpositive ->
      perceptible relation locus counterpositive delimiter ->
      exhaustivelySearched relation locus counterpositive delimiter ->
      cognized relation locus counterpositive delimiter

namespace Model

variable {Locus : Type u} {Counterpositive : Type v}
  {Delimiter : Type w} {Relation : Type x}
  (model : Model Locus Counterpositive Delimiter Relation)

/-- Presence qualified by all four indices. -/
def QualifiedPresence (relation : Relation) (locus : Locus)
    (counterpositive : Counterpositive) (delimiter : Delimiter) : Prop :=
  model.relates relation locus counterpositive /\
    model.delimits delimiter counterpositive

/-- Absence is the negation of the correspondingly qualified presence. -/
def QualifiedAbsence (relation : Relation) (locus : Locus)
    (counterpositive : Counterpositive) (delimiter : Delimiter) : Prop :=
  ¬ model.QualifiedPresence relation locus counterpositive delimiter

/-- Counterpositives are extensionally indistinguishable in this model when
all relation/locus/delimiter profiles agree. -/
def CounterpositiveCoextensive
    (left right : Counterpositive) : Prop :=
  forall relation locus delimiter,
    model.QualifiedPresence relation locus left delimiter <->
      model.QualifiedPresence relation locus right delimiter

/-- Delimiters are extensionally indistinguishable when they qualify the same
relation/locus/counterpositive profiles. -/
def DelimiterCoextensive (left right : Delimiter) : Prop :=
  forall relation locus counterpositive,
    model.QualifiedPresence relation locus counterpositive left <->
      model.QualifiedPresence relation locus counterpositive right

/-- Relations are extensionally indistinguishable when their qualified
presence profiles agree. -/
def RelationCoextensive (left right : Relation) : Prop :=
  forall locus counterpositive delimiter,
    model.QualifiedPresence left locus counterpositive delimiter <->
      model.QualifiedPresence right locus counterpositive delimiter

/-- Package perceptibility and completed search as the perceptibility field
of the repository's shared non-cognition interface.  This conjunction keeps
both obligations visible rather than treating bare non-cognition as proof of
absence. -/
def asNonCognitionModel (relation : Relation) (delimiter : Delimiter) :
    BuddhistComparativeLogic.MimamsaEpistemology.NonCognitionModel
      (Locus × Counterpositive) where
  present := fun target =>
    model.QualifiedPresence relation target.1 target.2 delimiter
  perceived := fun target =>
    model.cognized relation target.1 target.2 delimiter
  perceptible := fun target =>
    model.perceptible relation target.1 target.2 delimiter /\
      model.exhaustivelySearched relation target.1 target.2 delimiter
  visibility := by
    rintro ⟨locus, counterpositive⟩ presence ⟨perceptible, searched⟩
    exact model.detection presence.1 presence.2 perceptible searched

end Model

/-! ## The explicit absence certificate -/

/-- Evidence for one exactly indexed absence claim.  The three evidential
fields are independent of the target presence predicate. -/
structure AbsenceCertificate
    {Locus : Type u} {Counterpositive : Type v}
    {Delimiter : Type w} {Relation : Type x}
    (model : Model Locus Counterpositive Delimiter Relation)
    (relation : Relation) (locus : Locus)
    (counterpositive : Counterpositive) (delimiter : Delimiter) : Prop where
  perceptible : model.perceptible relation locus counterpositive delimiter
  exhaustiveSearch :
    model.exhaustivelySearched relation locus counterpositive delimiter
  noncognition : ¬ model.cognized relation locus counterpositive delimiter

namespace AbsenceCertificate

variable {Locus : Type u} {Counterpositive : Type v}
  {Delimiter : Type w} {Relation : Type x}
  {model : Model Locus Counterpositive Delimiter Relation}
  {relation : Relation} {locus : Locus}
  {counterpositive : Counterpositive} {delimiter : Delimiter}

/-- Detection plus the three certificate fields derives only the qualified
absence named by the certificate. -/
theorem sound
    (certificate : AbsenceCertificate model relation locus
      counterpositive delimiter) :
    model.QualifiedAbsence relation locus counterpositive delimiter := by
  intro presence
  exact certificate.noncognition
    (model.detection presence.1 presence.2 certificate.perceptible
      certificate.exhaustiveSearch)

/-- The same proof can be checked through the existing Mīmāṃsā-facing
non-cognition API after the four indices have been fixed explicitly. -/
theorem throughMimamsaNonCognition
    (certificate : AbsenceCertificate model relation locus
      counterpositive delimiter) :
    ¬ (model.asNonCognitionModel relation delimiter).present
      (locus, counterpositive) :=
  BuddhistComparativeLogic.MimamsaEpistemology.visible_noncognition_sound
    (model.asNonCognitionModel relation delimiter)
    ⟨certificate.perceptible, certificate.exhaustiveSearch⟩
    certificate.noncognition

end AbsenceCertificate

/-! ## An inhabited finite certificate -/

inductive Room where
  | hall
  | store
  deriving DecidableEq, Repr

inductive Item where
  | pot
  | cloth
  deriving DecidableEq, Repr

inductive Qualification where
  | visible
  | red
  deriving DecidableEq, Repr

inductive Connection where
  | contact
  | inherence
  deriving DecidableEq, Repr

open Room Item Qualification Connection

/-- The cloth is visibly in contact with the hall; the red pot is related to
the store only by inherence.  Every indexed query can in principle be
perceived and exhaustively searched in this finite model. -/
def storeroomModel : Model Room Item Qualification Connection where
  relates
    | .contact, .hall, .cloth => True
    | .inherence, .store, .pot => True
    | _, _, _ => False
  delimits
    | .visible, .cloth => True
    | .red, .pot => True
    | _, _ => False
  perceptible := fun _ _ _ _ => True
  exhaustivelySearched := fun _ _ _ _ => True
  cognized := fun relation locus counterpositive delimiter =>
    (match relation, locus, counterpositive with
      | .contact, .hall, .cloth => True
      | .inherence, .store, .pot => True
      | _, _, _ => False) /\
    (match delimiter, counterpositive with
      | .visible, .cloth => True
      | .red, .pot => True
      | _, _ => False)
  detection := by
    intro relation locus counterpositive delimiter related delimited
      _perceptible _searched
    exact ⟨related, delimited⟩

theorem noVisiblePotInStore :
    AbsenceCertificate storeroomModel .contact .store .pot .visible where
  perceptible := trivial
  exhaustiveSearch := trivial
  noncognition := by
    simp [storeroomModel]

theorem finite_certificate_is_nonvacuous :
    storeroomModel.QualifiedPresence .contact .hall .cloth .visible /\
      storeroomModel.cognized .contact .hall .cloth .visible /\
      storeroomModel.QualifiedAbsence .contact .store .pot .visible /\
      ¬ (storeroomModel.asNonCognitionModel .contact .visible).present
        (.store, .pot) := by
  exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
    noVisiblePotInStore.sound,
    noVisiblePotInStore.throughMimamsaNonCognition⟩

/-! ## Non-cognition alone is insufficient -/

inductive HiddenLocus where
  | chamber
  deriving DecidableEq, Repr

inductive HiddenItem where
  | jewel
  deriving DecidableEq, Repr

inductive HiddenDelimiter where
  | valuable
  deriving DecidableEq, Repr

inductive HiddenRelation where
  | enclosure
  deriving DecidableEq, Repr

/-- The jewel is present but is neither perceptible nor searched.  Its
non-cognition is consequently compatible with presence. -/
def hiddenJewelModel :
    Model HiddenLocus HiddenItem HiddenDelimiter HiddenRelation where
  relates := fun _ _ _ => True
  delimits := fun _ _ => True
  perceptible := fun _ _ _ _ => False
  exhaustivelySearched := fun _ _ _ _ => False
  cognized := fun _ _ _ _ => False
  detection := by
    intro _relation _locus _counterpositive _delimiter _related _delimited
      perceptible _searched
    exact False.elim perceptible

theorem noncognition_alone_does_not_entail_qualified_absence :
    hiddenJewelModel.QualifiedPresence .enclosure .chamber .jewel .valuable /\
      ¬ hiddenJewelModel.cognized .enclosure .chamber .jewel .valuable /\
      ¬ hiddenJewelModel.perceptible .enclosure .chamber .jewel .valuable /\
      ¬ (¬ hiddenJewelModel.cognized
          .enclosure .chamber .jewel .valuable ->
        hiddenJewelModel.QualifiedAbsence
          .enclosure .chamber .jewel .valuable) := by
  refine ⟨⟨trivial, trivial⟩, by simp [hiddenJewelModel],
    by simp [hiddenJewelModel], ?_⟩
  intro implication
  exact implication (by simp [hiddenJewelModel]) ⟨trivial, trivial⟩

/-! ## Coextension is weaker than identity of an index -/

inductive TwinLocus where
  | site
  deriving DecidableEq, Repr

inductive TwinCounterpositive where
  | first
  | second
  deriving DecidableEq, Repr

inductive TwinDelimiter where
  | first
  | second
  deriving DecidableEq, Repr

inductive TwinRelation where
  | first
  | second
  deriving DecidableEq, Repr

/-- Every qualified profile is inhabited, but each index type still contains
two different constructors. -/
def twinModel :
    Model TwinLocus TwinCounterpositive TwinDelimiter TwinRelation where
  relates := fun _ _ _ => True
  delimits := fun _ _ => True
  perceptible := fun _ _ _ _ => True
  exhaustivelySearched := fun _ _ _ _ => True
  cognized := fun _ _ _ _ => True
  detection := by
    intro _relation _locus _counterpositive _delimiter _related _delimited
      _perceptible _searched
    trivial

theorem coextension_does_not_identify_indices :
    twinModel.CounterpositiveCoextensive
        .first .second /\
      (TwinCounterpositive.first : TwinCounterpositive) ≠ .second /\
      twinModel.DelimiterCoextensive .first .second /\
      (TwinDelimiter.first : TwinDelimiter) ≠ .second /\
      twinModel.RelationCoextensive .first .second /\
      (TwinRelation.first : TwinRelation) ≠ .second := by
  refine ⟨?_, by decide, ?_, by decide, ?_, by decide⟩
  · intro relation locus delimiter
    simp [Model.QualifiedPresence, twinModel]
  · intro relation locus counterpositive
    simp [Model.QualifiedPresence, twinModel]
  · intro locus counterpositive delimiter
    simp [Model.QualifiedPresence, twinModel]

end BuddhistComparativeLogic.NavyaNyayaAbsence
