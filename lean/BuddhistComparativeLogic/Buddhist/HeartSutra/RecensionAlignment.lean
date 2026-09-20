/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.Longer

/-!
# Edition-parametric recension alignment

This module separates structural alignment from philological identity.  An
`Alignment` can certify that source-unit identifiers cover target units,
behave as a function, and preserve order without asserting any source string,
translation, token count, or preferred reading.  Lexical evidence is a
separate, explicitly partial layer: absent Sanskrit or Tibetan witnesses
produce proof obligations rather than axioms.

The concrete lexical data below was checked against two scholarly source
texts (punctuation is omitted when tokenizing):

* GRETIL, `Prajñāpāramitā-hṛdaya-sūtra`, Unicode reference text, lines 61--65:
  https://gretil.sub.uni-goettingen.de/gretil/1_sanskr/4_rellit/buddh/prajnhsu.htm
* Jonathan A. Silk, *The Heart Sūtra in Tibetan: A Critical Edition of the
  Two Recensions Contained in the Kanjur*, WSTB 34 (1994), Recension B,
  Appendix p. 177 (PDF p. 190):
  https://wstb.univie.ac.at/wp-content/uploads/WSTB_34.pdf

The Tibetan strings use punctuation-free Wylie tokens and normalize the
typographic apostrophe in `pa’o` to ASCII `pa'o`.  The validators below check
only surface occurrences of the form and emptiness expressions.  They do not
choose among identity, predication, non-separation, or other construals.
-/

namespace BuddhistComparativeLogic

/-! ## Generic ordered editions and alignments -/

/-- A finite edition inventory.  The list order is the order declared for a
particular comparison; `rank` makes that claim independently checkable.
Concrete diplomatic source order is recorded separately when it differs from
the canonical target-key order. -/
structure OrderedEdition (Unit : Type) where
  units : List Unit
  rank : Unit → Nat

namespace OrderedEdition

variable {Unit : Type}

/-- Boolean pairwise checking over every earlier/later list pair. -/
def pairwiseAll {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (p x) && pairwiseAll p xs

theorem pairwiseAll_eq_true_iff {α : Type} (p : α → α → Bool)
    (xs : List α) :
    pairwiseAll p xs = true ↔ xs.Pairwise fun x y => p x y = true := by
  induction xs with
  | nil => simp [pairwiseAll]
  | cons x xs ih =>
      simp [pairwiseAll, ih, List.all_eq_true]

/-- Unit identifiers are unique and strictly increase in the listed order. -/
def wellFormed [DecidableEq Unit] (E : OrderedEdition Unit) : Bool :=
  decide E.units.Nodup &&
    pairwiseAll (fun x y => decide (E.rank x < E.rank y)) E.units

def WellFormed [DecidableEq Unit] (E : OrderedEdition Unit) : Prop :=
  E.wellFormed = true

end OrderedEdition

/-- A partial map from the units of one edition into an ordered target.
`required` lists the target units for which reverse coverage is claimed. -/
structure Alignment (Source Target : Type) where
  source : OrderedEdition Source
  target : OrderedEdition Target
  mapsTo : Source → Option Target
  required : List Target

namespace Alignment

variable {Source Target : Type}

def Relates (A : Alignment Source Target) (s : Source) (t : Target) : Prop :=
  A.mapsTo s = some t

/-- Every enumerated source unit has a target. -/
def sourceCovered (A : Alignment Source Target) : Bool :=
  A.source.units.all fun s => (A.mapsTo s).isSome

def SourceCovered (A : Alignment Source Target) : Prop :=
  A.sourceCovered = true

/-- Every mapped target occurs in the target edition inventory. -/
def mappedIntoTarget [DecidableEq Target] (A : Alignment Source Target) : Bool :=
  A.source.units.all (fun s =>
    match A.mapsTo s with
    | none => false
    | some t => decide (t ∈ A.target.units))

def MappedIntoTarget [DecidableEq Target] (A : Alignment Source Target) : Prop :=
  A.mappedIntoTarget = true

/-- Every required target is hit by an enumerated source unit. -/
def requiredCovered [DecidableEq Target] (A : Alignment Source Target) : Bool :=
  A.required.all (fun t =>
    A.source.units.any fun s => decide (A.mapsTo s = some t))

def RequiredCovered [DecidableEq Target] (A : Alignment Source Target) : Prop :=
  A.requiredCovered = true

/-- The required targets are themselves distinct members of the target
inventory. -/
def requirementsWellFormed [DecidableEq Target]
    (A : Alignment Source Target) : Bool :=
  decide A.required.Nodup &&
    A.required.all fun t => decide (t ∈ A.target.units)

def RequirementsWellFormed [DecidableEq Target]
    (A : Alignment Source Target) : Prop :=
  A.requirementsWellFormed = true

/-- Earlier enumerated source units map to lower-ranked target units. -/
def orderPreserving (A : Alignment Source Target) : Bool :=
  OrderedEdition.pairwiseAll (fun x y =>
    match A.mapsTo x, A.mapsTo y with
    | some tx, some ty => decide (A.target.rank tx < A.target.rank ty)
    | _, _ => false) A.source.units

def OrderPreserving (A : Alignment Source Target) : Prop :=
  A.orderPreserving = true

/-- Executable validation of the bounded structural obligations. -/
def validate [DecidableEq Source] [DecidableEq Target]
    (A : Alignment Source Target) : Bool :=
  A.source.wellFormed &&
  A.target.wellFormed &&
  A.sourceCovered &&
  A.mappedIntoTarget &&
  A.requirementsWellFormed &&
  A.requiredCovered &&
  A.orderPreserving

/-- Complete structural validity.  This proposition mentions no lexical
content and therefore cannot silently identify the source texts. -/
def Valid [DecidableEq Source] [DecidableEq Target]
    (A : Alignment Source Target) : Prop :=
  A.validate = true

theorem validate_eq_true_iff [DecidableEq Source] [DecidableEq Target]
    (A : Alignment Source Target) :
    A.validate = true ↔ A.Valid := by
  rfl

theorem valid_iff_components [DecidableEq Source] [DecidableEq Target]
    (A : Alignment Source Target) :
    A.Valid ↔
      A.source.WellFormed ∧ A.target.WellFormed ∧ A.SourceCovered ∧
      A.MappedIntoTarget ∧ A.RequirementsWellFormed ∧ A.RequiredCovered ∧
      A.OrderPreserving := by
  simp only [Valid, validate, OrderedEdition.WellFormed, SourceCovered,
    MappedIntoTarget, RequirementsWellFormed, RequiredCovered,
    OrderPreserving, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hs, ht⟩, hc⟩, hm⟩, hw⟩, hr⟩, ho⟩
    exact ⟨hs, ht, hc, hm, hw, hr, ho⟩
  · rintro ⟨hs, ht, hc, hm, hw, hr, ho⟩
    exact ⟨⟨⟨⟨⟨⟨hs, ht⟩, hc⟩, hm⟩, hw⟩, hr⟩, ho⟩

theorem coverage_of_valid [DecidableEq Source] [DecidableEq Target]
    (A : Alignment Source Target) (h : A.Valid) :
    A.SourceCovered ∧ A.RequiredCovered := by
  rcases (A.valid_iff_components.mp h) with
    ⟨_, _, hSource, _, _, hRequired, _⟩
  exact ⟨hSource, hRequired⟩

theorem order_preserving_of_valid [DecidableEq Source] [DecidableEq Target]
    (A : Alignment Source Target) (h : A.Valid) : A.OrderPreserving := by
  rcases (A.valid_iff_components.mp h) with ⟨_, _, _, _, _, _, hOrder⟩
  exact hOrder

/-- Functionality is guaranteed by the `Option`-valued alignment map. -/
theorem relates_unique (A : Alignment Source Target) {s : Source}
    {t₁ t₂ : Target} (h₁ : A.Relates s t₁) (h₂ : A.Relates s t₂) :
    t₁ = t₂ := by
  simp only [Relates] at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

end Alignment

/-! ## Central-clause structural identifiers -/

/-- Neutral unit identifiers for the two Sanskrit central clauses.  Their
names state alignment positions only; they contain no lexical transcription. -/
inductive SanskritCentralUnit where
  | saHS06
  | saHS07
  deriving DecidableEq, Repr

/-- Neutral unit identifiers for the two Tibetan central clauses.  Their
names state alignment positions only; they contain no lexical transcription. -/
inductive TibetanCentralUnit where
  | boHS06
  | boHS07
  deriving DecidableEq, Repr

open Clause

def centralClauseEdition : OrderedEdition Clause where
  units := [HS06, HS07]
  rank
    | HS06 => 6
    | HS07 => 7
    | _ => 31

/-- Source identifiers sorted by the canonical Clause key, not by GRETIL's
printed sequence. -/
def sanskritCanonicalKeyEdition : OrderedEdition SanskritCentralUnit where
  units := [.saHS06, .saHS07]
  rank
    | .saHS06 => 6
    | .saHS07 => 7

/-- Source identifiers sorted by the canonical Clause key, not by Silk's
printed sequence. -/
def tibetanCanonicalKeyEdition : OrderedEdition TibetanCentralUnit where
  units := [.boHS06, .boHS07]
  rank
    | .boHS06 => 6
    | .boHS07 => 7

/-- GRETIL lines 61--65 put the nominal formulation represented by HS07
before the `na pṛthak` formulation represented by HS06. -/
def sanskritDiplomaticCentralOrder : List SanskritCentralUnit :=
  [.saHS07, .saHS06]

/-- Silk's Recension B, p. 177, likewise prints the nominal formulation
before the two `gzhan ma yin` statements represented by HS06. -/
def tibetanDiplomaticCentralOrder : List TibetanCentralUnit :=
  [.boHS07, .boHS06]

theorem diplomatic_orders_reverse_the_canonical_alignment_key :
    sanskritDiplomaticCentralOrder ≠ sanskritCanonicalKeyEdition.units ∧
    tibetanDiplomaticCentralOrder ≠ tibetanCanonicalKeyEdition.units := by
  decide

def sanskritDiplomaticEdition : OrderedEdition SanskritCentralUnit where
  units := sanskritDiplomaticCentralOrder
  rank
    | .saHS07 => 0
    | .saHS06 => 1

def tibetanDiplomaticEdition : OrderedEdition TibetanCentralUnit where
  units := tibetanDiplomaticCentralOrder
  rank
    | .boHS07 => 0
    | .boHS06 => 1

def sanskritCanonicalKeyAlignment : Alignment SanskritCentralUnit Clause where
  source := sanskritCanonicalKeyEdition
  target := centralClauseEdition
  mapsTo
    | .saHS06 => some HS06
    | .saHS07 => some HS07
  required := [HS06, HS07]

def tibetanCanonicalKeyAlignment : Alignment TibetanCentralUnit Clause where
  source := tibetanCanonicalKeyEdition
  target := centralClauseEdition
  mapsTo
    | .boHS06 => some HS06
    | .boHS07 => some HS07
  required := [HS06, HS07]

/-- This alignment uses GRETIL's printed order on the source and the canonical
HS06--HS07 order on the target. -/
def sanskritDiplomaticAlignment : Alignment SanskritCentralUnit Clause where
  source := sanskritDiplomaticEdition
  target := centralClauseEdition
  mapsTo
    | .saHS06 => some HS06
    | .saHS07 => some HS07
  required := [HS06, HS07]

/-- This alignment uses Silk Recension B's printed order on the source and
the canonical HS06--HS07 order on the target. -/
def tibetanDiplomaticAlignment : Alignment TibetanCentralUnit Clause where
  source := tibetanDiplomaticEdition
  target := centralClauseEdition
  mapsTo
    | .boHS06 => some HS06
    | .boHS07 => some HS07
  required := [HS06, HS07]

/-- All structural checks other than target-key order succeed for the actual
GRETIL presentation order. -/
theorem sanskrit_diplomatic_nonorder_checks :
    sanskritDiplomaticAlignment.source.WellFormed ∧
    sanskritDiplomaticAlignment.target.WellFormed ∧
    sanskritDiplomaticAlignment.SourceCovered ∧
    sanskritDiplomaticAlignment.MappedIntoTarget ∧
    sanskritDiplomaticAlignment.RequirementsWellFormed ∧
    sanskritDiplomaticAlignment.RequiredCovered := by
  change sanskritDiplomaticAlignment.source.wellFormed = true ∧
    sanskritDiplomaticAlignment.target.wellFormed = true ∧
    sanskritDiplomaticAlignment.sourceCovered = true ∧
    sanskritDiplomaticAlignment.mappedIntoTarget = true ∧
    sanskritDiplomaticAlignment.requirementsWellFormed = true ∧
    sanskritDiplomaticAlignment.requiredCovered = true
  decide

/-- All structural checks other than target-key order succeed for Silk's
Recension B presentation order. -/
theorem tibetan_diplomatic_nonorder_checks :
    tibetanDiplomaticAlignment.source.WellFormed ∧
    tibetanDiplomaticAlignment.target.WellFormed ∧
    tibetanDiplomaticAlignment.SourceCovered ∧
    tibetanDiplomaticAlignment.MappedIntoTarget ∧
    tibetanDiplomaticAlignment.RequirementsWellFormed ∧
    tibetanDiplomaticAlignment.RequiredCovered := by
  change tibetanDiplomaticAlignment.source.wellFormed = true ∧
    tibetanDiplomaticAlignment.target.wellFormed = true ∧
    tibetanDiplomaticAlignment.sourceCovered = true ∧
    tibetanDiplomaticAlignment.mappedIntoTarget = true ∧
    tibetanDiplomaticAlignment.requirementsWellFormed = true ∧
    tibetanDiplomaticAlignment.requiredCovered = true
  decide

theorem sanskrit_diplomatic_not_order_preserving :
    ¬ sanskritDiplomaticAlignment.OrderPreserving := by
  change ¬ sanskritDiplomaticAlignment.orderPreserving = true
  decide

theorem tibetan_diplomatic_not_order_preserving :
    ¬ tibetanDiplomaticAlignment.OrderPreserving := by
  change ¬ tibetanDiplomaticAlignment.orderPreserving = true
  decide

theorem sanskrit_diplomatic_alignment_not_valid :
    ¬ sanskritDiplomaticAlignment.Valid := by
  change ¬ sanskritDiplomaticAlignment.validate = true
  decide

theorem tibetan_diplomatic_alignment_not_valid :
    ¬ tibetanDiplomaticAlignment.Valid := by
  change ¬ tibetanDiplomaticAlignment.validate = true
  decide

theorem sanskrit_diplomatic_mapping_unique {u : SanskritCentralUnit}
    {c₁ c₂ : Clause} (h₁ : sanskritDiplomaticAlignment.Relates u c₁)
    (h₂ : sanskritDiplomaticAlignment.Relates u c₂) : c₁ = c₂ :=
  sanskritDiplomaticAlignment.relates_unique h₁ h₂

theorem tibetan_diplomatic_mapping_unique {u : TibetanCentralUnit}
    {c₁ c₂ : Clause} (h₁ : tibetanDiplomaticAlignment.Relates u c₁)
    (h₂ : tibetanDiplomaticAlignment.Relates u c₂) : c₁ = c₂ :=
  tibetanDiplomaticAlignment.relates_unique h₁ h₂

theorem sanskrit_canonical_key_alignment_valid :
    sanskritCanonicalKeyAlignment.Valid := by
  change sanskritCanonicalKeyAlignment.validate = true
  decide

theorem tibetan_canonical_key_alignment_valid :
    tibetanCanonicalKeyAlignment.Valid := by
  change tibetanCanonicalKeyAlignment.validate = true
  decide

theorem sanskrit_canonical_key_validator_accepts :
    sanskritCanonicalKeyAlignment.validate = true := by
  decide

theorem tibetan_canonical_key_validator_accepts :
    tibetanCanonicalKeyAlignment.validate = true := by
  decide

theorem sanskrit_canonical_HS06_unique {c : Clause}
    (h : sanskritCanonicalKeyAlignment.Relates .saHS06 c) : c = HS06 := by
  exact sanskritCanonicalKeyAlignment.relates_unique h rfl

theorem tibetan_canonical_HS07_unique {c : Clause}
    (h : tibetanCanonicalKeyAlignment.Relates .boHS07 c) : c = HS07 := by
  exact tibetanCanonicalKeyAlignment.relates_unique h rfl

/-! ## The longer recension's frame alignment -/

inductive LongerFrameUnit where
  | lrNidana
  | lrEnterSamadhi
  | lrQuestion
  | lrAnswer
  | lrEndorsement
  | lrRejoicing
  deriving DecidableEq, Repr

def longerFrameSource : OrderedEdition LongerFrameUnit where
  units := [.lrNidana, .lrEnterSamadhi, .lrQuestion, .lrAnswer,
    .lrEndorsement, .lrRejoicing]
  rank
    | .lrNidana => 0
    | .lrEnterSamadhi => 1
    | .lrQuestion => 2
    | .lrAnswer => 3
    | .lrEndorsement => 4
    | .lrRejoicing => 5

def framePartEdition : OrderedEdition FramePart where
  units := longFrame
  rank
    | .nidana => 0
    | .enterSamadhi => 1
    | .question => 2
    | .answer => 3
    | .endorsement => 4
    | .rejoicing => 5

def longerFrameAlignment : Alignment LongerFrameUnit FramePart where
  source := longerFrameSource
  target := framePartEdition
  mapsTo
    | .lrNidana => some .nidana
    | .lrEnterSamadhi => some .enterSamadhi
    | .lrQuestion => some .question
    | .lrAnswer => some .answer
    | .lrEndorsement => some .endorsement
    | .lrRejoicing => some .rejoicing
  required := longFrame

theorem longer_frame_alignment_valid : longerFrameAlignment.Valid := by
  change longerFrameAlignment.validate = true
  decide

theorem longer_frame_validator_accepts :
    longerFrameAlignment.validate = true := by
  decide

/-! ## Candidate readings and lexical-evidence obligations -/

inductive CentralDirection where
  | formToEmptiness
  | emptinessToForm
  deriving DecidableEq, Repr

inductive CentralConstrual where
  | identity
  | mutualPredication
  | nonSeparation
  | illusionComparison
  deriving DecidableEq, Repr

structure CentralReading where
  direction : CentralDirection
  construal : CentralConstrual
  deriving DecidableEq, Repr

/-- A candidate construal explicitly assigns readings to both HS06 and HS07.
Profiles are formal alternatives; this type makes no claim that a manuscript
attests any one of them. -/
structure CentralProfile where
  hs06 : CentralReading
  hs07 : CentralReading
  deriving DecidableEq, Repr

namespace CentralProfile

def atClause (P : CentralProfile) : Clause → Option CentralReading
  | HS06 => some P.hs06
  | HS07 => some P.hs07
  | _ => none

def uniform (c : CentralConstrual) : CentralProfile where
  hs06 := ⟨.formToEmptiness, c⟩
  hs07 := ⟨.emptinessToForm, c⟩

def identityCandidate : CentralProfile := uniform .identity
def mutualCandidate : CentralProfile := uniform .mutualPredication
def nonSeparationCandidate : CentralProfile := uniform .nonSeparation

/-- A formal variant in which only HS06 receives an illusion construal.  Its
name records a possible profile, not an attribution to an edition. -/
def hs06IllusionCandidate : CentralProfile where
  hs06 := ⟨.formToEmptiness, .illusionComparison⟩
  hs07 := ⟨.emptinessToForm, .mutualPredication⟩

theorem every_profile_covers_central (P : CentralProfile) :
    (∃ r, P.atClause HS06 = some r) ∧
    (∃ r, P.atClause HS07 = some r) := by
  exact ⟨⟨P.hs06, rfl⟩, ⟨P.hs07, rfl⟩⟩

theorem candidate_profiles_distinct :
    identityCandidate ≠ mutualCandidate ∧
    mutualCandidate ≠ nonSeparationCandidate ∧
    hs06IllusionCandidate ≠ mutualCandidate := by
  decide

end CentralProfile

inductive WitnessEdition where
  | gretilPrajnhsuUnicode
  | silk1994KanjurRecensionB
  deriving DecidableEq, Repr

def WitnessEdition.identifier : WitnessEdition → String
  | .gretilPrajnhsuUnicode => "GRETIL:prajnhsu:unicode"
  | .silk1994KanjurRecensionB => "Silk1994:Kanjur:Recension-B:p177"

/-- Half-open token interval `[start, stop)`. -/
structure TokenSpan where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

namespace TokenSpan

def boundedBy (s : TokenSpan) (tokens : List String) : Bool :=
  decide (s.start < s.stop) && decide (s.stop ≤ tokens.length)

def extract (s : TokenSpan) (tokens : List String) : List String :=
  (tokens.drop s.start).take (s.stop - s.start)

end TokenSpan

/-- A lexical witness carries its edition, a punctuation-free bounded evidence
excerpt, and spans for the surface form and emptiness expressions.  `reading`
remains a caller-selected annotation and is deliberately absent from the
lexical validator. -/
structure LexicalWitness (Unit : Type) where
  edition : WitnessEdition
  sourceUnit : Unit
  targetClause : Clause
  reading : CentralReading
  tokens : List String
  excerptSpan : TokenSpan
  formSpan : TokenSpan
  emptinessSpan : TokenSpan

namespace LexicalWitness

def formSurfaceOK {Unit : Type} (w : LexicalWitness Unit) : Bool :=
  let surface := w.formSpan.extract w.tokens
  match w.edition with
  | .gretilPrajnhsuUnicode =>
      surface == ["rūpaṃ"] || surface == ["rūpān"]
  | .silk1994KanjurRecensionB => surface == ["gzugs"]

def emptinessSurfaceOK {Unit : Type} (w : LexicalWitness Unit) : Bool :=
  let surface := w.emptinessSpan.extract w.tokens
  match w.edition with
  | .gretilPrajnhsuUnicode =>
      surface == ["śūnyatā"] || surface == ["śūnyatāyā"] ||
        surface == ["śūnyat'aiva"]
  | .silk1994KanjurRecensionB =>
      surface == ["stong", "pa", "nyid"]

/-- The executable lexical validator checks interval bounds, complete
extraction of the bounded evidence excerpt, a central target key, and the two
edition-specific surface features.  It makes no claim about translation or
philosophical construal. -/
def validate {Unit : Type} (w : LexicalWitness Unit) : Bool :=
  w.excerptSpan.boundedBy w.tokens &&
  w.formSpan.boundedBy w.tokens &&
  w.emptinessSpan.boundedBy w.tokens &&
  decide (w.excerptSpan.extract w.tokens = w.tokens) &&
  decide (w.targetClause = HS06 ∨ w.targetClause = HS07) &&
  w.formSurfaceOK &&
  w.emptinessSurfaceOK

end LexicalWitness

/-- Partial evidence may contain no witness.  Any supplied witness must name
the queried source unit. -/
structure PartialLexicalEvidence (Unit : Type) where
  get : Unit → Option (LexicalWitness Unit)
  coherent : ∀ u w, get u = some w → w.sourceUnit = u

namespace PartialLexicalEvidence

def empty (Unit : Type) : PartialLexicalEvidence Unit where
  get _ := none
  coherent _ _ h := by simp at h

def validateOn {Unit : Type} (E : PartialLexicalEvidence Unit)
    (units : List Unit) : Bool :=
  units.all fun u =>
    match E.get u with
    | none => false
    | some w => w.validate

end PartialLexicalEvidence

/-- A lexical obligation is discharged only when the evidence layer supplies
a coherent nonempty token-span witness for the aligned clause and candidate
reading. -/
def LexicalObligationDischarged {Unit : Type}
    (A : Alignment Unit Clause) (P : CentralProfile)
    (E : PartialLexicalEvidence Unit) (u : Unit) : Prop :=
  ∃ c r w, A.Relates u c ∧ P.atClause c = some r ∧
    E.get u = some w ∧ w.targetClause = c ∧ w.reading = r ∧
    w.validate = true

/-- A mapped central unit with no supplied lexical witness. -/
def MissingLexicalWitness {Unit : Type}
    (A : Alignment Unit Clause) (P : CentralProfile)
    (E : PartialLexicalEvidence Unit) (u : Unit) : Prop :=
  ∃ c r, A.Relates u c ∧ P.atClause c = some r ∧ E.get u = none

theorem empty_evidence_discharges_no_obligation {Unit : Type}
    (A : Alignment Unit Clause) (P : CentralProfile) (u : Unit) :
    ¬ LexicalObligationDischarged A P
      (PartialLexicalEvidence.empty Unit) u := by
  rintro ⟨_, _, w, _, _, hEvidence, _, _⟩
  simp [PartialLexicalEvidence.empty] at hEvidence

/-! ### Checked GRETIL and Silk witnesses -/

def sanskritCentralTokens : SanskritCentralUnit → List String
  | .saHS06 =>
      ["rūpān", "na", "pṛthak", "śūnyatā",
        "śūnyatāyā", "na", "pṛthag", "rūpaṃ"]
  | .saHS07 => ["rūpaṃ", "śūnyatā", "śūnyat'aiva", "rūpaṃ"]

def tibetanCentralTokens : TibetanCentralUnit → List String
  | .boHS06 =>
      ["gzugs", "las", "stong", "pa", "nyid", "gzhan", "ma", "yin", "no"]
  | .boHS07 =>
      ["gzugs", "stong", "pa'o", "stong", "pa", "nyid", "gzugs", "so"]

def sanskritLexicalWitness (P : CentralProfile) :
    SanskritCentralUnit → LexicalWitness SanskritCentralUnit
  | .saHS06 =>
      { edition := .gretilPrajnhsuUnicode
        sourceUnit := .saHS06
        targetClause := HS06
        reading := P.hs06
        tokens := sanskritCentralTokens .saHS06
        excerptSpan := ⟨0, 8⟩
        formSpan := ⟨0, 1⟩
        emptinessSpan := ⟨3, 4⟩ }
  | .saHS07 =>
      { edition := .gretilPrajnhsuUnicode
        sourceUnit := .saHS07
        targetClause := HS07
        reading := P.hs07
        tokens := sanskritCentralTokens .saHS07
        excerptSpan := ⟨0, 4⟩
        formSpan := ⟨0, 1⟩
        emptinessSpan := ⟨1, 2⟩ }

def tibetanLexicalWitness (P : CentralProfile) :
    TibetanCentralUnit → LexicalWitness TibetanCentralUnit
  | .boHS06 =>
      { edition := .silk1994KanjurRecensionB
        sourceUnit := .boHS06
        targetClause := HS06
        reading := P.hs06
        tokens := tibetanCentralTokens .boHS06
        excerptSpan := ⟨0, 9⟩
        formSpan := ⟨0, 1⟩
        emptinessSpan := ⟨2, 5⟩ }
  | .boHS07 =>
      { edition := .silk1994KanjurRecensionB
        sourceUnit := .boHS07
        targetClause := HS07
        reading := P.hs07
        tokens := tibetanCentralTokens .boHS07
        excerptSpan := ⟨0, 8⟩
        formSpan := ⟨0, 1⟩
        emptinessSpan := ⟨3, 6⟩ }

def sanskritLexicalEvidence (P : CentralProfile) :
    PartialLexicalEvidence SanskritCentralUnit where
  get u := some (sanskritLexicalWitness P u)
  coherent u w h := by
    have hw : sanskritLexicalWitness P u = w := Option.some.inj h
    rw [← hw]
    cases u <;> rfl

def tibetanLexicalEvidence (P : CentralProfile) :
    PartialLexicalEvidence TibetanCentralUnit where
  get u := some (tibetanLexicalWitness P u)
  coherent u w h := by
    have hw : tibetanLexicalWitness P u = w := Option.some.inj h
    rw [← hw]
    cases u <;> rfl

theorem sanskrit_HS06_span_extraction (P : CentralProfile) :
    ((sanskritLexicalWitness P .saHS06).formSpan.extract
        (sanskritLexicalWitness P .saHS06).tokens = ["rūpān"]) ∧
    ((sanskritLexicalWitness P .saHS06).emptinessSpan.extract
        (sanskritLexicalWitness P .saHS06).tokens = ["śūnyatā"]) := by
  constructor <;> rfl

theorem sanskrit_HS07_span_extraction (P : CentralProfile) :
    ((sanskritLexicalWitness P .saHS07).formSpan.extract
        (sanskritLexicalWitness P .saHS07).tokens = ["rūpaṃ"]) ∧
    ((sanskritLexicalWitness P .saHS07).emptinessSpan.extract
        (sanskritLexicalWitness P .saHS07).tokens = ["śūnyatā"]) := by
  constructor <;> rfl

theorem tibetan_HS06_span_extraction (P : CentralProfile) :
    ((tibetanLexicalWitness P .boHS06).formSpan.extract
        (tibetanLexicalWitness P .boHS06).tokens = ["gzugs"]) ∧
    ((tibetanLexicalWitness P .boHS06).emptinessSpan.extract
        (tibetanLexicalWitness P .boHS06).tokens = ["stong", "pa", "nyid"]) := by
  constructor <;> rfl

theorem tibetan_HS07_span_extraction (P : CentralProfile) :
    ((tibetanLexicalWitness P .boHS07).formSpan.extract
        (tibetanLexicalWitness P .boHS07).tokens = ["gzugs"]) ∧
    ((tibetanLexicalWitness P .boHS07).emptinessSpan.extract
        (tibetanLexicalWitness P .boHS07).tokens = ["stong", "pa", "nyid"]) := by
  constructor <;> rfl

theorem sanskrit_lexical_validator_accepts (P : CentralProfile) :
    (sanskritLexicalEvidence P).validateOn sanskritDiplomaticCentralOrder = true := by
  rfl

theorem tibetan_lexical_validator_accepts (P : CentralProfile) :
    (tibetanLexicalEvidence P).validateOn tibetanDiplomaticCentralOrder = true := by
  rfl

theorem lexical_validation_is_construal_neutral (P Q : CentralProfile) :
    (sanskritLexicalEvidence P).validateOn sanskritDiplomaticCentralOrder =
      (sanskritLexicalEvidence Q).validateOn sanskritDiplomaticCentralOrder ∧
    (tibetanLexicalEvidence P).validateOn tibetanDiplomaticCentralOrder =
      (tibetanLexicalEvidence Q).validateOn tibetanDiplomaticCentralOrder := by
  constructor <;> rfl

theorem sanskrit_HS06_lexical_obligation_discharged
    (P : CentralProfile) :
    LexicalObligationDischarged sanskritCanonicalKeyAlignment P
      (sanskritLexicalEvidence P) .saHS06 := by
  refine ⟨HS06, P.hs06, sanskritLexicalWitness P .saHS06,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  rfl

theorem sanskrit_HS07_lexical_obligation_discharged
    (P : CentralProfile) :
    LexicalObligationDischarged sanskritCanonicalKeyAlignment P
      (sanskritLexicalEvidence P) .saHS07 := by
  refine ⟨HS07, P.hs07, sanskritLexicalWitness P .saHS07,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  rfl

theorem tibetan_HS06_lexical_obligation_discharged
    (P : CentralProfile) :
    LexicalObligationDischarged tibetanCanonicalKeyAlignment P
      (tibetanLexicalEvidence P) .boHS06 := by
  refine ⟨HS06, P.hs06, tibetanLexicalWitness P .boHS06,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  rfl

theorem tibetan_HS07_lexical_obligation_discharged
    (P : CentralProfile) :
    LexicalObligationDischarged tibetanCanonicalKeyAlignment P
      (tibetanLexicalEvidence P) .boHS07 := by
  refine ⟨HS07, P.hs07, tibetanLexicalWitness P .boHS07,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  rfl

theorem sanskrit_HS06_lexical_obligation
    (P : CentralProfile) :
    MissingLexicalWitness sanskritCanonicalKeyAlignment P
      (PartialLexicalEvidence.empty SanskritCentralUnit) .saHS06 := by
  exact ⟨HS06, P.hs06, rfl, rfl, rfl⟩

theorem sanskrit_HS07_lexical_obligation
    (P : CentralProfile) :
    MissingLexicalWitness sanskritCanonicalKeyAlignment P
      (PartialLexicalEvidence.empty SanskritCentralUnit) .saHS07 := by
  exact ⟨HS07, P.hs07, rfl, rfl, rfl⟩

theorem tibetan_HS06_lexical_obligation
    (P : CentralProfile) :
    MissingLexicalWitness tibetanCanonicalKeyAlignment P
      (PartialLexicalEvidence.empty TibetanCentralUnit) .boHS06 := by
  exact ⟨HS06, P.hs06, rfl, rfl, rfl⟩

theorem tibetan_HS07_lexical_obligation
    (P : CentralProfile) :
    MissingLexicalWitness tibetanCanonicalKeyAlignment P
      (PartialLexicalEvidence.empty TibetanCentralUnit) .boHS07 := by
  exact ⟨HS07, P.hs07, rfl, rfl, rfl⟩

theorem sanskrit_empty_evidence_leaves_HS06_undischarged
    (P : CentralProfile) :
    ¬ LexicalObligationDischarged sanskritCanonicalKeyAlignment P
      (PartialLexicalEvidence.empty SanskritCentralUnit) .saHS06 :=
  empty_evidence_discharges_no_obligation _ _ _

theorem tibetan_empty_evidence_leaves_HS07_undischarged
    (P : CentralProfile) :
    ¬ LexicalObligationDischarged tibetanCanonicalKeyAlignment P
      (PartialLexicalEvidence.empty TibetanCentralUnit) .boHS07 :=
  empty_evidence_discharges_no_obligation _ _ _

/-! ## Structural alignment does not identify texts -/

/-- Synthetic measures used only as a countermodel to the implication from
structural validity to character-count equality. -/
def syntheticSourceCount : SanskritCentralUnit → Nat
  | .saHS06 => 0
  | .saHS07 => 1

theorem structural_alignment_does_not_force_character_counts :
    sanskritCanonicalKeyAlignment.Valid ∧
    sanskritCanonicalKeyAlignment.Relates .saHS06 HS06 ∧
    syntheticSourceCount .saHS06 ≠ char_count HS06 := by
  exact ⟨sanskrit_canonical_key_alignment_valid, rfl, by decide⟩

/-- Arbitrary text codes provide a second countermodel: the same valid
alignment is compatible with unequal source and target lexical values. -/
theorem structural_alignment_does_not_force_text_equivalence :
    ∃ sourceText : SanskritCentralUnit → Nat,
      ∃ targetText : Clause → Nat,
        sanskritCanonicalKeyAlignment.Valid ∧
        sanskritCanonicalKeyAlignment.Relates .saHS07 HS07 ∧
        sourceText .saHS07 ≠ targetText HS07 := by
  refine ⟨fun _ => 0, fun _ => 1,
    sanskrit_canonical_key_alignment_valid, rfl, ?_⟩
  decide

end BuddhistComparativeLogic
