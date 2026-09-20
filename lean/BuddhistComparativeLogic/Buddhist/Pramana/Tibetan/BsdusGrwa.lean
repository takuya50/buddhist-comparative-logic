/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.Definitions
import BuddhistComparativeLogic.Buddhist.Pramana.Dharmakirti

/-!
# Four-cell predicate comparison from *bsdus grwa*

This module isolates one extensional exercise found in Tibetan collected-topic
(*bsdus grwa*) pedagogy: compare two predicates by asking which of the four
joint truth cells have witnesses.  It is not an edition of a particular
manual, and it does not claim that this finite predicate semantics exhausts
the intensional or dialectical uses of the historical relation vocabulary.

The formal core records the four cells, the familiar coextension, exclusion,
proper-inclusion, three-possibility, and four-possibility conditions.  A
complete finite enumeration produces a Boolean witness profile consumed by
two executable reports: an all-matches list and an ordered primary diagnostic.
Real adapters identify coextension with the
existing Tibetan definition interface and the two directions of pervasion
with `Dharmakirti.Model.vyapti`.  A finite countermodel shows why being neither
coextensive nor mutually exclusive does not establish all four possibilities.

Source status (accessed 2026-09-19): Ngag-wang-tra-shi's bilingual *Collected
Topics of Epistemology*, vol. 1, chapter 1, pp. 31–32 explicitly lists and
witnesses the four color/shape possibilities
<https://uma-tibet.s3.us-east-1.amazonaws.com/public/pdf/gelug-curriculum/logic-debate/collected-topics/gomang-collected-topics/NWT_GomangCollectedTopics_Ch01-12_HowToDebate.pdf>;
Magee maps the wider comparison taxonomy and warns that the compared phenomena
are not concepts or sets
<https://maitripa.org/wp-content/uploads/2019/09/Open-Source_Geshe.pdf>.
The published translation is consulted but not reproduced.  The Boolean cells
and executable reports are project-authored extensional encodings.
-/

namespace BuddhistComparativeLogic.BsdusGrwa

/-- Boolean predicates keep the finite classifier executable. -/
abbrev Predicate (Object : Type u) := Object → Bool

inductive Cell where
  | both
  | leftOnly
  | rightOnly
  | neither
  deriving DecidableEq, Repr

/-- Propositional membership in one joint truth cell. -/
def InCell (A B : Predicate Object) (cell : Cell) (object : Object) : Prop :=
  match cell with
  | .both => A object = true ∧ B object = true
  | .leftOnly => A object = true ∧ B object = false
  | .rightOnly => A object = false ∧ B object = true
  | .neither => A object = false ∧ B object = false

def WitnessProfile (A B : Predicate Object) : Cell → Prop :=
  fun cell => ∃ object, InCell A B cell object

def Coextensive (A B : Predicate Object) : Prop :=
  ∀ object, A object = B object

def MutuallyExclusive (A B : Predicate Object) : Prop :=
  ∀ object, ¬ (A object = true ∧ B object = true)

/-- `A` properly includes `B`: every `B` is an `A`, while some `A` is not a
`B`.  The names describe extensions rather than grammatical subjects. -/
def LeftProperlyIncludes (A B : Predicate Object) : Prop :=
  (∀ object, B object = true → A object = true) ∧
    ∃ object, A object = true ∧ B object = false

def RightProperlyIncludes (A B : Predicate Object) : Prop :=
  (∀ object, A object = true → B object = true) ∧
    ∃ object, A object = false ∧ B object = true

def FourPossibilities (A B : Predicate Object) : Prop :=
  (∃ object, InCell A B .both object) ∧
    (∃ object, InCell A B .leftOnly object) ∧
    (∃ object, InCell A B .rightOnly object) ∧
    ∃ object, InCell A B .neither object

/-- The left-inclusion three-cell pattern additionally has shared, left-only,
and neither witnesses. -/
def LeftThreePossibilities (A B : Predicate Object) : Prop :=
  WitnessProfile A B .both ∧
    WitnessProfile A B .leftOnly ∧
    ¬ WitnessProfile A B .rightOnly ∧
    WitnessProfile A B .neither

def RightThreePossibilities (A B : Predicate Object) : Prop :=
  WitnessProfile A B .both ∧
    ¬ WitnessProfile A B .leftOnly ∧
    WitnessProfile A B .rightOnly ∧
    WitnessProfile A B .neither

theorem four_possibilities_iff_all_cells_inhabited
    {A B : Predicate Object} :
    FourPossibilities A B ↔ ∀ cell, WitnessProfile A B cell := by
  constructor
  · rintro ⟨both, left, right, neither⟩ cell
    cases cell
    · exact both
    · exact left
    · exact right
    · exact neither
  · intro all
    exact ⟨all .both, all .leftOnly, all .rightOnly, all .neither⟩

theorem coextensive_iff_no_one_sided_cells {A B : Predicate Object} :
    Coextensive A B ↔
      ¬ WitnessProfile A B .leftOnly ∧
        ¬ WitnessProfile A B .rightOnly := by
  constructor
  · intro same
    constructor
    · rintro ⟨object, hasA, notB⟩
      rw [same object] at hasA
      simp_all
    · rintro ⟨object, notA, hasB⟩
      rw [same object] at notA
      simp_all
  · rintro ⟨noLeft, noRight⟩ object
    cases hasA : A object <;> cases hasB : B object
    · rfl
    · exact False.elim (noRight ⟨object, hasA, hasB⟩)
    · exact False.elim (noLeft ⟨object, hasA, hasB⟩)
    · rfl

theorem mutually_exclusive_iff_no_shared_cell {A B : Predicate Object} :
    MutuallyExclusive A B ↔ ¬ WitnessProfile A B .both := by
  constructor
  · intro exclusive
    rintro ⟨object, shared⟩
    exact exclusive object shared
  · intro noShared object shared
    exact noShared ⟨object, shared⟩

theorem left_properly_includes_iff_cells {A B : Predicate Object} :
    LeftProperlyIncludes A B ↔
      ¬ WitnessProfile A B .rightOnly ∧
        WitnessProfile A B .leftOnly := by
  constructor
  · rintro ⟨includes, left⟩
    refine ⟨?_, left⟩
    rintro ⟨object, notA, hasB⟩
    rw [includes object hasB] at notA
    contradiction
  · rintro ⟨noRight, left⟩
    refine ⟨?_, left⟩
    intro object hasB
    cases hasA : A object
    · exact False.elim (noRight ⟨object, hasA, hasB⟩)
    · rfl

theorem right_properly_includes_iff_cells {A B : Predicate Object} :
    RightProperlyIncludes A B ↔
      ¬ WitnessProfile A B .leftOnly ∧
        WitnessProfile A B .rightOnly := by
  constructor
  · rintro ⟨includes, right⟩
    refine ⟨?_, right⟩
    rintro ⟨object, hasA, notB⟩
    rw [includes object hasA] at notB
    contradiction
  · rintro ⟨noLeft, right⟩
    refine ⟨?_, right⟩
    intro object hasA
    cases hasB : B object
    · exact False.elim (noLeft ⟨object, hasA, hasB⟩)
    · rfl

theorem left_three_implies_strict_inclusion
    {A B : Predicate Object} (three : LeftThreePossibilities A B) :
    LeftProperlyIncludes A B :=
  left_properly_includes_iff_cells.mpr ⟨three.2.2.1, three.2.1⟩

theorem right_three_implies_strict_inclusion
    {A B : Predicate Object} (three : RightThreePossibilities A B) :
    RightProperlyIncludes A B :=
  right_properly_includes_iff_cells.mpr ⟨three.2.1, three.2.2.1⟩

theorem four_possibilities_implies_bidirectional_nonpervasion
    {A B : Predicate Object} (four : FourPossibilities A B) :
    (¬ ∀ object, A object = true → B object = true) ∧
      ¬ ∀ object, B object = true → A object = true := by
  constructor
  · intro pervasion
    obtain ⟨object, hasA, notB⟩ := four.2.1
    have := pervasion object hasA
    simp_all
  · intro pervasion
    obtain ⟨object, notA, hasB⟩ := four.2.2.1
    have := pervasion object hasB
    simp_all

/-! ## Complete finite enumeration and executable classification -/

/-- A supplied list is a complete finite enumeration when every object occurs
in it.  The proof field is erased; the list drives the computation. -/
structure FiniteEnumeration (Object : Type u) where
  items : List Object
  complete : ∀ object, object ∈ items

def cellTest (A B : Predicate Object) (cell : Cell) (object : Object) : Bool :=
  match cell with
  | .both => A object && B object
  | .leftOnly => A object && !B object
  | .rightOnly => !A object && B object
  | .neither => !A object && !B object

theorem cellTest_eq_true_iff {A B : Predicate Object} {cell : Cell}
    {object : Object} :
    cellTest A B cell object = true ↔ InCell A B cell object := by
  cases cell <;> simp [cellTest, InCell]

structure CellBits where
  both : Bool
  leftOnly : Bool
  rightOnly : Bool
  neither : Bool
  deriving DecidableEq, Repr

def CellBits.at (bits : CellBits) : Cell → Bool
  | .both => bits.both
  | .leftOnly => bits.leftOnly
  | .rightOnly => bits.rightOnly
  | .neither => bits.neither

def observedBits (enumeration : FiniteEnumeration Object)
    (A B : Predicate Object) : CellBits where
  both := enumeration.items.any (cellTest A B .both)
  leftOnly := enumeration.items.any (cellTest A B .leftOnly)
  rightOnly := enumeration.items.any (cellTest A B .rightOnly)
  neither := enumeration.items.any (cellTest A B .neither)

theorem observed_bit_iff_cell_inhabited
    (enumeration : FiniteEnumeration Object) (A B : Predicate Object)
    (cell : Cell) :
    (observedBits enumeration A B).at cell = true ↔
      WitnessProfile A B cell := by
  cases cell <;>
    simp only [observedBits, CellBits.at, List.any_eq_true]
  all_goals
    constructor
    · rintro ⟨object, membership, test⟩
      exact ⟨object, cellTest_eq_true_iff.mp test⟩
    · rintro ⟨object, inCell⟩
      exact ⟨object, enumeration.complete object,
        cellTest_eq_true_iff.mpr inCell⟩

inductive RelationKind where
  | coextensive
  | mutuallyExclusive
  | leftProperlyIncludes
  | rightProperlyIncludes
  | leftThreePossibilities
  | rightThreePossibilities
  | fourPossibilities
  | unclassified
  deriving DecidableEq, Repr

/-- A relation statement phrased only through the four witness cells. -/
def Classifies (A B : Predicate Object) : RelationKind → Prop
  | .coextensive =>
      ¬ WitnessProfile A B .leftOnly ∧
        ¬ WitnessProfile A B .rightOnly
  | .mutuallyExclusive => ¬ WitnessProfile A B .both
  | .leftProperlyIncludes =>
      ¬ WitnessProfile A B .rightOnly ∧
        WitnessProfile A B .leftOnly
  | .rightProperlyIncludes =>
      ¬ WitnessProfile A B .leftOnly ∧
        WitnessProfile A B .rightOnly
  | .leftThreePossibilities => LeftThreePossibilities A B
  | .rightThreePossibilities => RightThreePossibilities A B
  | .fourPossibilities => ∀ cell, WitnessProfile A B cell
  | .unclassified =>
      ¬ (¬ WitnessProfile A B .leftOnly ∧
          ¬ WitnessProfile A B .rightOnly) ∧
        ¬ (¬ WitnessProfile A B .both) ∧
        ¬ (¬ WitnessProfile A B .rightOnly ∧
          WitnessProfile A B .leftOnly) ∧
        ¬ (¬ WitnessProfile A B .leftOnly ∧
          WitnessProfile A B .rightOnly) ∧
        ¬ LeftThreePossibilities A B ∧
        ¬ RightThreePossibilities A B ∧
        ¬ (∀ cell, WitnessProfile A B cell)

def BitClassifies (bits : CellBits) : RelationKind → Prop
  | .coextensive => bits.leftOnly = false ∧ bits.rightOnly = false
  | .mutuallyExclusive => bits.both = false
  | .leftProperlyIncludes =>
      bits.rightOnly = false ∧ bits.leftOnly = true
  | .rightProperlyIncludes =>
      bits.leftOnly = false ∧ bits.rightOnly = true
  | .leftThreePossibilities =>
      bits.both = true ∧ bits.leftOnly = true ∧
        bits.rightOnly = false ∧ bits.neither = true
  | .rightThreePossibilities =>
      bits.both = true ∧ bits.leftOnly = false ∧
        bits.rightOnly = true ∧ bits.neither = true
  | .fourPossibilities =>
      bits.both = true ∧ bits.leftOnly = true ∧
        bits.rightOnly = true ∧ bits.neither = true
  | .unclassified =>
      ¬ (bits.leftOnly = false ∧ bits.rightOnly = false) ∧
        ¬ (bits.both = false) ∧
        ¬ (bits.rightOnly = false ∧ bits.leftOnly = true) ∧
        ¬ (bits.leftOnly = false ∧ bits.rightOnly = true) ∧
        ¬ (bits.both = true ∧ bits.leftOnly = true ∧
          bits.rightOnly = false ∧ bits.neither = true) ∧
        ¬ (bits.both = true ∧ bits.leftOnly = false ∧
          bits.rightOnly = true ∧ bits.neither = true) ∧
        ¬ (bits.both = true ∧ bits.leftOnly = true ∧
          bits.rightOnly = true ∧ bits.neither = true)

/-- Pure Boolean code: all sixteen profiles reduce to one tag. -/
def classifyBits (bits : CellBits) : RelationKind :=
  if !bits.leftOnly && !bits.rightOnly then .coextensive
  else if !bits.both then .mutuallyExclusive
  else if bits.both && bits.leftOnly && !bits.rightOnly && bits.neither then
    .leftThreePossibilities
  else if bits.both && !bits.leftOnly && bits.rightOnly && bits.neither then
    .rightThreePossibilities
  else if !bits.rightOnly && bits.leftOnly then .leftProperlyIncludes
  else if !bits.leftOnly && bits.rightOnly then .rightProperlyIncludes
  else if bits.both && bits.leftOnly && bits.rightOnly && bits.neither then
    .fourPossibilities
  else .unclassified

theorem classifyBits_sound (bits : CellBits) :
    BitClassifies bits (classifyBits bits) := by
  rcases bits with ⟨both, left, right, neither⟩
  cases both <;> cases left <;> cases right <;> cases neither <;>
    simp [classifyBits, BitClassifies]

/-- The ordered primary diagnostic for an enumerated finite domain.  Some
relations overlap on degenerate profiles, so this function intentionally
returns only the first applicable tag.  Use `classifyAll` below when every
applicable relation is wanted. -/
def classifyPrimary (enumeration : FiniteEnumeration Object)
    (A B : Predicate Object) : RelationKind :=
  classifyBits (observedBits enumeration A B)

theorem observed_bit_false_iff_cell_empty
    (enumeration : FiniteEnumeration Object) (A B : Predicate Object)
    (cell : Cell) :
    (observedBits enumeration A B).at cell = false ↔
      ¬ WitnessProfile A B cell :=
  Bool.eq_false_iff.trans
    (not_congr (observed_bit_iff_cell_inhabited enumeration A B cell))

theorem bit_classification_matches_semantics
    (enumeration : FiniteEnumeration Object) (A B : Predicate Object)
    (kind : RelationKind) :
    BitClassifies (observedBits enumeration A B) kind ↔
      Classifies A B kind := by
  have both := observed_bit_iff_cell_inhabited enumeration A B .both
  have left := observed_bit_iff_cell_inhabited enumeration A B .leftOnly
  have right := observed_bit_iff_cell_inhabited enumeration A B .rightOnly
  have neither := observed_bit_iff_cell_inhabited enumeration A B .neither
  have noBoth := observed_bit_false_iff_cell_empty enumeration A B .both
  have noLeft := observed_bit_false_iff_cell_empty enumeration A B .leftOnly
  have noRight := observed_bit_false_iff_cell_empty enumeration A B .rightOnly
  have coextensiveCells := and_congr noLeft noRight
  have leftInclusionCells := and_congr noRight left
  have rightInclusionCells := and_congr noLeft right
  have leftThreeCells :
      ((observedBits enumeration A B).both = true ∧
        (observedBits enumeration A B).leftOnly = true ∧
        (observedBits enumeration A B).rightOnly = false ∧
        (observedBits enumeration A B).neither = true) ↔
        LeftThreePossibilities A B :=
    and_congr both (and_congr left (and_congr noRight neither))
  have rightThreeCells :
      ((observedBits enumeration A B).both = true ∧
        (observedBits enumeration A B).leftOnly = false ∧
        (observedBits enumeration A B).rightOnly = true ∧
        (observedBits enumeration A B).neither = true) ↔
        RightThreePossibilities A B :=
    and_congr both (and_congr noLeft (and_congr right neither))
  have fourCells :
      ((observedBits enumeration A B).both = true ∧
        (observedBits enumeration A B).leftOnly = true ∧
        (observedBits enumeration A B).rightOnly = true ∧
        (observedBits enumeration A B).neither = true) ↔
        ∀ cell, WitnessProfile A B cell := by
    constructor
    · rintro ⟨hasBoth, hasLeft, hasRight, hasNeither⟩ cell
      cases cell
      · exact both.mp hasBoth
      · exact left.mp hasLeft
      · exact right.mp hasRight
      · exact neither.mp hasNeither
    · intro all
      exact ⟨both.mpr (all .both), left.mpr (all .leftOnly),
        right.mpr (all .rightOnly), neither.mpr (all .neither)⟩
  cases kind
  · exact coextensiveCells
  · exact noBoth
  · exact leftInclusionCells
  · exact rightInclusionCells
  · exact leftThreeCells
  · exact rightThreeCells
  · exact fourCells
  · exact and_congr (not_congr coextensiveCells)
      (and_congr (not_congr noBoth)
        (and_congr (not_congr leftInclusionCells)
          (and_congr (not_congr rightInclusionCells)
            (and_congr (not_congr leftThreeCells)
              (and_congr (not_congr rightThreeCells)
                (not_congr fourCells))))))

/-- Soundness of the ordered primary diagnostic.  Exhaustiveness here means
that its residual tag states the failure of every named relation; it does not
assert that the named relations form a disjoint partition. -/
theorem classifyPrimary_sound (enumeration : FiniteEnumeration Object)
    (A B : Predicate Object) :
    Classifies A B (classifyPrimary enumeration A B) :=
  (bit_classification_matches_semantics enumeration A B _).mp
    (classifyBits_sound (observedBits enumeration A B))

theorem classification_exists (enumeration : FiniteEnumeration Object)
    (A B : Predicate Object) :
    ∃ kind, Classifies A B kind :=
  ⟨classifyPrimary enumeration A B,
    classifyPrimary_sound enumeration A B⟩

/-! ### All matching relations -/

def namedRelationKinds : List RelationKind :=
  [.coextensive, .mutuallyExclusive, .leftProperlyIncludes,
    .rightProperlyIncludes, .leftThreePossibilities,
    .rightThreePossibilities, .fourPossibilities]

/-- Executable truth test for each named bit-level relation.  The residual
tag is handled by `classifyAll` only when no named relation matches. -/
def matchesNamed (bits : CellBits) : RelationKind → Bool
  | .coextensive => !bits.leftOnly && !bits.rightOnly
  | .mutuallyExclusive => !bits.both
  | .leftProperlyIncludes => !bits.rightOnly && bits.leftOnly
  | .rightProperlyIncludes => !bits.leftOnly && bits.rightOnly
  | .leftThreePossibilities =>
      bits.both && bits.leftOnly && !bits.rightOnly && bits.neither
  | .rightThreePossibilities =>
      bits.both && !bits.leftOnly && bits.rightOnly && bits.neither
  | .fourPossibilities =>
      bits.both && bits.leftOnly && bits.rightOnly && bits.neither
  | .unclassified => false

/-- Return every named relation satisfied by the four-bit profile.  The
singleton residual report is returned exactly when the filtered list is
empty. -/
def classifyAll (bits : CellBits) : List RelationKind :=
  let matching := namedRelationKinds.filter (matchesNamed bits)
  if matching.isEmpty then [.unclassified] else matching

/-- Complete sixteen-profile audit of the all-matches classifier. -/
theorem classifyAll_membership_iff (bits : CellBits) (kind : RelationKind) :
    kind ∈ classifyAll bits ↔ BitClassifies bits kind := by
  rcases bits with ⟨both, left, right, neither⟩
  cases both <;> cases left <;> cases right <;> cases neither <;>
    cases kind <;>
    simp [classifyAll, namedRelationKinds, matchesNamed, BitClassifies]

/-- Each applicable tag occurs exactly once in the all-matches report. -/
theorem classifyAll_nodup (bits : CellBits) :
    (classifyAll bits).Nodup := by
  rcases bits with ⟨both, left, right, neither⟩
  cases both <;> cases left <;> cases right <;> cases neither <;>
    decide

/-- Membership in the executable all-matches report is equivalent to the
corresponding semantic relation on the completely enumerated domain. -/
theorem classifyAll_semantic_membership_iff
    (enumeration : FiniteEnumeration Object) (A B : Predicate Object)
    (kind : RelationKind) :
    kind ∈ classifyAll (observedBits enumeration A B) ↔
      Classifies A B kind :=
  (classifyAll_membership_iff _ kind).trans
    (bit_classification_matches_semantics enumeration A B kind)

theorem classifyAll_sound
    (enumeration : FiniteEnumeration Object) (A B : Predicate Object)
    {kind : RelationKind}
    (member : kind ∈ classifyAll (observedBits enumeration A B)) :
    Classifies A B kind :=
  (classifyAll_semantic_membership_iff enumeration A B kind).mp member

theorem classifyAll_complete
    (enumeration : FiniteEnumeration Object) (A B : Predicate Object)
    {kind : RelationKind} (classified : Classifies A B kind) :
    kind ∈ classifyAll (observedBits enumeration A B) :=
  (classifyAll_semantic_membership_iff enumeration A B kind).mpr classified

theorem classified_coextensive_iff {A B : Predicate Object} :
    Classifies A B .coextensive ↔ Coextensive A B :=
  coextensive_iff_no_one_sided_cells.symm

theorem classified_exclusive_iff {A B : Predicate Object} :
    Classifies A B .mutuallyExclusive ↔ MutuallyExclusive A B :=
  mutually_exclusive_iff_no_shared_cell.symm

theorem classified_left_inclusion_iff {A B : Predicate Object} :
    Classifies A B .leftProperlyIncludes ↔ LeftProperlyIncludes A B :=
  left_properly_includes_iff_cells.symm

theorem classified_right_inclusion_iff {A B : Predicate Object} :
    Classifies A B .rightProperlyIncludes ↔ RightProperlyIncludes A B :=
  right_properly_includes_iff_cells.symm

theorem classified_left_three_iff {A B : Predicate Object} :
    Classifies A B .leftThreePossibilities ↔
      LeftThreePossibilities A B :=
  Iff.rfl

theorem classified_right_three_iff {A B : Predicate Object} :
    Classifies A B .rightThreePossibilities ↔
      RightThreePossibilities A B :=
  Iff.rfl

theorem classified_four_iff {A B : Predicate Object} :
    Classifies A B .fourPossibilities ↔ FourPossibilities A B :=
  four_possibilities_iff_all_cells_inhabited.symm

/-! ## Typed adapters to existing project interfaces -/

def asDefinitionTriad (A B : Predicate Object) (basis : Object) :
    BuddhistComparativeLogic.TibetanDefinitions.DefinitionTriad Object Unit where
  hasFeatures object _ := A object = true
  requires _ := True
  definiendum object := B object = true
  basis := basis

theorem coextensive_iff_definition_triad
    {A B : Predicate Object} (basis : Object) :
    Coextensive A B ↔ (asDefinitionTriad A B basis).Coextensive := by
  change (∀ object, A object = B object) ↔
    ∀ object, B object = true ↔
      ∀ _ : Unit, True → A object = true
  constructor
  · intro same object
    constructor
    · intro hasB _ _
      exact (Bool.eq_iff_iff.mp (same object)).mpr hasB
    · intro condition
      exact (Bool.eq_iff_iff.mp (same object)).mp
        (condition () trivial)
  · intro same object
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hasA
      exact (same object).mpr (fun _ _ => hasA)
    · intro hasB
      exact (same object).mp hasB () trivial

def asVyaptiModel (reason conclusion : Predicate Object) (basis : Object) :
    BuddhistComparativeLogic.Dharmakirti.Model Object where
  paksa := basis
  sadhya object := conclusion object = true
  reason object := reason object = true
  vyapti := ∀ object, reason object = true → conclusion object = true
  vyapti_iff := Iff.rfl

theorem four_possibilities_refutes_both_vyapti_models
    {A B : Predicate Object} (basis : Object)
    (four : FourPossibilities A B) :
    ¬ (asVyaptiModel A B basis).vyapti ∧
      ¬ (asVyaptiModel B A basis).vyapti :=
  four_possibilities_implies_bidirectional_nonpervasion four

/-! ## Inhabited finite scope countermodel -/

inductive ThreeCell where
  | shared
  | left
  | outside
  deriving DecidableEq, Repr

def sampleA : Predicate ThreeCell
  | .shared | .left => true
  | .outside => false

def sampleB : Predicate ThreeCell
  | .shared => true
  | .left | .outside => false

def threeCellEnumeration : FiniteEnumeration ThreeCell where
  items := [.shared, .left, .outside]
  complete := by intro object; cases object <;> simp

/-- The shared and left-only witnesses refute coextension and exclusion, but
the absent right-only cell blocks four possibilities. -/
theorem neither_coextensive_nor_exclusive_does_not_give_four :
    Nonempty ThreeCell ∧
      ¬ Coextensive sampleA sampleB ∧
      ¬ MutuallyExclusive sampleA sampleB ∧
      ¬ FourPossibilities sampleA sampleB := by
  refine ⟨⟨.shared⟩, ?_, ?_, ?_⟩
  · intro same
    have atLeft := same .left
    simp [sampleA, sampleB] at atLeft
  · intro exclusive
    exact exclusive .shared ⟨rfl, rfl⟩
  · rintro ⟨both, left, right, neither⟩
    obtain ⟨object, inRight⟩ := right
    cases object <;> simp [InCell, sampleA, sampleB] at inRight

theorem sample_primary_classifies_as_left_three_possibilities :
    classifyPrimary threeCellEnumeration sampleA sampleB =
      .leftThreePossibilities :=
  rfl

theorem sample_all_relations_retain_three_and_strict_inclusion :
    .leftThreePossibilities ∈
        classifyAll (observedBits threeCellEnumeration sampleA sampleB) ∧
      .leftProperlyIncludes ∈
        classifyAll (observedBits threeCellEnumeration sampleA sampleB) := by
  decide

/-- Named relations can overlap on degenerate profiles.  A singleton that is
`A` but not `B` is both mutually exclusive and a proper left inclusion.  The
all-matches report retains both facts instead of hiding the overlap. -/
def singletonA : Predicate Unit := fun _ => true

def singletonB : Predicate Unit := fun _ => false

def unitEnumeration : FiniteEnumeration Unit where
  items := [()]
  complete := by intro object; cases object; simp

theorem mutually_exclusive_and_left_inclusion_can_overlap :
    MutuallyExclusive singletonA singletonB ∧
      LeftProperlyIncludes singletonA singletonB ∧
      .mutuallyExclusive ∈
        classifyAll (observedBits unitEnumeration singletonA singletonB) ∧
      .leftProperlyIncludes ∈
        classifyAll (observedBits unitEnumeration singletonA singletonB) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro object
    cases object
    simp [singletonA, singletonB]
  · exact ⟨by intro object; cases object; simp [singletonA, singletonB],
      ⟨(), rfl, rfl⟩⟩
  · decide
  · decide

end BuddhistComparativeLogic.BsdusGrwa
