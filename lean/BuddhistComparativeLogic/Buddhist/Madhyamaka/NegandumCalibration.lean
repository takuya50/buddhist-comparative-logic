/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.Definitions
import BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceModes
import BuddhistComparativeLogic.Buddhist.HeartSutra.Emptiness

/-!
# Calibrating an object of negation

This module gives a restrained predicate reconstruction of the Gelug concern,
especially associated with Tsongkhapa, that an object of negation must be
neither too broad nor too narrow.  It does not treat this calibration as the
single Tibetan interpretation of Madhyamaka.  Here `candidate x` says that the
proposed content to be negated applies at `x`; it does not say that the
conventional object `x` is erased.

The central theorem is extensional: a candidate is exactly the intrinsic-
existence predicate iff it has neither an overreach witness nor an omission
witness.  A bridge to `TibetanDefinitions` packages this fit as a certified
definition.  Bridges to `DependenceModes` and `Emptiness` then state the extra
premises needed to retain conventional appearance while rejecting intrinsic
existence.  In particular, many-valued emptiness needs a no-glut bridge before
formula-level negation can be used as metalevel non-designation.

Source status (accessed 2026-09-19): this is secondary orientation only.  The
Stanford Encyclopedia of Philosophy entry “Tsongkhapa,” section 3
(https://plato.stanford.edu/entries/tsongkhapa/), and Garfield and Thakchöe,
“Identifying the Object of Negation and the Status of Conventional Truth,”
chapter 5 of *Moonshadows* (Oxford University Press, 2011), identify the paired
danger of going too far (`khyab che ba`) and not far enough (`khyab chung ba`).
No primary Tibetan passage or translation is claimed here.  `TooBroad`,
`TooNarrow`, and `Calibrated` are project-authored extensional paraphrases of
that orientation, not translations of Tsongkhapa's wording.
-/

namespace BuddhistComparativeLogic.NegandumCalibration

universe u v

abbrev Predicate (Object : Type u) := Object -> Prop

/-- The candidate reaches an object outside the intended intrinsic-existence
predicate. -/
def TooBroad {Object : Type u}
    (candidate intrinsic : Predicate Object) : Prop :=
  exists object, candidate object /\ Not (intrinsic object)

/-- The candidate omits an object to which the intended intrinsic-existence
predicate applies. -/
def TooNarrow {Object : Type u}
    (candidate intrinsic : Predicate Object) : Prop :=
  exists object, intrinsic object /\ Not (candidate object)

/-- Extensional calibration, with overreach and omission kept as separate
auditable failures. -/
def Calibrated {Object : Type u}
    (candidate intrinsic : Predicate Object) : Prop :=
  Not (TooBroad candidate intrinsic) /\
    Not (TooNarrow candidate intrinsic)

/-- Besides function and proposition extensionality, the reverse direction
uses classical double-negation elimination to turn absence of overreach and
omission witnesses into positive pointwise membership.  It does not infer the
intended intrinsic predicate from textual data. -/
theorem candidate_eq_intrinsic_iff_calibrated {Object : Type u}
    (candidate intrinsic : Predicate Object) :
    candidate = intrinsic <-> Calibrated candidate intrinsic := by
  constructor
  · intro equality
    subst candidate
    constructor
    · rintro ⟨object, intrinsicAt, notIntrinsic⟩
      exact notIntrinsic intrinsicAt
    · rintro ⟨object, intrinsicAt, notIntrinsic⟩
      exact notIntrinsic intrinsicAt
  · rintro ⟨notBroad, notNarrow⟩
    classical
    funext object
    apply propext
    constructor
    · intro candidateAt
      exact Classical.byContradiction (fun notIntrinsic =>
        notBroad ⟨object, candidateAt, notIntrinsic⟩)
    · intro intrinsicAt
      exact Classical.byContradiction (fun notCandidate =>
        notNarrow ⟨object, intrinsicAt, notCandidate⟩)

theorem calibrated_iff_pointwise {Object : Type u}
    (candidate intrinsic : Predicate Object) :
    Calibrated candidate intrinsic <->
      forall object, candidate object <-> intrinsic object := by
  rw [← candidate_eq_intrinsic_iff_calibrated]
  constructor
  · intro equality object
    rw [equality]
  · intro pointwise
    funext object
    exact propext (pointwise object)

/-! ## Conventional retention and finite boundary models -/

/-- Conventional objects are retained when the candidate content does not
apply to them. -/
def RetainsConventions {Object : Type u}
    (candidate conventional : Predicate Object) : Prop :=
  forall object, conventional object -> Not (candidate object)

/-- The substantive middle-way premise: conventional presence and intrinsic
existence have disjoint extensions. -/
def ConventionalIsNonIntrinsic {Object : Type u}
    (conventional intrinsic : Predicate Object) : Prop :=
  forall object, conventional object -> Not (intrinsic object)

theorem calibrated_candidate_retains_conventions {Object : Type u}
    (candidate intrinsic conventional : Predicate Object)
    (calibration : Calibrated candidate intrinsic)
    (separation : ConventionalIsNonIntrinsic conventional intrinsic) :
    RetainsConventions candidate conventional := by
  have equality :=
    (candidate_eq_intrinsic_iff_calibrated candidate intrinsic).mpr
      calibration
  intro object conventionalAt
  rw [equality]
  exact separation object conventionalAt

inductive CalibrationObject where
  | conventionalCup
  | projectedIntrinsic
  deriving DecidableEq, Repr

def sampleIntrinsic : Predicate CalibrationObject
  | .conventionalCup => False
  | .projectedIntrinsic => True

def sampleConventional : Predicate CalibrationObject
  | .conventionalCup => True
  | .projectedIntrinsic => False

def universalCandidate : Predicate CalibrationObject := fun _ => True

def emptyCandidate : Predicate CalibrationObject := fun _ => False

/-- The universal candidate captures a conventional cup outside the intended
intrinsic predicate and therefore fails conventional retention. -/
theorem universal_candidate_is_too_broad :
    TooBroad universalCandidate sampleIntrinsic /\
      Not (RetainsConventions universalCandidate sampleConventional) /\
      Not (Calibrated universalCandidate sampleIntrinsic) := by
  have broad : TooBroad universalCandidate sampleIntrinsic :=
    ⟨.conventionalCup, trivial, by simp [sampleIntrinsic]⟩
  refine ⟨broad, ?_, ?_⟩
  · intro retention
    exact retention .conventionalCup (by simp [sampleConventional]) trivial
  · intro calibration
    exact calibration.1 broad

/-- The empty candidate leaves the projected intrinsic content untouched and
is consequently too narrow. -/
theorem empty_candidate_is_too_narrow :
    TooNarrow emptyCandidate sampleIntrinsic /\
      sampleIntrinsic .projectedIntrinsic /\
      Not (emptyCandidate .projectedIntrinsic) /\
      Not (Calibrated emptyCandidate sampleIntrinsic) := by
  have narrow : TooNarrow emptyCandidate sampleIntrinsic :=
    ⟨.projectedIntrinsic, trivial, by simp [emptyCandidate]⟩
  exact ⟨narrow, trivial, by simp [emptyCandidate],
    fun calibration => calibration.2 narrow⟩

theorem finite_calibrated_candidate_retains_the_cup :
    Calibrated sampleIntrinsic sampleIntrinsic /\
      RetainsConventions sampleIntrinsic sampleConventional := by
  constructor
  · exact (candidate_eq_intrinsic_iff_calibrated _ _).mp rfl
  · apply calibrated_candidate_retains_conventions
      sampleIntrinsic sampleIntrinsic sampleConventional
    · exact (candidate_eq_intrinsic_iff_calibrated _ _).mp rfl
    · intro object conventionalAt
      cases object <;> simp_all [sampleConventional, sampleIntrinsic]

/-! ## Adapter to Tibetan definition certificates -/

/-- A minimal permissive standard.  It licenses this formal requirement but
makes no claim about historical or pedagogical admissibility. -/
def permissiveStandard :
    BuddhistComparativeLogic.TibetanDefinitions.DefinitionStandard Unit where
  licensed := fun _ => True

/-- The intrinsic predicate is represented by one required feature; the
candidate is the proposed definiendum. -/
def negandumTriad {Object : Type u}
    (intrinsic candidate : Predicate Object) (basis : Object) :
    BuddhistComparativeLogic.TibetanDefinitions.DefinitionTriad Object Unit where
  hasFeatures := fun object _ => intrinsic object
  requires := fun _ => True
  definiendum := candidate
  basis := basis

theorem negandumTriad_condition_iff {Object : Type u}
    (intrinsic candidate : Predicate Object) (basis object : Object) :
    (negandumTriad intrinsic candidate basis).definingCondition object <->
      intrinsic object := by
  constructor
  · intro condition
    exact condition () trivial
  · intro intrinsicAt _ _
    exact intrinsicAt

theorem calibrated_iff_definition_coextensive {Object : Type u}
    (intrinsic candidate : Predicate Object) (basis : Object) :
    Calibrated candidate intrinsic <->
      (negandumTriad intrinsic candidate basis).Coextensive := by
  constructor
  · intro calibration object
    have pointwise :=
      (calibrated_iff_pointwise candidate intrinsic).mp calibration object
    exact pointwise.trans
      (negandumTriad_condition_iff intrinsic candidate basis object).symm
  · intro coextensive
    apply (calibrated_iff_pointwise candidate intrinsic).mpr
    intro object
    exact (coextensive object).trans
      (negandumTriad_condition_iff intrinsic candidate basis object)

/-- A calibrated candidate with a genuine intrinsic basis becomes an actual
`TibetanDefinitions.DefinitionCertificate`; its three obligations remain
visible in that shared interface. -/
theorem toDefinitionCertificate {Object : Type u}
    (intrinsic candidate : Predicate Object) (basis : Object)
    (calibration : Calibrated candidate intrinsic)
    (basisIntrinsic : intrinsic basis) :
    BuddhistComparativeLogic.TibetanDefinitions.DefinitionCertificate
      permissiveStandard (negandumTriad intrinsic candidate basis) where
  coextensive :=
    (calibrated_iff_definition_coextensive intrinsic candidate basis).mp
      calibration
  basisFits := by
    intro _ _
    exact basisIntrinsic
  licensed := trivial

theorem definitionCertificate_recovers_calibration {Object : Type u}
    (intrinsic candidate : Predicate Object) (basis : Object)
    (certificate : BuddhistComparativeLogic.TibetanDefinitions.DefinitionCertificate
      permissiveStandard (negandumTriad intrinsic candidate basis)) :
    Calibrated candidate intrinsic :=
  (calibrated_iff_definition_coextensive intrinsic candidate basis).mpr
    certificate.coextensive

theorem finite_calibration_has_definition_certificate :
    Nonempty (BuddhistComparativeLogic.TibetanDefinitions.DefinitionCertificate
      permissiveStandard
        (negandumTriad sampleIntrinsic sampleIntrinsic
          CalibrationObject.projectedIntrinsic)) := by
  exact ⟨toDefinitionCertificate sampleIntrinsic sampleIntrinsic
    .projectedIntrinsic
    ((candidate_eq_intrinsic_iff_calibrated _ _).mp rfl) trivial⟩

/-! ## Adapter to mode-indexed dependence -/

/-- In a dependence model, primitive `own` supplies the intended intrinsic-
existence predicate; this is an explicit interpretation, not a definitional
identification made by the dependence module. -/
def CalibratedToOwn {Object : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model Object)
    (candidate : Predicate Object) : Prop :=
  Calibrated candidate model.own

theorem mode_dependence_refutes_calibrated_candidate {Object : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model Object)
    (candidate : Predicate Object)
    (calibration : CalibratedToOwn model candidate)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode)
    {source object : Object} (edge : model.DependsAt mode source object) :
    Not (candidate object) := by
  have equality :=
    (candidate_eq_intrinsic_iff_calibrated candidate model.own).mpr
      calibration
  rw [equality]
  exact model.empty_of_mode_dependency mode invariant edge

/-- Coverage plus calibration retains every conventional item in the supplied
domain.  Coverage is not inferred from calibration. -/
theorem covered_dependence_retains_conventions {Object : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model Object)
    (candidate conventional : Predicate Object)
    (calibration : CalibratedToOwn model candidate)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode)
    (coverage : forall object, conventional object ->
      exists source, model.DependsAt mode source object) :
    RetainsConventions candidate conventional := by
  intro object conventionalAt
  obtain ⟨source, edge⟩ := coverage object conventionalAt
  exact mode_dependence_refutes_calibrated_candidate
    model candidate calibration mode invariant edge

theorem dependent_appearance_is_retained {Object : Type u}
    (model : BuddhistComparativeLogic.DependenceModes.Model Object)
    (candidate appears : Predicate Object)
    (calibration : CalibratedToOwn model candidate)
    (mode : BuddhistComparativeLogic.DependenceModes.Mode)
    (invariant : model.InvariantOwnAt mode)
    {source object : Object} (edge : model.DependsAt mode source object)
    (appearance : appears object) :
    appears object /\ Not (candidate object) :=
  ⟨appearance, mode_dependence_refutes_calibrated_candidate
    model candidate calibration mode invariant edge⟩

/-! ## Adapter to the sutra's many-valued emptiness model -/

/-- Designated own-being is the intended intrinsic content in this adapter. -/
def SutraIntrinsic {Value : Type v} (model : BuddhistComparativeLogic.Emptiness Value) :
    Predicate BuddhistComparativeLogic.Dharma :=
  fun dharma => model.logic.designated (model.sv dharma)

/-- Formula-level emptiness excludes designated own-being only under this
additional no-glut condition. -/
def MetaExclusive {Value : Type v} (model : BuddhistComparativeLogic.Emptiness Value) :
    Prop :=
  forall dharma, model.emptyOf dharma ->
    Not (SutraIntrinsic model dharma)

theorem calibrated_emptiness_retains_conventional_appearance
    {Value : Type v} (model : BuddhistComparativeLogic.Emptiness Value)
    (candidate : Predicate BuddhistComparativeLogic.Dharma)
    (calibration : Calibrated candidate (SutraIntrinsic model))
    (exclusive : MetaExclusive model) (dharma : BuddhistComparativeLogic.Dharma) :
    model.logic.designated (model.appears dharma) /\
      Not (candidate dharma) := by
  have equality :=
    (candidate_eq_intrinsic_iff_calibrated candidate
      (SutraIntrinsic model)).mpr calibration
  constructor
  · exact model.samvrti dharma
  · rw [equality]
    exact exclusive dharma (model.sarva_dharma_sunya dharma)

theorem classicalEmptiness_is_meta_exclusive :
    MetaExclusive BuddhistComparativeLogic.classicalEmptiness := by
  intro dharma _
  simp [SutraIntrinsic, BuddhistComparativeLogic.classicalEmptiness,
    BuddhistComparativeLogic.mvClassical]

theorem classical_calibration_retains_every_appearance
    (dharma : BuddhistComparativeLogic.Dharma) :
    BuddhistComparativeLogic.classicalEmptiness.logic.designated
        (BuddhistComparativeLogic.classicalEmptiness.appears dharma) /\
      Not (SutraIntrinsic BuddhistComparativeLogic.classicalEmptiness dharma) := by
  apply calibrated_emptiness_retains_conventional_appearance
    BuddhistComparativeLogic.classicalEmptiness
    (SutraIntrinsic BuddhistComparativeLogic.classicalEmptiness)
  · exact (candidate_eq_intrinsic_iff_calibrated _ _).mp rfl
  · exact classicalEmptiness_is_meta_exclusive

/-- The existing all-glut FDE model is an inhabited boundary case: emptiness,
own-being, and conventional appearance are all designated.  Hence the
metalevel exclusion needed above is not supplied by formula-level emptiness
alone. -/
theorem fde_glut_blocks_meta_exclusion (dharma : BuddhistComparativeLogic.Dharma) :
    BuddhistComparativeLogic.fdeAllGlutEmptiness.emptyOf dharma /\
      SutraIntrinsic BuddhistComparativeLogic.fdeAllGlutEmptiness dharma /\
      BuddhistComparativeLogic.fdeAllGlutEmptiness.logic.designated
        (BuddhistComparativeLogic.fdeAllGlutEmptiness.appears dharma) /\
      Not (MetaExclusive BuddhistComparativeLogic.fdeAllGlutEmptiness) := by
  have empty : BuddhistComparativeLogic.fdeAllGlutEmptiness.emptyOf dharma :=
    BuddhistComparativeLogic.fdeAllGlutEmptiness.sarva_dharma_sunya dharma
  have intrinsic : SutraIntrinsic BuddhistComparativeLogic.fdeAllGlutEmptiness dharma := by
    simp [SutraIntrinsic, BuddhistComparativeLogic.fdeAllGlutEmptiness,
      BuddhistComparativeLogic.mvFDE, BuddhistComparativeLogic.tr]
  refine ⟨empty, intrinsic, BuddhistComparativeLogic.fdeAllGlutEmptiness.samvrti dharma,
    ?_⟩
  intro exclusive
  exact exclusive dharma empty intrinsic

end BuddhistComparativeLogic.NegandumCalibration
