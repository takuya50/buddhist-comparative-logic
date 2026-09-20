/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Grammar.PaniniDerivation

/-!
# Analysis-relative existence in the Abhidharmakośabhāṣya

This module reconstructs the analytical contrast discussed around
*Abhidharmakośabhāṣya* VI.4.  Physical destruction and mental analysis are
tagged separately.  A framework also keeps transformation, admissibility,
and continued recognition separate.  An object is `ParamarthaSat` here when
its recognition survives every admitted analysis; it is `SamvrtiSat` when an
admitted analysis supplies a recognition-loss witness.

These predicates are relative to an explicit analysis framework.  They are
not identified with Madhyamaka's two truths, with an invariant substance, or
with an edition-wide exegesis of Vasubandhu.  Complement equivalence is proved
only for a finite, complete inventory carrying local decision procedures.
Empty and overly coarse inventories show why analysis coverage is a
substantive premise.

Source status (accessed 2026-09-19): *Abhidharmakośabhāṣya* VI.4 and its
prose explanation are located in the GRETIL Sanskrit text at source-page
markers 333.23–334.13:
<https://gretil.sub.uni-goettingen.de/gretil/corpustei/transformations/html/sa_vasubandhu-abhidharmakozabhASya.htm>.
No source translation is reproduced.  The English labels, framework, and
finite complement audit are project-authored paraphrases and formal additions.
The `PaniniDerivation` import is used only by the final adapter to the shared
generic `FiniteRankedRewrite` carrier; it does not identify Abhidharma analysis
with Pāṇinian grammar.
-/

namespace BuddhistComparativeLogic.AbhidharmaAnalysis

universe u v

/-! ## Analysis frameworks and two classifications -/

inductive AnalysisKind where
  | physical
  | mental
  deriving DecidableEq, Repr

/-- `transform` records what an analysis produces.  `admissible` determines
which analyses count in the current framework, while `recognizes` determines
whether a transformed state is still cognized as the original object. -/
structure Framework (Object : Type u) (Analysis : Type v) where
  kind : Analysis -> AnalysisKind
  transform : Analysis -> Object -> Object
  admissible : Analysis -> Prop
  recognizes : Object -> Object -> Prop

namespace Framework

variable {Object : Type u} {Analysis : Type v}
  (framework : Framework Object Analysis)

def RecognitionSurvives (object : Object) (analysis : Analysis) : Prop :=
  framework.recognizes object (framework.transform analysis object)

/-- Recognition survives every analysis admitted by the stated framework. -/
def ParamarthaSat (object : Object) : Prop :=
  forall analysis, framework.admissible analysis ->
    framework.RecognitionSurvives object analysis

/-- Conventional existence is witnessed by one admitted analysis under which
recognition of the original object is lost. -/
def SamvrtiSat (object : Object) : Prop :=
  exists analysis, framework.admissible analysis /\
    Not (framework.RecognitionSurvives object analysis)

theorem samvrti_excludes_paramartha {object : Object}
    (conventional : framework.SamvrtiSat object) :
    Not (framework.ParamarthaSat object) := by
  rintro ultimate
  obtain ⟨analysis, admissible, lost⟩ := conventional
  exact lost (ultimate analysis admissible)

end Framework

/-! ## Content-bearing certificates -/

/-- A stable-result certificate derives universal survival from a common
recognized result.  It does not contain `ParamarthaSat` as a field. -/
structure StableResultCertificate {Object : Type u} {Analysis : Type v}
    (framework : Framework Object Analysis) (object : Object) where
  result : Object
  recognized : framework.recognizes object result
  sameResult : forall analysis, framework.admissible analysis ->
    framework.transform analysis object = result

namespace StableResultCertificate

variable {Object : Type u} {Analysis : Type v}
  {framework : Framework Object Analysis} {object : Object}

theorem sound
    (certificate : StableResultCertificate framework object) :
    framework.ParamarthaSat object := by
  intro analysis admissible
  unfold Framework.RecognitionSurvives
  rw [certificate.sameResult analysis admissible]
  exact certificate.recognized

end StableResultCertificate

/-- A dissolution certificate records a concrete transformation and failure
of recognition.  `SamvrtiSat` is derived from those data. -/
structure DissolutionCertificate {Object : Type u} {Analysis : Type v}
    (framework : Framework Object Analysis) (object : Object) where
  analysis : Analysis
  result : Object
  admitted : framework.admissible analysis
  transformed : framework.transform analysis object = result
  unrecognized : Not (framework.recognizes object result)

namespace DissolutionCertificate

variable {Object : Type u} {Analysis : Type v}
  {framework : Framework Object Analysis} {object : Object}

theorem sound
    (certificate : DissolutionCertificate framework object) :
    framework.SamvrtiSat object := by
  refine ⟨certificate.analysis, certificate.admitted, ?_⟩
  unfold Framework.RecognitionSurvives
  rw [certificate.transformed]
  exact certificate.unrecognized

end DissolutionCertificate

/-! ## Finite coverage and decidable complementarity -/

/-- A finite inventory covers all and only admitted analyses and supplies a
decision procedure for survival at the object under audit. -/
structure FiniteCoverage {Object : Type u} {Analysis : Type v}
    (framework : Framework Object Analysis) (object : Object) where
  inventory : List Analysis
  admissibleIffMem : forall analysis,
    framework.admissible analysis <-> analysis ∈ inventory
  survivalDecidable : forall analysis, analysis ∈ inventory ->
    Decidable (framework.RecognitionSurvives object analysis)

namespace FiniteCoverage

variable {Object : Type u} {Analysis : Type v}
  {framework : Framework Object Analysis} {object : Object}

/-- A finite family of decidable survival claims either contains a concrete
failure or verifies every listed claim. -/
private theorem list_failure_or_all
    (survives : Analysis -> Prop) (inventory : List Analysis)
    (decides : forall analysis, analysis ∈ inventory ->
      Decidable (survives analysis)) :
    (exists analysis, analysis ∈ inventory /\ Not (survives analysis)) \/
      (forall analysis, analysis ∈ inventory -> survives analysis) := by
  induction inventory with
  | nil =>
      exact Or.inr (by
        intro analysis member
        simp at member)
  | cons head tail ih =>
      have headMember : head ∈ head :: tail := by simp
      cases decides head headMember with
      | isFalse headFails =>
          exact Or.inl ⟨head, headMember, headFails⟩
      | isTrue headSurvives =>
          have tailDecides : forall analysis, analysis ∈ tail ->
              Decidable (survives analysis) := by
            intro analysis member
            exact decides analysis (by simp [member])
          cases ih tailDecides with
          | inl failure =>
              obtain ⟨analysis, member, lost⟩ := failure
              exact Or.inl ⟨analysis, by simp [member], lost⟩
          | inr allTail =>
              apply Or.inr
              intro analysis member
              simp only [List.mem_cons] at member
              cases member with
              | inl equality =>
                  subst analysis
                  exact headSurvives
              | inr inTail => exact allTail analysis inTail

/-- Finite coverage plus local decisions gives an exhaustive classification.
This is the constructive engine behind the complement theorems. -/
theorem classification_complete
    (coverage : FiniteCoverage framework object) :
    framework.SamvrtiSat object \/
      framework.ParamarthaSat object := by
  have audit := list_failure_or_all
    (framework.RecognitionSurvives object) coverage.inventory
    coverage.survivalDecidable
  cases audit with
  | inl failure =>
      obtain ⟨analysis, member, lost⟩ := failure
      exact Or.inl ⟨analysis,
        (coverage.admissibleIffMem analysis).mpr member, lost⟩
  | inr allSurvive =>
      apply Or.inr
      intro analysis admitted
      exact allSurvive analysis
        ((coverage.admissibleIffMem analysis).mp admitted)

/-- Completeness and local decidability turn failure of universal survival
into an explicit admitted counteranalysis. -/
theorem samvrti_iff_not_paramartha
    (coverage : FiniteCoverage framework object) :
    framework.SamvrtiSat object <->
      Not (framework.ParamarthaSat object) := by
  constructor
  · exact framework.samvrti_excludes_paramartha
  · intro notUltimate
    cases coverage.classification_complete with
    | inl conventional => exact conventional
    | inr ultimate => exact False.elim (notUltimate ultimate)

theorem paramartha_iff_not_samvrti
    (coverage : FiniteCoverage framework object) :
    framework.ParamarthaSat object <->
      Not (framework.SamvrtiSat object) := by
  constructor
  · intro ultimate conventional
    exact framework.samvrti_excludes_paramartha conventional ultimate
  · intro noConventional
    cases coverage.classification_complete with
    | inl conventional => exact False.elim (noConventional conventional)
    | inr ultimate => exact ultimate

end FiniteCoverage

/-! ## Pot, water, and a stable quality: a finite audit -/

inductive SampleObject where
  | pot
  | shards
  | water
  | separatedQualities
  | colorDharma
  deriving DecidableEq, Repr

inductive SampleAnalysis where
  | breakPot
  | mentallySeparateWater
  | inspect
  deriving DecidableEq, Repr

open SampleObject SampleAnalysis

def sampleFramework : Framework SampleObject SampleAnalysis where
  kind
    | .breakPot => .physical
    | .mentallySeparateWater => .mental
    | .inspect => .mental
  transform
    | .breakPot, .pot => .shards
    | .mentallySeparateWater, .water => .separatedQualities
    | _, object => object
  admissible := fun _ => True
  recognizes original result :=
    match original, result with
    | .pot, .pot => True
    | .water, .water => True
    | .colorDharma, .colorDharma => True
    | .shards, .shards => True
    | .separatedQualities, .separatedQualities => True
    | _, _ => False

def potDissolution : DissolutionCertificate sampleFramework .pot where
  analysis := .breakPot
  result := .shards
  admitted := trivial
  transformed := rfl
  unrecognized := fun impossible => impossible

def waterDissolution : DissolutionCertificate sampleFramework .water where
  analysis := .mentallySeparateWater
  result := .separatedQualities
  admitted := trivial
  transformed := rfl
  unrecognized := fun impossible => impossible

def colorStability :
    StableResultCertificate sampleFramework .colorDharma where
  result := .colorDharma
  recognized := trivial
  sameResult := by
    intro analysis _
    cases analysis <;> rfl

theorem finite_examples_are_classified :
    sampleFramework.SamvrtiSat .pot /\
      sampleFramework.SamvrtiSat .water /\
      sampleFramework.ParamarthaSat .colorDharma :=
  ⟨potDissolution.sound, waterDissolution.sound, colorStability.sound⟩

def sampleCoverage (object : SampleObject) :
    FiniteCoverage sampleFramework object where
  inventory := [.breakPot, .mentallySeparateWater, .inspect]
  admissibleIffMem := by
    intro analysis
    cases analysis <;> simp [sampleFramework]
  survivalDecidable := by
    intro analysis _
    cases object <;> cases analysis <;> simp [Framework.RecognitionSurvives,
      sampleFramework] <;> infer_instance

theorem sample_complement_is_audited (object : SampleObject) :
    sampleFramework.SamvrtiSat object <->
      Not (sampleFramework.ParamarthaSat object) :=
  (sampleCoverage object).samvrti_iff_not_paramartha

/-! ## Coverage countermodels -/

/-- With no admitted analyses, universal survival is vacuous even though the
recognition relation is everywhere false. -/
def emptyFramework : Framework Unit Unit where
  kind _ := .mental
  transform _ _ := ()
  admissible _ := False
  recognizes _ _ := False

theorem empty_inventory_is_vacuously_paramartha :
    emptyFramework.ParamarthaSat () /\
      Not (emptyFramework.SamvrtiSat ()) := by
  constructor
  · intro _ admitted
    exact False.elim admitted
  · rintro ⟨_, admitted, _⟩
    exact admitted

/-- A coarse inventory admits only inspection.  It labels the pot ultimate,
whereas the richer sample framework has the physical destruction witness.
This is an inhabited model of undercoverage, not a claim that a pot is
ultimately real. -/
def coarseFramework : Framework SampleObject SampleAnalysis :=
  { sampleFramework with
    admissible := fun analysis => analysis = .inspect }

theorem coarse_analysis_misclassifies_the_pot :
    coarseFramework.ParamarthaSat .pot /\
      Not (coarseFramework.SamvrtiSat .pot) /\
      sampleFramework.SamvrtiSat .pot := by
  refine ⟨?_, ?_, potDissolution.sound⟩
  · intro analysis admitted
    subst analysis
    exact trivial
  · rintro ⟨analysis, admitted, lost⟩
    subst analysis
    exact lost trivial

/-! ## Adapter to the shared ranked-rewrite carrier -/

/-- The sample transformations can be executed by the repository's generic
finite ranked-rewrite interface.  This reuses only its termination carrier;
it does not identify Abhidharma analysis with Pāṇinian grammar. -/
def sampleRewrite :
    BuddhistComparativeLogic.PaniniDerivation.FiniteRankedRewrite
      SampleObject SampleAnalysis where
  applies analysis object :=
    match analysis, object with
    | .breakPot, .pot => true
    | .mentallySeparateWater, .water => true
    | _, _ => false
  result := sampleFramework.transform
  priority
    | .breakPot => 1
    | .mentallySeparateWater => 1
    | .inspect => 0
  rank
    | .pot => 1
    | .water => 1
    | .shards => 0
    | .separatedQualities => 0
    | .colorDharma => 0
  rules := [.breakPot, .mentallySeparateWater, .inspect]
  rulesComplete := by
    intro analysis
    cases analysis <;> decide
  rulesNodup := by decide
  decreases := by
    intro analysis object applies
    cases analysis <;> cases object <;> simp_all [sampleFramework]

theorem physical_analysis_is_a_ranked_raw_step :
    sampleRewrite.RawStep .pot .shards := by
  exact ⟨.breakPot, rfl, rfl⟩

theorem mental_analysis_is_a_ranked_raw_step :
    sampleRewrite.RawStep .water .separatedQualities := by
  exact ⟨.mentallySeparateWater, rfl, rfl⟩

theorem ranked_steps_correspond_to_recognition_loss :
    sampleRewrite.RawStep .pot .shards /\
      Not (sampleFramework.recognizes .pot .shards) /\
      sampleRewrite.RawStep .water .separatedQualities /\
      Not (sampleFramework.recognizes .water .separatedQualities) :=
  ⟨physical_analysis_is_a_ranked_raw_step,
    (fun impossible => impossible), mental_analysis_is_a_ranked_raw_step,
    (fun impossible => impossible)⟩

end BuddhistComparativeLogic.AbhidharmaAnalysis
