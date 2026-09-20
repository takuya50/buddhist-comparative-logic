/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.Definitions
import BuddhistComparativeLogic.Comparative.Mimamsa.MimamsaEpistemology
import BuddhistComparativeLogic.Buddhist.HeartSutra.PremiseCertificates

/-!
# A finite definition audit motivated by Sriharsa

This module isolates four checkable defects often useful when reconstructing
the definition criticism in Sriharsa's *Khandanakhandakhadya*: a definition
may omit a target case, include a non-target case, depend directly and
mutually on another definition, or classify relevantly alike cases
non-uniformly.  The model is a modern finite audit, not an edition of the
Sanskrit work and not a claim that these four tests exhaust Sriharsa's
dialectic.  In particular, the dependency check detects reciprocal edges,
not longer directed cycles.

The executable report retains the first witness to every defect.  Completeness
depends on the explicit `complete` proofs for the finite object and rule
lists.  The epistemic examples then separate a cognition that happens to be
true from reliability across relevant alternatives and from the conjunction
called knowledge here.

Historical orientation (sources accessed 2026-09-19):

* Ganganatha Jha, trans., *The Sweets of Refutation: An English Translation
  of the Khandanakhandakhadya of Shri-Harsha* (Allahabad, 1913), chapter I,
  section 14, paragraphs 257-259 (translation pages 138-140; the translation
  records source-edition pages 229-232), gives the chance-correct five-shell
  answer and mist-for-smoke inference.  A scan was checked at
  https://archive.org/details/khandana-khanda-khadya.
* Nilanjan Das, "Sriharsa," *Stanford Encyclopedia of Philosophy*, sections
  1.2 and 2.1-2.3, maps extensional adequacy, non-circularity, uniformity, and
  epistemic-luck objections to the *Khandanakhandakhadya*.  Its locators
  include KKh 207-208 (chance-correct awareness), 211 and 213 (mist and
  horns), 230 (the uniformity discussion), and 238 (circularity); `KKh`
  denotes the 2010 reprint of Swami Yogindrananda's 1979 edition:
  https://plato.stanford.edu/archives/fall2022/entries/sriharsa/.

The mapping remains partial.  `UnderextendedAt` and `OverextendedAt` render
the modern extension tests used to explain the first adequacy criterion;
only overextension and the chance-correct knowledge example have the precise
KKh locators above.  `MutualDependencyAt` checks a direct reciprocal pair and
is narrower than the direct-or-indirect circularity criterion.  `NonuniformAt`
is motivated by `anugama`, but its Boolean `sameProfile` relation is supplied
by the formal model and is not translated from KKh 230.  The two tracking
models give a modern relevant-alternatives reconstruction of accidental truth:
`luckyShell` changes the five-shell guessing case into a jewel/empty-shell
model, and `mistFire` abstracts the mist-for-smoke example.  The English prose
therefore paraphrases the cited translations and scholarship rather than
claiming a new Sanskrit translation or a complete passage-by-predicate map.
-/

namespace BuddhistComparativeLogic.Sriharsa

universe u v

/-! ## Reusable finite witness search -/

/-- Return the first list member on which a Boolean test succeeds. -/
def firstHit (domain : List α) (test : α -> Bool) : Option α :=
  match domain with
  | [] => none
  | object :: rest =>
      if test object then some object else firstHit rest test

private theorem firstHit_some_sound
    {domain : List α} {test : α -> Bool} {object : α}
    (found : firstHit domain test = some object) :
    test object = true /\ object ∈ domain := by
  induction domain with
  | nil => simp [firstHit] at found
  | cons head tail ih =>
      cases headResult : test head with
      | false =>
          have tailFound : firstHit tail test = some object := by
            simpa [firstHit, headResult] using found
          have sound := ih tailFound
          exact ⟨sound.1, by simp [sound.2]⟩
      | true =>
          have same : head = object := by
            simpa [firstHit, headResult] using found
          subst object
          exact ⟨headResult, by simp⟩

private theorem firstHit_none_iff (domain : List α) (test : α -> Bool) :
    firstHit domain test = none <->
      ∀ object ∈ domain, test object = false := by
  induction domain with
  | nil => simp [firstHit]
  | cons head tail ih =>
      cases headResult : test head <;>
        simp [firstHit, headResult, ih]

/-- Search a finite rectangle in row-major order and retain both coordinates. -/
def firstPair (rows : List α) (columns : List β)
    (test : α -> β -> Bool) : Option (α × β) :=
  match rows with
  | [] => none
  | row :: rest =>
      match firstHit columns (test row) with
      | some column => some (row, column)
      | none => firstPair rest columns test

private theorem firstPair_some_sound
    {rows : List α} {columns : List β} {test : α -> β -> Bool}
    {left : α} {right : β}
    (found : firstPair rows columns test = some (left, right)) :
    test left right = true /\ left ∈ rows /\ right ∈ columns := by
  induction rows with
  | nil => simp [firstPair] at found
  | cons head tail ih =>
      cases rowResult : firstHit columns (test head) with
      | none =>
          have tailFound :
              firstPair tail columns test = some (left, right) := by
            simpa [firstPair, rowResult] using found
          obtain ⟨hit, inTail, inColumns⟩ := ih tailFound
          exact ⟨hit, by simp [inTail], inColumns⟩
      | some column =>
          have same : (head, column) = (left, right) := by
            simpa [firstPair, rowResult] using found
          cases same
          have sound := firstHit_some_sound rowResult
          exact ⟨sound.1, by simp, sound.2⟩

private theorem firstPair_none_iff (rows : List α) (columns : List β)
    (test : α -> β -> Bool) :
    firstPair rows columns test = none <->
      ∀ left ∈ rows, ∀ right ∈ columns,
        test left right = false := by
  induction rows with
  | nil => simp [firstPair]
  | cons head tail ih =>
      cases rowResult : firstHit columns (test head) with
      | none =>
          constructor
          · intro absent left inRows right inColumns
            have tailAbsent : firstPair tail columns test = none := by
              simpa [firstPair, rowResult] using absent
            rcases List.mem_cons.mp inRows with same | inTail
            · subst left
              exact (firstHit_none_iff columns (test head)).mp rowResult
                right inColumns
            · exact (ih.mp tailAbsent) left inTail right inColumns
          · intro misses
            have tailAbsent : firstPair tail columns test = none :=
              ih.mpr (fun left inTail right inColumns =>
                misses left (by simp [inTail]) right inColumns)
            simp [firstPair, rowResult, tailAbsent]
      | some column =>
          constructor
          · intro absent
            simp [firstPair, rowResult] at absent
          · intro misses
            have sound := firstHit_some_sound rowResult
            have failure := misses head (by simp) column sound.2
            rw [sound.1] at failure
            contradiction

def boolDifferent (left right : Bool) : Bool :=
  (left && !right) || (!left && right)

theorem boolDifferent_eq_true_iff (left right : Bool) :
    boolDifferent left right = true <-> left ≠ right := by
  cases left <;> cases right <;> decide

/-! ## Definition audits and their proof obligations -/

/-- A definition candidate, its target, and two additional finite checks.
`sameProfile` records which objects the chosen reconstruction treats as
relevantly alike.  `dependsOn` records definitional, rather than causal,
dependence between candidate rules. -/
structure DefinitionAudit (Object : Type u) (Rule : Type v) where
  objects : List Object
  objectsComplete : forall object, object ∈ objects
  objectsNodup : objects.Nodup
  rules : List Rule
  rulesComplete : forall rule, rule ∈ rules
  rulesNodup : rules.Nodup
  candidate : Object -> Bool
  target : Object -> Bool
  sameProfile : Object -> Object -> Bool
  dependsOn : Rule -> Rule -> Bool

namespace DefinitionAudit

variable {Object : Type u} {Rule : Type v}
    (audit : DefinitionAudit Object Rule)

def UnderextendedAt (object : Object) : Prop :=
  audit.target object = true /\ audit.candidate object = false

def OverextendedAt (object : Object) : Prop :=
  audit.candidate object = true /\ audit.target object = false

def MutualDependencyAt (left right : Rule) : Prop :=
  audit.dependsOn left right = true /\
    audit.dependsOn right left = true

def NonuniformAt (left right : Object) : Prop :=
  audit.sameProfile left right = true /\
    audit.candidate left ≠ audit.candidate right

def firstUnderextension : Option Object :=
  firstHit audit.objects fun object =>
    audit.target object && !audit.candidate object

def firstOverextension : Option Object :=
  firstHit audit.objects fun object =>
    audit.candidate object && !audit.target object

def firstMutualDependencyPair : Option (Rule × Rule) :=
  firstPair audit.rules audit.rules fun left right =>
    audit.dependsOn left right && audit.dependsOn right left

def firstNonuniformPair : Option (Object × Object) :=
  firstPair audit.objects audit.objects fun left right =>
    audit.sameProfile left right &&
      boolDifferent (audit.candidate left) (audit.candidate right)

/-- The executable result retains one counterexample for each failed check. -/
structure DefectReport (Object : Type u) (Rule : Type v) where
  underextension : Option Object
  overextension : Option Object
  mutualDependency : Option (Rule × Rule)
  nonuniform : Option (Object × Object)
  deriving Repr

def report : DefectReport Object Rule where
  underextension := audit.firstUnderextension
  overextension := audit.firstOverextension
  mutualDependency := audit.firstMutualDependencyPair
  nonuniform := audit.firstNonuniformPair

def DefectReport.Clean (result : DefectReport Object Rule) : Prop :=
  result.underextension = none /\
    result.overextension = none /\
    result.mutualDependency = none /\
    result.nonuniform = none

theorem firstUnderextension_some_sound {object : Object}
    (found : audit.firstUnderextension = some object) :
    audit.UnderextendedAt object := by
  have sound := firstHit_some_sound found
  simpa [UnderextendedAt] using sound.1

theorem firstOverextension_some_sound {object : Object}
    (found : audit.firstOverextension = some object) :
    audit.OverextendedAt object := by
  have sound := firstHit_some_sound found
  simpa [OverextendedAt] using sound.1

theorem firstMutualDependencyPair_some_sound {left right : Rule}
    (found : audit.firstMutualDependencyPair = some (left, right)) :
    audit.MutualDependencyAt left right := by
  have sound := firstPair_some_sound found
  simpa [MutualDependencyAt] using sound.1

theorem firstNonuniformPair_some_sound {left right : Object}
    (found : audit.firstNonuniformPair = some (left, right)) :
    audit.NonuniformAt left right := by
  have sound := firstPair_some_sound found
  simpa [NonuniformAt, boolDifferent_eq_true_iff] using sound.1

def TargetSubsetCandidate : Prop :=
  forall object, audit.target object = true ->
    audit.candidate object = true

def CandidateSubsetTarget : Prop :=
  forall object, audit.candidate object = true ->
    audit.target object = true

def NoMutualDependency : Prop :=
  forall left right, audit.dependsOn left right = true ->
    audit.dependsOn right left = false

def Uniform : Prop :=
  forall left right, audit.sameProfile left right = true ->
    audit.candidate left = audit.candidate right

def ExtensionallyExact : Prop :=
  audit.TargetSubsetCandidate /\ audit.CandidateSubsetTarget

def PassesStatedChecks : Prop :=
  audit.ExtensionallyExact /\ audit.NoMutualDependency /\ audit.Uniform

theorem firstUnderextension_none_iff :
    audit.firstUnderextension = none <-> audit.TargetSubsetCandidate := by
  rw [firstUnderextension, firstHit_none_iff]
  constructor
  · intro misses object target
    have check := misses object (audit.objectsComplete object)
    cases candidate : audit.candidate object <;>
      simp_all
  · intro included object _inDomain
    cases target : audit.target object <;>
      cases candidate : audit.candidate object <;>
        simp_all [TargetSubsetCandidate]

theorem firstOverextension_none_iff :
    audit.firstOverextension = none <-> audit.CandidateSubsetTarget := by
  rw [firstOverextension, firstHit_none_iff]
  constructor
  · intro misses object candidate
    have check := misses object (audit.objectsComplete object)
    cases target : audit.target object <;>
      simp_all
  · intro included object _inDomain
    cases candidate : audit.candidate object <;>
      cases target : audit.target object <;>
        simp_all [CandidateSubsetTarget]

theorem firstMutualDependencyPair_none_iff :
    audit.firstMutualDependencyPair = none <->
      audit.NoMutualDependency := by
  rw [firstMutualDependencyPair, firstPair_none_iff]
  constructor
  · intro misses left right dependency
    have check := misses left (audit.rulesComplete left)
      right (audit.rulesComplete right)
    cases reverse : audit.dependsOn right left <;>
      simp_all
  · intro acyclic left _leftIn right _rightIn
    cases dependency : audit.dependsOn left right <;>
      cases reverse : audit.dependsOn right left <;>
        simp_all [NoMutualDependency]

theorem firstNonuniformPair_none_iff :
    audit.firstNonuniformPair = none <-> audit.Uniform := by
  rw [firstNonuniformPair, firstPair_none_iff]
  constructor
  · intro misses left right sameProfile
    have check := misses left (audit.objectsComplete left)
      right (audit.objectsComplete right)
    cases leftValue : audit.candidate left <;>
      cases rightValue : audit.candidate right <;>
        simp_all [boolDifferent]
  · intro uniform left _leftIn right _rightIn
    cases profile : audit.sameProfile left right <;>
      cases leftValue : audit.candidate left <;>
        cases rightValue : audit.candidate right <;>
          simp_all [boolDifferent]
    · exact False.elim (Bool.noConfusion
        (uniform left right profile |>.trans rightValue |>.symm.trans leftValue))
    · exact False.elim (Bool.noConfusion
        (uniform left right profile |>.trans rightValue |>.symm.trans leftValue))

/-- Soundness and completeness of the whole executable report.  The reverse
direction uses the supplied completeness proofs, so it applies to every
object and rule of the stated types, not just the elements reached by an
unjustified sample. -/
theorem report_clean_iff_passes_stated_checks :
    audit.report.Clean <-> audit.PassesStatedChecks := by
  rw [DefectReport.Clean, report,
    audit.firstUnderextension_none_iff,
    audit.firstOverextension_none_iff,
    audit.firstMutualDependencyPair_none_iff,
    audit.firstNonuniformPair_none_iff]
  constructor
  · rintro ⟨targetIncluded, candidateIncluded, acyclic, uniform⟩
    exact ⟨⟨targetIncluded, candidateIncluded⟩, acyclic, uniform⟩
  · rintro ⟨⟨targetIncluded, candidateIncluded⟩, acyclic, uniform⟩
    exact ⟨targetIncluded, candidateIncluded, acyclic, uniform⟩

/-! ## Bridge to the existing Tibetan definition interface -/

/-- Turn the Boolean candidate into a one-feature defining condition.  This
bridge compares only extensions; historical licensing remains a separate
field in `TibetanDefinitions.DefinitionCertificate`. -/
def asDefinitionTriad (basis : Object) :
    BuddhistComparativeLogic.TibetanDefinitions.DefinitionTriad Object Unit where
  hasFeatures object _ := audit.candidate object = true
  requires _ := True
  definiendum object := audit.target object = true
  basis := basis

theorem extensionallyExact_iff_triad_coextensive (basis : Object) :
    audit.ExtensionallyExact <->
      (audit.asDefinitionTriad basis).Coextensive := by
  constructor
  · rintro ⟨targetIncluded, candidateIncluded⟩ object
    constructor
    · intro target _feature _required
      exact targetIncluded object target
    · intro condition
      exact candidateIncluded object (condition () trivial)
  · intro coextensive
    constructor
    · intro object target
      exact (coextensive object).mp target () trivial
    · intro object candidate
      apply (coextensive object).mpr
      intro _feature _required
      exact candidate

end DefinitionAudit

/-! ## Inhabited finite reports -/

inductive Specimen where
  | canonical
  | missed
  | intruder
  deriving DecidableEq, Repr

inductive CandidateRule where
  | perception
  | inference
  deriving DecidableEq, Repr

open Specimen CandidateRule DefinitionAudit

def specimenProfile : Specimen -> Bool
  | .canonical | .missed => true
  | .intruder => false

/-- The target contains `canonical` and `missed`; the candidate instead
contains `canonical` and `intruder`.  The first two share a selected profile. -/
def defectiveAudit : DefinitionAudit Specimen CandidateRule where
  objects := [.canonical, .missed, .intruder]
  objectsComplete := by intro object; cases object <;> simp
  objectsNodup := by decide
  rules := [.perception, .inference]
  rulesComplete := by intro rule; cases rule <;> simp
  rulesNodup := by decide
  candidate
    | .canonical | .intruder => true
    | .missed => false
  target
    | .canonical | .missed => true
    | .intruder => false
  sameProfile := fun left right =>
    specimenProfile left == specimenProfile right
  dependsOn
    | .perception, .inference => true
    | .inference, .perception => true
    | _, _ => false

/-- All four defects have concrete witnesses in one finite report. -/
theorem defective_report_retains_all_witnesses :
    defectiveAudit.report.underextension = some .missed /\
      defectiveAudit.report.overextension = some .intruder /\
      defectiveAudit.report.mutualDependency =
        some (.perception, .inference) /\
      defectiveAudit.report.nonuniform = some (.canonical, .missed) /\
      defectiveAudit.UnderextendedAt .missed /\
      defectiveAudit.OverextendedAt .intruder /\
      defectiveAudit.MutualDependencyAt .perception .inference /\
      defectiveAudit.NonuniformAt .canonical .missed := by
  simp [DefinitionAudit.report, DefinitionAudit.firstUnderextension,
    DefinitionAudit.firstOverextension,
    DefinitionAudit.firstMutualDependencyPair,
    DefinitionAudit.firstNonuniformPair, firstHit, firstPair,
    defectiveAudit, specimenProfile, boolDifferent,
    DefinitionAudit.UnderextendedAt, DefinitionAudit.OverextendedAt,
    DefinitionAudit.MutualDependencyAt, DefinitionAudit.NonuniformAt]

/-- A positive candidate with exact extension, identity profiles, and one-way
grounding supplies a nonvacuous clean report. -/
def cleanAudit : DefinitionAudit Specimen CandidateRule where
  objects := [.canonical, .missed, .intruder]
  objectsComplete := by intro object; cases object <;> simp
  objectsNodup := by decide
  rules := [.perception, .inference]
  rulesComplete := by intro rule; cases rule <;> simp
  rulesNodup := by decide
  candidate
    | .canonical => true
    | _ => false
  target
    | .canonical => true
    | _ => false
  sameProfile := fun left right => left == right
  dependsOn
    | .inference, .perception => true
    | _, _ => false

theorem cleanAuditPassesStatedChecks :
    cleanAudit.PassesStatedChecks := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro object target
    cases object <;> simp_all [cleanAudit]
  · intro object candidate
    cases object <;> simp_all [cleanAudit]
  · intro left right dependency
    cases left <;> cases right <;> simp_all [cleanAudit]
  · intro left right sameProfile
    cases left <;> cases right <;> simp_all [cleanAudit]

theorem clean_report_is_nonvacuous_and_complete :
    cleanAudit.report.Clean /\
      cleanAudit.target .canonical = true /\
      cleanAudit.candidate .canonical = true /\
      cleanAudit.target .missed = false := by
  exact ⟨cleanAudit.report_clean_iff_passes_stated_checks.mpr
      cleanAuditPassesStatedChecks,
    rfl, rfl, rfl⟩

/-! ## Boundary of the direct mutual-dependency check -/

inductive ThreeCycleRule where
  | first
  | second
  | third
  deriving DecidableEq, Repr

/-- This audit contains the directed edges `first -> second -> third -> first`
but no reciprocal pair.  It makes the checker boundary explicit rather than
letting `Clean` be read as a decision procedure for arbitrary graph cycles. -/
def threeCycleAudit : DefinitionAudit Specimen ThreeCycleRule where
  objects := [.canonical, .missed, .intruder]
  objectsComplete := by intro object; cases object <;> simp
  objectsNodup := by decide
  rules := [.first, .second, .third]
  rulesComplete := by intro rule; cases rule <;> simp
  rulesNodup := by decide
  candidate
    | .canonical => true
    | _ => false
  target
    | .canonical => true
    | _ => false
  sameProfile := fun left right => left == right
  dependsOn
    | .first, .second => true
    | .second, .third => true
    | .third, .first => true
    | _, _ => false

theorem threeCycleAuditPassesStatedChecks :
    threeCycleAudit.PassesStatedChecks := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro object target
    cases object <;> simp_all [threeCycleAudit]
  · intro object candidate
    cases object <;> simp_all [threeCycleAudit]
  · intro left right dependency
    cases left <;> cases right <;> simp_all [threeCycleAudit]
  · intro left right sameProfile
    cases left <;> cases right <;> simp_all [threeCycleAudit]

/-- A three-edge dependency cycle can pass this deliberately pairwise audit.
The theorem prevents the direct reciprocal-edge test from being reported as
a general acyclicity check. -/
theorem three_step_cycle_is_outside_direct_mutual_test :
    threeCycleAudit.dependsOn .first .second = true /\
      threeCycleAudit.dependsOn .second .third = true /\
      threeCycleAudit.dependsOn .third .first = true /\
      threeCycleAudit.NoMutualDependency /\
      threeCycleAudit.report.Clean := by
  exact ⟨rfl, rfl, rfl, threeCycleAuditPassesStatedChecks.2.1,
    threeCycleAudit.report_clean_iff_passes_stated_checks.mpr
      threeCycleAuditPassesStatedChecks⟩

/-- Reuse the repository's provenance-bearing wrapper: unlike a citation
label, this certificate contains the checked theorem as its payload. -/
def cleanAuditCertificate :
    BuddhistComparativeLogic.PremiseCertificates.Certified
      cleanAudit.PassesStatedChecks :=
  BuddhistComparativeLogic.PremiseCertificates.certifyInternal
    ``BuddhistComparativeLogic.Sriharsa.cleanAuditPassesStatedChecks
      cleanAuditPassesStatedChecks

/-! ## True cognition, reliability, and epistemic luck -/

/-- Reliability is evaluated across an explicitly stated relevant-alternative
relation.  `TrueCognitionAt` describes success at one world; it does not by
definition quantify over alternatives. -/
structure TrackingModel (World : Type u) where
  claimTrue : World -> Bool
  cognitionAffirms : World -> Bool
  relevant : World -> World -> Bool

namespace TrackingModel

variable {World : Type u} (model : TrackingModel World)

def TrueCognitionAt (world : World) : Prop :=
  model.claimTrue world = true /\ model.cognitionAffirms world = true

def ReliableAt (world : World) : Prop :=
  forall alternative, model.relevant world alternative = true ->
    model.cognitionAffirms alternative = model.claimTrue alternative

def KnowledgeAt (world : World) : Prop :=
  model.TrueCognitionAt world /\ model.ReliableAt world

/-- Embed tracking into the existing Mīmāṃsā audit.  An affirmation receives
prima-facie status; failure to track a relevant alternative is represented as
a defeater.  This is an interface bridge, not an identification of theories. -/
def asMimamsaModel :
    BuddhistComparativeLogic.MimamsaEpistemology.EpistemicModel World Unit where
  generated _ world _ := model.cognitionAffirms world = true
  primaFacieValid _ world _ := model.cognitionAffirms world = true
  defeated _ world _ := ¬ model.ReliableAt world
  trueAt world _ := model.claimTrue world = true

theorem true_cognition_initially_qualified
    {world : World} (trueCognition : model.TrueCognitionAt world) :
    model.asMimamsaModel.InitiallyQualified .perception world () :=
  trueCognition.2

theorem unreliable_true_cognition_is_defeated
    {world : World} (trueCognition : model.TrueCognitionAt world)
    (unreliable : ¬ model.ReliableAt world) :
    model.asMimamsaModel.trueAt world () /\
      model.asMimamsaModel.defeated .perception world () /\
      ¬ model.KnowledgeAt world := by
  exact ⟨trueCognition.1, unreliable,
    fun knowledge => unreliable knowledge.2⟩

end TrackingModel

inductive ShellWorld where
  | jewelShell
  | emptyShell
  deriving DecidableEq, Repr

/-- The guess "this shell contains a jewel" is true at the selected shell,
but the same affirmation persists at a relevant empty shell. -/
def luckyShell : TrackingModel ShellWorld where
  claimTrue
    | .jewelShell => true
    | .emptyShell => false
  cognitionAffirms _ := true
  relevant _ _ := true

theorem lucky_shell_true_but_not_reliable_or_knowledge :
    luckyShell.TrueCognitionAt .jewelShell /\
      ¬ luckyShell.ReliableAt .jewelShell /\
      ¬ luckyShell.KnowledgeAt .jewelShell /\
      luckyShell.asMimamsaModel.InitiallyQualified
        .perception .jewelShell () /\
      luckyShell.asMimamsaModel.defeated
        .perception .jewelShell () := by
  have trueCognition : luckyShell.TrueCognitionAt .jewelShell := by
    simp [TrackingModel.TrueCognitionAt, luckyShell]
  have unreliable : ¬ luckyShell.ReliableAt .jewelShell := by
    intro reliable
    have tracking := reliable .emptyShell (by simp [luckyShell])
    simp [luckyShell] at tracking
  have status := luckyShell.unreliable_true_cognition_is_defeated
    trueCognition unreliable
  exact ⟨trueCognition, unreliable, status.2.2,
    luckyShell.true_cognition_initially_qualified trueCognition,
    status.2.1⟩

inductive MistWorld where
  | mistWithFire
  | mistWithoutFire
  | smokeWithFire
  deriving DecidableEq, Repr

/-- An appearance interpreted as smoke leads to affirmation in all three
worlds.  Fire happens to be present in the actual mist world, but the nearby
mist-without-fire world breaks tracking. -/
def mistFire : TrackingModel MistWorld where
  claimTrue
    | .mistWithFire | .smokeWithFire => true
    | .mistWithoutFire => false
  cognitionAffirms _ := true
  relevant _ _ := true

theorem mist_fire_true_result_is_not_reliable_knowledge :
    mistFire.TrueCognitionAt .mistWithFire /\
      mistFire.claimTrue .smokeWithFire = true /\
      ¬ mistFire.claimTrue .mistWithoutFire = true /\
      ¬ mistFire.ReliableAt .mistWithFire /\
      ¬ mistFire.KnowledgeAt .mistWithFire := by
  have trueCognition : mistFire.TrueCognitionAt .mistWithFire := by
    simp [TrackingModel.TrueCognitionAt, mistFire]
  have unreliable : ¬ mistFire.ReliableAt .mistWithFire := by
    intro reliable
    have tracking := reliable .mistWithoutFire (by simp [mistFire])
    simp [mistFire] at tracking
  exact ⟨trueCognition, rfl, by decide, unreliable,
    fun knowledge => unreliable knowledge.2⟩

end BuddhistComparativeLogic.Sriharsa
