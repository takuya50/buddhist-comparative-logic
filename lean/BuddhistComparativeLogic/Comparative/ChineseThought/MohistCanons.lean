/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Nyaya.Nyaya

/-!
# Kind, standard, naming, and analogical extension in the Mohist Canons

This module gives a small semantic audit inspired by the Later Mohist
discussions of `lei` (kind), `fa` (standard), names and objects, and `tui`
(extension by analogy).  It is not a transcription of the damaged received
text, and it does not identify Mohist reasoning with modern propositional
logic.  In particular, surface parallelism is represented as data about a
public expression and is kept separate from semantic relevance.

The positive result is deliberately conditional.  A standard supplies a
genuine positive example, the target must fall under the same selected kind,
the reason must apply to the target, and a relevance rule must carry reasons
to conclusions within that kind.  The resulting restricted argument is sent
through the existing Nyaya semantic-proof interface.  Finite countermodels
show that a matching verbal frame, a same-kind source, and a positive source
case do not by themselves license extension to the target.
-/

namespace BuddhistComparativeLogic.MohistCanons

open BuddhistComparativeLogic.Hetucakra

universe u v w

/-! ## Names, objects, and kinds -/

/-- A neutral name-object interface.  `kindOf` classifies objects, `designates`
records actual application of a name, and `admits` records the kinds for which
that name is licensed.  Keeping the last two fields independent makes
misapplication expressible rather than ruling it out by definition. -/
structure Naming (Object : Type u) (Name : Type v) (Kind : Type w) where
  kindOf : Object → Kind
  designates : Name → Object → Prop
  admits : Name → Kind → Prop

namespace Naming

variable {Object : Type u} {Name : Type v} {Kind : Type w}
    (M : Naming Object Name Kind)

/-- A selected name fits a selected object when its actual designation agrees
with its kind-based license.  This is one extensional audit of name-object
matching, not a claim that Later Mohist semantics reduces names to extensions. -/
def Fits (name : Name) (object : Object) : Prop :=
  M.designates name object ↔ M.admits name (M.kindOf object)

/-- Global regularity of the deliberately small naming interface. -/
def Regular : Prop := ∀ name object, M.Fits name object

theorem designates_iff_admitted_kind (regular : M.Regular)
    (name : Name) (object : Object) :
    M.designates name object ↔ M.admits name (M.kindOf object) :=
  regular name object

end Naming

/-! ## A standard and kind-bounded analogical extension -/

/-- A `fa` in this model contains a positive illustration already separated
from universal pervasion by `BuddhistComparativeLogic.Nyaya.PositiveExample`.  The extra
field records that source and target belong to the same selected kind. -/
structure Standard {Object : Type u} {Name : Type v} {Kind : Type w}
    (M : Naming Object Name Kind) (argument : Anumana Object) where
  illustration : BuddhistComparativeLogic.Nyaya.PositiveExample argument
  sameKind :
    M.kindOf illustration.witness = M.kindOf argument.paksa

/-- Restrict an argument's reason to the kind instantiated by its standard.
The conclusion predicate is unchanged. -/
def restrictToStandardKind {Object : Type u} {Name : Type v} {Kind : Type w}
    (M : Naming Object Name Kind) (argument : Anumana Object)
    (standard : Standard M argument) : Anumana Object where
  paksa := argument.paksa
  reason object :=
    argument.reason object ∧
      M.kindOf object = M.kindOf standard.illustration.witness
  sadhya := argument.sadhya

/-- A checked analogical extension.  `relevance` is semantic and kind-bounded;
it is not inferred from the public expression's shape or from the standard's
single positive illustration. -/
structure TuiLeiCertificate
    {Object : Type u} {Name : Type v} {Kind : Type w}
    (M : Naming Object Name Kind) (argument : Anumana Object) where
  standard : Standard M argument
  subjectReason : argument.reason argument.paksa
  relevance : ∀ object,
    M.kindOf object = M.kindOf standard.illustration.witness →
      argument.reason object → argument.sadhya object

namespace TuiLeiCertificate

variable {Object : Type u} {Name : Type v} {Kind : Type w}
    {M : Naming Object Name Kind} {argument : Anumana Object}

/-- Package kind-bounded extension as the existing Nyaya semantic proof.
Only the restricted argument receives global pervasion. -/
theorem toSemanticProof (certificate : TuiLeiCertificate M argument) :
    BuddhistComparativeLogic.Nyaya.SemanticProof
      (restrictToStandardKind M argument certificate.standard) where
  subjectReason := by
    exact ⟨certificate.subjectReason, certificate.standard.sameKind.symm⟩
  pervasion := by
    intro object reason
    exact certificate.relevance object reason.2 reason.1

/-- Soundness of the checked extension.  The theorem reaches only the
selected target conclusion and makes no claim that every same-kind analogy is
licensed. -/
theorem sound (certificate : TuiLeiCertificate M argument) :
    argument.sadhya argument.paksa := by
  exact certificate.toSemanticProof.sound

/-- If every reason-bearing object lies in the standard's kind, the local
relevance certificate also yields the unrestricted pervasion used elsewhere
in the repository. -/
theorem global_pervasion_of_reason_confinement
    (certificate : TuiLeiCertificate M argument)
    (confined : ∀ object, argument.reason object →
      M.kindOf object = M.kindOf certificate.standard.illustration.witness) :
    BuddhistComparativeLogic.Nyaya.Pervasion argument := by
  intro object reason
  exact certificate.relevance object (confined object reason) reason

end TuiLeiCertificate

/-! ## Public parallelism is syntactic data -/

/-- Four form labels suffice to record whether source and target utterances
reuse the same reason and conclusion frames.  The labels carry no denotation. -/
structure PublicAnalogy (Form : Type u) where
  sourceReasonForm : Form
  targetReasonForm : Form
  sourceConclusionForm : Form
  targetConclusionForm : Form
  deriving Repr

namespace PublicAnalogy

/-- Surface parallelism contains only equalities between form labels. -/
def SyntacticallyParallel {Form : Type u} (presentation : PublicAnalogy Form) :
    Prop :=
  presentation.sourceReasonForm = presentation.targetReasonForm ∧
    presentation.sourceConclusionForm = presentation.targetConclusionForm

end PublicAnalogy

/-! ## A finite nonvacuous licensed extension -/

inductive Artifact where
  | modelTile
  | targetTile
  | bell
  deriving DecidableEq, Repr

inductive ArtifactKind where
  | shaped
  | sounded
  deriving DecidableEq, Repr

inductive ArtifactName where
  | tile
  | resonator
  deriving DecidableEq, Repr

open Artifact ArtifactKind ArtifactName

/-- Two tiles occupy one kind and a bell occupies another.  Both name
extensions are inhabited and the kinds are distinguished. -/
def artifactNaming : Naming Artifact ArtifactName ArtifactKind where
  kindOf
    | .modelTile | .targetTile => .shaped
    | .bell => .sounded
  designates
    | .tile, object => object = .modelTile ∨ object = .targetTile
    | .resonator, object => object = .bell
  admits
    | .tile, kind => kind = .shaped
    | .resonator, kind => kind = .sounded

theorem artifact_naming_regular : artifactNaming.Regular := by
  intro name object
  cases name <;> cases object <;>
    simp [Naming.Fits, artifactNaming]

/-- The reason and conclusion both select the two tiles.  The bell supplies a
genuine negative comparison, so pervasion is not vacuous. -/
def tileArgument : Anumana Artifact where
  paksa := .targetTile
  reason object := object = .modelTile ∨ object = .targetTile
  sadhya object := object ≠ .bell

def tileStandard : Standard artifactNaming tileArgument where
  illustration :=
    { witness := .modelTile
      distinct := by decide
      hasReason := Or.inl rfl
      hasThesis := by simp [tileArgument] }
  sameKind := rfl

def tileExtension : TuiLeiCertificate artifactNaming tileArgument where
  standard := tileStandard
  subjectReason := Or.inr rfl
  relevance := by
    intro object _kind reason
    rcases reason with rfl | rfl <;> simp [tileArgument]

/-- The licensed finite model has a true target, a distinct positive
standard, two inhabited name extensions, and a negative object outside the
reason and conclusion. -/
theorem tile_extension_nonvacuous :
    tileArgument.sadhya tileArgument.paksa ∧
      (∃ source, source ≠ tileArgument.paksa ∧
        tileArgument.reason source ∧ tileArgument.sadhya source) ∧
      artifactNaming.designates .tile .targetTile ∧
      artifactNaming.designates .resonator .bell ∧
      (∃ outside, ¬ tileArgument.reason outside ∧
        ¬ tileArgument.sadhya outside) := by
  refine ⟨tileExtension.sound, ?_, ?_, ?_, ?_⟩
  · exact ⟨.modelTile, by decide, Or.inl rfl, by simp [tileArgument]⟩
  · exact Or.inr rfl
  · exact rfl
  · exact ⟨.bell, by simp [tileArgument], by simp [tileArgument]⟩

/-! ## Finite boundaries for unlicensed analogies and names -/

inductive PairObject where
  | source
  | target
  deriving DecidableEq, Repr

inductive SingleKind where
  | shared
  deriving DecidableEq, Repr

inductive PairName where
  | pair
  deriving DecidableEq, Repr

inductive Form where
  | reasonFrame
  | conclusionFrame
  deriving DecidableEq, Repr

open PairObject SingleKind PairName Form

def pairNaming : Naming PairObject PairName SingleKind where
  kindOf _ := .shared
  designates _ _ := True
  admits _ _ := True

/-- Source and target share a reason, but only the source has the conclusion. -/
def badExtensionArgument : Anumana PairObject where
  paksa := .target
  reason _ := True
  sadhya object := object = .source

def badStandard : Standard pairNaming badExtensionArgument where
  illustration :=
    { witness := .source
      distinct := by decide
      hasReason := trivial
      hasThesis := rfl }
  sameKind := rfl

def parallelBadPresentation : PublicAnalogy Form where
  sourceReasonForm := .reasonFrame
  targetReasonForm := .reasonFrame
  sourceConclusionForm := .conclusionFrame
  targetConclusionForm := .conclusionFrame

/-- Syntactic parallelism, common kind, a positive standard, and target
application coexist with a false target conclusion.  The missing premise is
precisely kind-bounded semantic relevance. -/
theorem parallel_form_and_same_kind_do_not_license_extension :
    parallelBadPresentation.SyntacticallyParallel ∧
      Nonempty (Standard pairNaming badExtensionArgument) ∧
      badExtensionArgument.reason badExtensionArgument.paksa ∧
      ¬ (∀ object,
        pairNaming.kindOf object =
            pairNaming.kindOf badStandard.illustration.witness →
          badExtensionArgument.reason object →
          badExtensionArgument.sadhya object) ∧
      ¬ badExtensionArgument.sadhya badExtensionArgument.paksa ∧
      ¬ Nonempty (TuiLeiCertificate pairNaming badExtensionArgument) := by
  refine ⟨⟨rfl, rfl⟩, ⟨badStandard⟩, trivial, ?_,
    by simp [badExtensionArgument], ?_⟩
  · intro relevance
    exact PairObject.noConfusion
      (relevance .target rfl trivial)
  · rintro ⟨certificate⟩
    exact PairObject.noConfusion certificate.sound

/-- A deliberately irregular naming model: uttering the tile name of the
target does not make that use fit the sole kind license. -/
def misnaming : Naming PairObject PairName SingleKind where
  kindOf _ := .shared
  designates _ object := object = .target
  admits _ _ := False

theorem mere_designation_does_not_ensure_name_object_fit :
    misnaming.designates .pair .target ∧
      ¬ misnaming.Fits .pair .target ∧
      ¬ misnaming.Regular := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [Naming.Fits, misnaming]
  · intro regular
    exact (by simpa [Naming.Fits, misnaming] using regular .pair .target)

end BuddhistComparativeLogic.MohistCanons
