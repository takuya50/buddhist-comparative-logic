/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceModes
import BuddhistComparativeLogic.Buddhist.Madhyamaka.TwoTruths
import BuddhistComparativeLogic.Buddhist.Pramana.Tattvasamgraha

/-!
# A scoped reconstruction of the neither-one-nor-many reason

This module formalizes the proof shape associated with Śāntarakṣita's
`ekānekaviyogahetu`.  `Intrinsic`, `TrulyOne` and `TrulyMany` are primitive
predicates on analyzed subjects.  In particular, the last two are not Lean
claims about the cardinality of the carrier type.  The central conclusion
requires an explicit premise that anything intrinsic falls under one of the
two horns and explicit rejections of both horns.

The many horn may instead be closed from a constitution bridge: anything
truly many has a truly one constituent on which it depends mereologically.
The dependence component uses the intervention-sensitive relation already
defined in `BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceModes`; it is not silently identified with a
bare membership relation.

Finite models exhibit both boundaries.  If one-or-many exhaustiveness is
absent, an intrinsic subject can fall under neither horn.  If the constitution
bridge is absent, a subject can be stipulated truly many even on a singleton
Lean carrier.  A separate two-level model keeps conventional existence while
rejecting intrinsic existence.
-/

namespace BuddhistComparativeLogic.Ekanekaviyoga

universe u v

/-- Analysis data for the one-many dilemma.  The capitalized predicates below
are aliases for these independent fields, not cardinality definitions. -/
structure Model (D : Type u) where
  dependence : BuddhistComparativeLogic.DependenceModes.Model.{u, u} D
  intrinsic : D -> Prop
  trulyOne : D -> Prop
  trulyMany : D -> Prop
  conventionallyExists : D -> Prop

namespace Model

variable {D : Type u} (model : Model D)

/-- The target notion of intrinsic existence or own-nature in this scoped
reconstruction. -/
def Intrinsic (subject : D) : Prop := model.intrinsic subject

/-- Ultimate analytical unity, deliberately distinct from a singleton type or
from having one conventionally counted component. -/
def TrulyOne (subject : D) : Prop := model.trulyOne subject

/-- Ultimate analytical plurality, deliberately distinct from the carrier
having two or more inhabitants. -/
def TrulyMany (subject : D) : Prop := model.trulyMany subject

/-- Ordinary existence at the conventional level. -/
def ConventionallyExists (subject : D) : Prop :=
  model.conventionallyExists subject

/-- The disputed exhaustive division of an intrinsically existent subject. -/
def OneManyExhaustive : Prop :=
  forall subject, model.Intrinsic subject ->
    model.TrulyOne subject ∨ model.TrulyMany subject

/-- Uniform rejection of the unity horn. -/
def RejectsOne : Prop := forall subject, ¬ model.TrulyOne subject

/-- Uniform rejection of the plurality horn. -/
def RejectsMany : Prop := forall subject, ¬ model.TrulyMany subject

/-- A truly-one constituent comes with a witnessed mereological dependence
edge from that constituent to the constituted subject. -/
def TrueOneConstituent (component whole : D) : Prop :=
  model.TrulyOne component /\
    model.dependence.DependsAt .mereological component whole

/-- The explicit composition bridge used to close the many horn. -/
structure ConstitutionBridge : Prop where
  manyHasTrueOneConstituent : forall subject,
    model.TrulyMany subject ->
      exists component, model.TrueOneConstituent component subject

/-- A bridge witness exposes the actual mereological dependence edge, so its
dependence component can be audited through the shared dependence API. -/
theorem many_has_mereological_dependency
    (bridge : model.ConstitutionBridge) {subject : D}
    (many : model.TrulyMany subject) :
    exists component,
      model.dependence.DependsAt .mereological component subject := by
  obtain ⟨component, _, edge⟩ :=
    bridge.manyHasTrueOneConstituent subject many
  exact ⟨component, edge⟩

/-- If all genuinely unitary candidates are rejected, the constitution bridge
turns that rejection into rejection of the genuinely many horn. -/
theorem rejects_many_from_constitution
    (bridge : model.ConstitutionBridge) (rejectOne : model.RejectsOne) :
    model.RejectsMany := by
  intro subject many
  obtain ⟨component, one, _⟩ :=
    bridge.manyHasTrueOneConstituent subject many
  exact rejectOne component one

/-- With the existing mereological invariance criterion, the same bridge also
makes every many subject empty according to the dependence projection. -/
theorem many_is_empty_by_mereological_dependence
    (bridge : model.ConstitutionBridge)
    (invariant : model.dependence.InvariantOwnAt .mereological)
    {subject : D} (many : model.TrulyMany subject) :
    (model.dependence.toDependenceAt .mereological).emptyOf subject := by
  obtain ⟨component, edge⟩ :=
    model.many_has_mereological_dependency bridge many
  exact model.dependence.empty_of_mode_dependency
    .mereological invariant edge

/-- The three proof-bearing premises of the two-horn analysis. -/
structure DilemmaPremises : Prop where
  exhaustive : model.OneManyExhaustive
  rejectsOne : model.RejectsOne
  rejectsMany : model.RejectsMany

/-- If every intrinsic subject must be truly one or truly many, and each horn
is rejected, then no subject has intrinsic existence. -/
theorem no_intrinsic_of_one_many_rejection
    (premises : model.DilemmaPremises) :
    forall subject, ¬ model.Intrinsic subject := by
  intro subject intrinsic
  cases premises.exhaustive subject intrinsic with
  | inl one => exact premises.rejectsOne subject one
  | inr many => exact premises.rejectsMany subject many

/-- Package the direct one-horn rejection and the constitution-derived
many-horn rejection into the complete dilemma. -/
theorem dilemmaOfConstitution
    (exhaustive : model.OneManyExhaustive)
    (rejectOne : model.RejectsOne)
    (bridge : model.ConstitutionBridge) : model.DilemmaPremises where
  exhaustive := exhaustive
  rejectsOne := rejectOne
  rejectsMany := model.rejects_many_from_constitution bridge rejectOne

/-- The common proof form with the constitution bridge exposed at the call
site rather than hidden in the many-horn premise. -/
theorem no_intrinsic_via_constitution
    (exhaustive : model.OneManyExhaustive)
    (rejectOne : model.RejectsOne)
    (bridge : model.ConstitutionBridge) :
    forall subject, ¬ model.Intrinsic subject :=
  model.no_intrinsic_of_one_many_rejection
    (model.dilemmaOfConstitution exhaustive rejectOne bridge)

/-- Reuse the Tattvasaṃgraha debate interface while keeping the one-many
premises visible as parameters.  Its `reason` is the opponent's intrinsic
existence assumption, so the rule has the shape of a reductio. -/
def toDebateRule (premises : model.DilemmaPremises) :
    BuddhistComparativeLogic.Tattvasamgraha.DebateRule D where
  topics := [.madhyamakaEmptiness, .dependentOwnBeing]
  scope := fun _ => True
  opponentThesis := model.Intrinsic
  reason := model.Intrinsic
  result := fun subject => ¬ model.Intrinsic subject
  pervasion := by
    intro subject _ _
    exact model.no_intrinsic_of_one_many_rejection premises subject
  refutes := by
    intro subject _ rejected asserted
    exact rejected asserted

theorem debate_rule_rejects_intrinsic
    (premises : model.DilemmaPremises) {subject : D}
    (opponentAssumption : model.Intrinsic subject) :
    (model.toDebateRule premises).result subject /\
      ¬ (model.toDebateRule premises).opponentThesis subject := by
  have result := (model.toDebateRule premises).pervasion
    subject trivial opponentAssumption
  exact ⟨result,
    (model.toDebateRule premises).refutes subject trivial result⟩

/-- Two-level existence indexed by the shared conventional/ultimate type. -/
def ExistsAtLevel (level : BuddhistComparativeLogic.Satya2) (subject : D) : Prop :=
  match level with
  | .samvrti => model.ConventionallyExists subject
  | .paramartha => model.Intrinsic subject

/-- Rejection of intrinsic existence is compatible with an explicitly given
conventional witness. -/
theorem two_level_status
    (premises : model.DilemmaPremises) {subject : D}
    (conventional : model.ConventionallyExists subject) :
    model.ExistsAtLevel .samvrti subject /\
      ¬ model.ExistsAtLevel .paramartha subject :=
  ⟨conventional,
    model.no_intrinsic_of_one_many_rejection premises subject⟩

end Model

/-! ## Finite audits of the two missing bridges -/

/-- A dependence model with no contextual variations. -/
def inertDependence (D : Type u) (own : D -> Prop) :
    BuddhistComparativeLogic.DependenceModes.Model.{u, u} D where
  Context := fun _ => ULift.{u} Unit
  support := fun _ _ _ => false
  manifest := fun _ _ _ => false
  own := own

/-- An intrinsic subject which falls under neither analytical horn. -/
def missingCoverageModel : Model Unit where
  dependence := inertDependence Unit (fun _ => True)
  intrinsic := fun _ => True
  trulyOne := fun _ => False
  trulyMany := fun _ => False
  conventionallyExists := fun _ => True

theorem horns_rejected_but_intrinsic_survives_without_coverage :
    missingCoverageModel.RejectsOne /\
      missingCoverageModel.RejectsMany /\
      missingCoverageModel.Intrinsic () /\
      ¬ missingCoverageModel.OneManyExhaustive := by
  refine ⟨fun _ one => one, fun _ many => many, trivial, ?_⟩
  intro exhaustive
  cases exhaustive () trivial with
  | inl one => exact one
  | inr many => exact many

/-- A stipulated truly-many intrinsic subject with no truly-one constituent.
Using `Unit` emphasizes that `TrulyMany` is an analytical predicate, not a
statement about the number of inhabitants of the Lean carrier. -/
def missingConstitutionModel : Model Unit where
  dependence := inertDependence Unit (fun _ => True)
  intrinsic := fun _ => True
  trulyOne := fun _ => False
  trulyMany := fun _ => True
  conventionallyExists := fun _ => True

theorem missing_constitution_has_exhaustive_many_horn :
    missingConstitutionModel.OneManyExhaustive /\
      missingConstitutionModel.RejectsOne /\
      missingConstitutionModel.TrulyMany () /\
      missingConstitutionModel.Intrinsic () := by
  exact ⟨fun _ _ => Or.inr trivial, fun _ one => one, trivial, trivial⟩

theorem constitution_bridge_is_substantive :
    ¬ missingConstitutionModel.ConstitutionBridge := by
  intro bridge
  obtain ⟨component, one, _⟩ :=
    bridge.manyHasTrueOneConstituent () trivial
  exact one

theorem many_horn_survives_without_constitution_bridge :
    missingConstitutionModel.OneManyExhaustive /\
      missingConstitutionModel.RejectsOne /\
      ¬ missingConstitutionModel.RejectsMany /\
      missingConstitutionModel.Intrinsic () := by
  refine ⟨missing_constitution_has_exhaustive_many_horn.1,
    missing_constitution_has_exhaustive_many_horn.2.1, ?_, trivial⟩
  intro rejectsMany
  exact rejectsMany () trivial

/-- The singleton carrier and a true `TrulyMany` predicate coexist, formally
auditing the prohibition on reading the horn as carrier cardinality. -/
theorem truly_many_is_not_carrier_cardinality :
    (forall x y : Unit, x = y) /\
      missingConstitutionModel.TrulyMany () :=
  ⟨fun _ _ => rfl, trivial⟩

/-! ## Conventional existence together with absence of intrinsic existence -/

def conventionalOnlyModel : Model Unit where
  dependence := inertDependence Unit (fun _ => False)
  intrinsic := fun _ => False
  trulyOne := fun _ => False
  trulyMany := fun _ => False
  conventionallyExists := fun _ => True

theorem conventional_only_dilemma : conventionalOnlyModel.DilemmaPremises := by
  constructor
  · intro subject intrinsic
    exact False.elim intrinsic
  · intro subject one
    exact one
  · intro subject many
    exact many

theorem no_intrinsic_and_conventional_existence_coexist :
    conventionalOnlyModel.ExistsAtLevel .samvrti () /\
      ¬ conventionalOnlyModel.ExistsAtLevel .paramartha () :=
  conventionalOnlyModel.two_level_status conventional_only_dilemma trivial

theorem no_intrinsic_does_not_deny_conventional_existence :
    ¬ ((¬ conventionalOnlyModel.Intrinsic ()) ->
      ¬ conventionalOnlyModel.ConventionallyExists ()) := by
  intro denial
  exact denial (fun intrinsic => intrinsic) trivial

end BuddhistComparativeLogic.Ekanekaviyoga
