/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.Dharma

/-!
# A scoped rafter-house mereology

This module develops a typed whole-part and functional-intervention model
inspired by Fazang's rafter-and-house discussions and the six characteristics.
The primary passage is *Huayan yisheng jiaoyi fenqi zhang* 華嚴一乘教義分齊章,
Taishō T45 no. 1866, 507c3–508a22, in pinned CBETA XML P5
<https://github.com/cbeta-org/xml-p5/blob/dbdea41071e1e260ad84b72faefd4587333cf76d/T/T45/T45n1866.xml#L2797-L2841>;
Jones's study supplies secondary orientation:
<https://doi.org/10.1080/09608788.2018.1563768> (accessed 2026-09-19).

The declarations are an auditable mathematical reconstruction, not a literal
translation of Fazang.  In particular, `CommonIdentity` below means witnessed
joint activity in a manifested whole, while `StrongInterpenetration` is an
intentionally strong functional interchangeability condition.  Neither is
silently identified with numerical equality or with every Huayan use of
identity and interpenetration.  No Chinese translation is reproduced; the
English labels and all formal predicates are project-authored paraphrases.
-/

namespace BuddhistComparativeLogic.FazangMereology

/-! ## The six-characteristic index -/

/-- English labels for the six-characteristic scheme used to organize the
formal predicates below. -/
inductive Characteristic where
  | totality
  | particularity
  | commonality
  | differentiation
  | integration
  | disintegration
  deriving DecidableEq, Repr

open Characteristic

def characteristics : List Characteristic :=
  [.totality, .particularity, .commonality, .differentiation,
    .integration, .disintegration]

theorem six_characteristics : HasCardinality Characteristic 6 := by
  refine ⟨characteristics, ?_, by decide, by decide⟩
  intro characteristic
  cases characteristic <;> decide

/-! ## Typed parts, wholes, functions, and contexts -/

/-- Parts and wholes have different carrier types.  Static membership and
contribution are separated from context-sensitive presence, role activity,
functional realization, and manifestation of a whole. -/
structure Model (Part : Type u) (Whole : Type v)
    (Function : Type w) (Context : Type x) where
  member : Part -> Whole -> Prop
  contributes : Part -> Whole -> Function -> Prop
  required : Whole -> Function -> Prop
  partPresent : Context -> Part -> Bool
  roleActive : Context -> Part -> Whole -> Bool
  functionActive : Context -> Whole -> Function -> Bool
  wholePresent : Context -> Whole -> Bool

namespace Model

variable {Part : Type u} {Whole : Type v}
    {Function : Type w} {Context : Type x}
    (model : Model Part Whole Function Context)

/-- A controlled part-removal intervention changes the selected part from
present to absent while holding every distinct part fixed. -/
def RemovesOnly (before after : Context) (part : Part) : Prop :=
  model.partPresent before part = true /\
    model.partPresent after part = false /\
    forall other, other ≠ part ->
      model.partPresent before other = model.partPresent after other

/-- Every function explicitly required by a whole has at least one member
that contributes it. -/
def RequiredCoverage (whole : Whole) : Prop :=
  forall function, model.required whole function ->
    exists part,
      model.member part whole /\ model.contributes part whole function

def IntegratedAt (context : Context) (whole : Whole) : Prop :=
  forall function, model.required whole function ->
    model.functionActive context whole function = true

/-- Functional completeness is sufficient for whole manifestation. -/
def IntegrationLaw (whole : Whole) : Prop :=
  forall context, model.IntegratedAt context whole ->
    model.wholePresent context whole = true

/-- Loss of any required function prevents manifestation of the whole.  This
bridge is kept explicit rather than built into `wholePresent`. -/
def DisintegrationLaw (whole : Whole) : Prop :=
  forall context,
    (exists function,
      model.required whole function /\
        model.functionActive context whole function = false) ->
      model.wholePresent context whole = false

/-- Shared identity in this scoped model is witnessed common whole-forming
status: both tokens are members, and there is one manifested context in which
both roles are active.  It is deliberately weaker than equality of the part
tokens. -/
def CommonIdentity (first second : Part) (whole : Whole) : Prop :=
  model.member first whole /\
    model.member second whole /\
    exists context,
      model.wholePresent context whole = true /\
        model.roleActive context first whole = true /\
        model.roleActive context second whole = true

/-- Two common members retain distinct tokens, and one function witnesses a
difference between their contribution profiles. -/
def DifferentiatedIdentity
    (first second : Part) (whole : Whole) : Prop :=
  model.CommonIdentity first second whole /\
    first ≠ second /\
    exists function,
      (model.contributes first whole function /\
          Not (model.contributes second whole function)) \/
        (model.contributes second whole function /\
          Not (model.contributes first whole function))

theorem differentiated_identity_preserves_part_distinctness
    {first second : Part} {whole : Whole}
    (differentiated : model.DifferentiatedIdentity first second whole) :
    first ≠ second :=
  differentiated.2.1

/-- A strong, intentionally testable reading of functional interpenetration:
the two common members are interchangeable for every contribution. -/
def StrongInterpenetration
    (first second : Part) (whole : Whole) : Prop :=
  model.CommonIdentity first second whole /\
    forall function,
      model.contributes first whole function <->
        model.contributes second whole function

/-- A witnessed difference in contribution profiles is incompatible with
strong functional interchangeability. -/
theorem differentiated_identity_excludes_strong_interpenetration
    {first second : Part} {whole : Whole}
    (differentiated : model.DifferentiatedIdentity first second whole) :
    Not (model.StrongInterpenetration first second whole) := by
  rintro ⟨_, interchangeability⟩
  obtain ⟨function, firstOnly | secondOnly⟩ := differentiated.2.2
  · exact firstOnly.2 ((interchangeability function).mp firstOnly.1)
  · exact secondOnly.2 ((interchangeability function).mpr secondOnly.1)

/-- Indispensability for one function is witnessed by an actual controlled
removal: a manifested whole and active function precede the intervention, and
that function is lost afterward. -/
def IndispensableFor (part : Part) (whole : Whole)
    (function : Function) : Prop :=
  model.member part whole /\
    model.required whole function /\
    model.contributes part whole function /\
    exists before after,
      model.RemovesOnly before after part /\
        model.wholePresent before whole = true /\
        model.functionActive before whole function = true /\
        model.functionActive after whole function = false

/-- Every covering contribution to a required function is indispensable in
the intervention sense just defined. -/
def CoveredContributionsIndispensable (whole : Whole) : Prop :=
  forall part function,
    model.member part whole ->
    model.required whole function ->
    model.contributes part whole function ->
      model.IndispensableFor part whole function

/-- Whole-to-part dependence is witnessed by removing only that part and
observing failure of a previously manifested whole. -/
def WholeDependsOnPart (part : Part) (whole : Whole) : Prop :=
  exists before after,
    model.RemovesOnly before after part /\
      model.wholePresent before whole = true /\
      model.wholePresent after whole = false

/-- A controlled whole-withdrawal intervention changes the selected whole
from present to absent while holding every part-presence fact fixed. -/
def WithdrawsOnlyWhole (before after : Context) (whole : Whole) : Prop :=
  model.wholePresent before whole = true /\
    model.wholePresent after whole = false /\
    forall part,
      model.partPresent before part = model.partPresent after part

/-- Part-to-whole dependence concerns the role of a token *as a part*: a
controlled withdrawal of the whole, with every part token held fixed, changes
that role from active to inactive. -/
def PartDependsOnWhole (part : Part) (whole : Whole) : Prop :=
  exists before after,
    model.WithdrawsOnlyWhole before after whole /\
      model.roleActive before part whole = true /\
      model.roleActive after part whole = false

def MutuallyDependent (part : Part) (whole : Whole) : Prop :=
  model.WholeDependsOnPart part whole /\
    model.PartDependsOnWhole part whole

/-- The status of every admitted member as a part is grounded in the whole by
a witnessed whole-withdrawal intervention. -/
def RoleGrounding (whole : Whole) : Prop :=
  forall part, model.member part whole ->
    model.PartDependsOnWhole part whole

/-- Required function loss plus the explicit disintegration bridge converts
an indispensability witness into whole-to-part dependence. -/
theorem whole_depends_on_indispensable_part
    {part : Part} {whole : Whole} {function : Function}
    (disintegrates : model.DisintegrationLaw whole)
    (indispensable : model.IndispensableFor part whole function) :
    model.WholeDependsOnPart part whole := by
  rcases indispensable with
    ⟨_, required, _, before, after, removal, wholeBefore, _, lost⟩
  refine ⟨before, after, removal, wholeBefore, ?_⟩
  exact disintegrates after ⟨function, required, lost⟩

/-- Coverage selects a contributor for the requested function;
indispensability supplies a removal intervention; disintegration turns the
lost function into witnessed failure of the whole. -/
theorem covered_indispensability_yields_whole_failure
    {whole : Whole} {function : Function}
    (coverage : model.RequiredCoverage whole)
    (indispensable : model.CoveredContributionsIndispensable whole)
    (disintegrates : model.DisintegrationLaw whole)
    (required : model.required whole function) :
    exists part,
      model.member part whole /\
        model.contributes part whole function /\
        model.WholeDependsOnPart part whole := by
  obtain ⟨part, member, contributes⟩ := coverage function required
  refine ⟨part, member, contributes, ?_⟩
  exact model.whole_depends_on_indispensable_part disintegrates
    (indispensable part function member required contributes)

/-- Adding the separately stated role-grounding direction yields mutual
dependence for a covering contributor. -/
theorem covered_indispensability_yields_mutual_dependence
    {whole : Whole} {function : Function}
    (coverage : model.RequiredCoverage whole)
    (indispensable : model.CoveredContributionsIndispensable whole)
    (disintegrates : model.DisintegrationLaw whole)
    (roleGrounding : model.RoleGrounding whole)
    (required : model.required whole function) :
    exists part,
      model.member part whole /\
        model.contributes part whole function /\
        model.MutuallyDependent part whole := by
  obtain ⟨part, member, contributes, wholeDepends⟩ :=
    model.covered_indispensability_yields_whole_failure
      coverage indispensable disintegrates required
  exact ⟨part, member, contributes, wholeDepends,
    roleGrounding part member⟩

/-- A six-field certificate corresponding to the organizing labels above.
The fields are laws of this reconstruction rather than translations of the
six Sanskrit or Chinese terms. -/
structure SixfoldProfile (whole : Whole) : Prop where
  totality : model.RequiredCoverage whole
  particularity : forall part, model.member part whole ->
    exists function,
      model.required whole function /\ model.contributes part whole function
  commonality : forall first second,
    model.member first whole -> model.member second whole ->
      model.CommonIdentity first second whole
  differentiation : forall first second,
    model.member first whole -> model.member second whole ->
    first ≠ second -> model.DifferentiatedIdentity first second whole
  integration : model.IntegrationLaw whole
  disintegration : model.DisintegrationLaw whole

/-- The full profile is accepted as one auditable package.  This particular
dependence consequence uses its coverage and disintegration fields; the other
four fields record separate six-characteristic obligations and are not
claimed to be necessary for this theorem. -/
theorem sixfold_profile_with_indispensability_yields_mutual_dependence
    {whole : Whole} {function : Function}
    (profile : model.SixfoldProfile whole)
    (indispensable : model.CoveredContributionsIndispensable whole)
    (roleGrounding : model.RoleGrounding whole)
    (required : model.required whole function) :
    exists part,
      model.member part whole /\
        model.contributes part whole function /\
        model.MutuallyDependent part whole :=
  model.covered_indispensability_yields_mutual_dependence
    profile.totality indispensable profile.disintegration roleGrounding required

/-- Two distinct static members suffice for a mere collection. -/
def MereCollection (whole : Whole) : Prop :=
  exists first second,
    first ≠ second /\
      model.member first whole /\ model.member second whole

/-- An optional member has a controlled removal under which the whole remains
manifested. -/
def OptionalPart (part : Part) (whole : Whole) : Prop :=
  model.member part whole /\
    exists before after,
      model.RemovesOnly before after part /\
        model.wholePresent before whole = true /\
        model.wholePresent after whole = true

end Model

/-! ## An optional-part countermodel -/

inductive HousePart where
  | rafter
  | ornament
  deriving DecidableEq, Repr

inductive House where
  | dwelling
  deriving DecidableEq, Repr

inductive HouseFunction where
  | loadBearing
  | decoration
  deriving DecidableEq, Repr

open HousePart House HouseFunction

/-! ## A finite positive model of mutual dependence -/

inductive StructuralPart where
  | leftRafter
  | rightRafter
  deriving DecidableEq, Repr

inductive StructuralFunction where
  | leftSupport
  | rightSupport
  deriving DecidableEq, Repr

inductive StructuralContext where
  | intact
  | leftRemoved
  | rightRemoved
  | wholeWithdrawn
  deriving DecidableEq, Repr

open StructuralPart StructuralFunction StructuralContext

/-- Each rafter supplies one required support.  Removing either rafter loses
its support and the house; withdrawing the house leaves the tokens available
but deactivates their roles as house-parts. -/
def loadBearingHouse :
    Model StructuralPart House StructuralFunction StructuralContext where
  member := fun _ _ => True
  contributes := fun part _ function =>
    match part, function with
    | .leftRafter, .leftSupport => True
    | .rightRafter, .rightSupport => True
    | _, _ => False
  required := fun _ _ => True
  partPresent := fun context part =>
    match context, part with
    | .leftRemoved, .leftRafter => false
    | .rightRemoved, .rightRafter => false
    | _, _ => true
  roleActive := fun context _ _ =>
    match context with
    | .intact => true
    | _ => false
  functionActive := fun context _ function =>
    match context, function with
    | .intact, _ => true
    | .leftRemoved, .rightSupport => true
    | .rightRemoved, .leftSupport => true
    | _, _ => false
  wholePresent := fun context _ =>
    match context with
    | .intact => true
    | _ => false

theorem load_bearing_coverage :
    loadBearingHouse.RequiredCoverage .dwelling := by
  intro function _
  cases function with
  | leftSupport => exact ⟨.leftRafter, trivial, trivial⟩
  | rightSupport => exact ⟨.rightRafter, trivial, trivial⟩

theorem load_bearing_contributions_are_indispensable :
    loadBearingHouse.CoveredContributionsIndispensable .dwelling := by
  intro part function _ _ contributes
  cases part <;> cases function
  case leftRafter.leftSupport =>
    refine ⟨trivial, trivial, trivial,
      .intact, .leftRemoved, ?_, rfl, rfl, rfl⟩
    refine ⟨rfl, rfl, ?_⟩
    intro other distinct
    cases other with
    | leftRafter => exact (distinct rfl).elim
    | rightRafter => rfl
  case leftRafter.rightSupport => exact False.elim contributes
  case rightRafter.leftSupport => exact False.elim contributes
  case rightRafter.rightSupport =>
    refine ⟨trivial, trivial, trivial,
      .intact, .rightRemoved, ?_, rfl, rfl, rfl⟩
    refine ⟨rfl, rfl, ?_⟩
    intro other distinct
    cases other with
    | leftRafter => rfl
    | rightRafter => exact (distinct rfl).elim

theorem load_bearing_integration :
    loadBearingHouse.IntegrationLaw .dwelling := by
  intro context integrated
  cases context with
  | intact => rfl
  | leftRemoved =>
      have impossible := integrated .leftSupport trivial
      cases impossible
  | rightRemoved =>
      have impossible := integrated .rightSupport trivial
      cases impossible
  | wholeWithdrawn =>
      have impossible := integrated .leftSupport trivial
      cases impossible

theorem load_bearing_disintegration :
    loadBearingHouse.DisintegrationLaw .dwelling := by
  intro context lost
  cases context with
  | intact =>
      obtain ⟨function, _, impossible⟩ := lost
      cases function <;> cases impossible
  | leftRemoved => rfl
  | rightRemoved => rfl
  | wholeWithdrawn => rfl

theorem load_bearing_role_grounding :
    loadBearingHouse.RoleGrounding .dwelling := by
  intro part _
  cases part <;> refine ⟨.intact, .wholeWithdrawn, ?_, rfl, rfl⟩
  all_goals
    refine ⟨rfl, rfl, ?_⟩
    intro fixedPart
    cases fixedPart <;> rfl

theorem load_bearing_sixfold_profile :
    loadBearingHouse.SixfoldProfile .dwelling := by
  refine {
    totality := load_bearing_coverage
    particularity := ?_
    commonality := ?_
    differentiation := ?_
    integration := load_bearing_integration
    disintegration := load_bearing_disintegration
  }
  · intro part _
    cases part with
    | leftRafter => exact ⟨.leftSupport, trivial, trivial⟩
    | rightRafter => exact ⟨.rightSupport, trivial, trivial⟩
  · intro first second _ _
    exact ⟨trivial, trivial, .intact, rfl, rfl, rfl⟩
  · intro first second _ _ distinct
    cases first <;> cases second
    · exact (distinct rfl).elim
    · exact ⟨⟨trivial, trivial, .intact, rfl, rfl, rfl⟩, distinct,
        .leftSupport, Or.inl ⟨trivial, by simp [loadBearingHouse]⟩⟩
    · exact ⟨⟨trivial, trivial, .intact, rfl, rfl, rfl⟩, distinct,
        .rightSupport, Or.inl ⟨trivial, by simp [loadBearingHouse]⟩⟩
    · exact (distinct rfl).elim

theorem left_rafter_and_house_are_mutually_dependent :
    loadBearingHouse.MutuallyDependent .leftRafter .dwelling := by
  have witness :=
    loadBearingHouse.sixfold_profile_with_indispensability_yields_mutual_dependence
      load_bearing_sixfold_profile
      load_bearing_contributions_are_indispensable
      load_bearing_role_grounding
      (function := StructuralFunction.leftSupport) trivial
  obtain ⟨part, _, contributes, mutuality⟩ := witness
  cases part with
  | leftRafter => exact mutuality
  | rightRafter => exact False.elim contributes

/-- The generic premise package has a finite, nonvacuous inhabitant.  The
result includes a controlled part removal and a controlled whole withdrawal;
the latter leaves both part-presence facts unchanged. -/
theorem load_bearing_positive_instance :
    loadBearingHouse.RequiredCoverage .dwelling /\
      loadBearingHouse.CoveredContributionsIndispensable .dwelling /\
      loadBearingHouse.DisintegrationLaw .dwelling /\
      loadBearingHouse.RoleGrounding .dwelling /\
      loadBearingHouse.SixfoldProfile .dwelling /\
      loadBearingHouse.MutuallyDependent .leftRafter .dwelling :=
  ⟨load_bearing_coverage,
    load_bearing_contributions_are_indispensable,
    load_bearing_disintegration,
    load_bearing_role_grounding,
    load_bearing_sixfold_profile,
    left_rafter_and_house_are_mutually_dependent⟩

/-- `Bool` records whether the optional ornament is installed.  The rafter and
load-bearing function remain present in both contexts. -/
def optionalHouse : Model HousePart House HouseFunction Bool where
  member := fun _ _ => True
  contributes := fun part _ function =>
    match part, function with
    | .rafter, .loadBearing => True
    | .ornament, .decoration => True
    | _, _ => False
  required := fun _ function => function = .loadBearing
  partPresent := fun context part =>
    match part with
    | .rafter => true
    | .ornament => context
  roleActive := fun context part _ =>
    match part with
    | .rafter => true
    | .ornament => context
  functionActive := fun context _ function =>
    match function with
    | .loadBearing => true
    | .decoration => context
  wholePresent := fun _ _ => true

theorem optional_house_has_required_coverage :
    optionalHouse.RequiredCoverage .dwelling := by
  intro function required
  cases function with
  | loadBearing => exact ⟨.rafter, trivial, trivial⟩
  | decoration => cases required

theorem ornament_is_optional :
    optionalHouse.OptionalPart .ornament .dwelling := by
  refine ⟨trivial, true, false, ?_, rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  intro other distinct
  cases other with
  | rafter => rfl
  | ornament => exact (distinct rfl).elim

theorem ornament_removal_does_not_break_the_house :
    Not (optionalHouse.WholeDependsOnPart .ornament .dwelling) := by
  rintro ⟨_, _, _, _, failure⟩
  cases failure

/-- Membership, an actual removal intervention, and coverage of all required
functions coexist with failure of strong whole-to-optional-part dependence. -/
theorem optional_part_does_not_entail_strong_dependence :
    optionalHouse.RequiredCoverage .dwelling /\
      optionalHouse.OptionalPart .ornament .dwelling /\
      Not (optionalHouse.WholeDependsOnPart .ornament .dwelling) :=
  ⟨optional_house_has_required_coverage, ornament_is_optional,
    ornament_removal_does_not_break_the_house⟩

/-! ## A mere-collection countermodel -/

inductive CollectionPart where
  | beam
  | tile
  deriving DecidableEq, Repr

inductive CollectionWhole where
  | assemblage
  deriving DecidableEq, Repr

inductive CollectionFunction where
  | beamRole
  | tileRole
  deriving DecidableEq, Repr

open CollectionPart CollectionWhole CollectionFunction

/-- Both tokens are always present and have distinct functions.  Since no
context removes either token, static collection membership creates no
intervention dependence. -/
def staticCollection :
    Model CollectionPart CollectionWhole CollectionFunction Unit where
  member := fun _ _ => True
  contributes := fun part _ function =>
    match part, function with
    | .beam, .beamRole => True
    | .tile, .tileRole => True
    | _, _ => False
  required := fun _ _ => True
  partPresent := fun _ _ => true
  roleActive := fun _ _ _ => true
  functionActive := fun _ _ _ => true
  wholePresent := fun _ _ => true

theorem static_members_form_a_nontrivial_collection :
    staticCollection.MereCollection .assemblage :=
  ⟨.beam, .tile, by decide, trivial, trivial⟩

theorem static_members_share_common_identity :
    staticCollection.CommonIdentity .beam .tile .assemblage :=
  ⟨trivial, trivial, (), rfl, rfl, rfl⟩

theorem static_members_are_differentiated :
    staticCollection.DifferentiatedIdentity .beam .tile .assemblage := by
  exact ⟨static_members_share_common_identity, by decide,
    .beamRole, Or.inl ⟨trivial, by simp [staticCollection]⟩⟩

theorem static_collection_has_no_removal_dependence :
    Not (staticCollection.WholeDependsOnPart .beam .assemblage) := by
  rintro ⟨_, _, removal, _⟩
  exact Bool.noConfusion removal.2.1

theorem differentiated_collection_is_not_strongly_interpenetrating :
    Not (staticCollection.StrongInterpenetration
      .beam .tile .assemblage) :=
  staticCollection.differentiated_identity_excludes_strong_interpenetration
    static_members_are_differentiated

/-- The finite model has two genuine, differentiated members.  Mere
collection and common whole-forming status entail neither controlled-removal
dependence nor strong functional interpenetration. -/
theorem mere_collection_does_not_entail_dependence_or_interpenetration :
    staticCollection.MereCollection .assemblage /\
      staticCollection.CommonIdentity .beam .tile .assemblage /\
      staticCollection.DifferentiatedIdentity .beam .tile .assemblage /\
      Not (staticCollection.WholeDependsOnPart .beam .assemblage) /\
      Not (staticCollection.StrongInterpenetration
        .beam .tile .assemblage) :=
  ⟨static_members_form_a_nontrivial_collection,
    static_members_share_common_identity,
    static_members_are_differentiated,
    static_collection_has_no_removal_dependence,
    differentiated_collection_is_not_strongly_interpenetrating⟩

end BuddhistComparativeLogic.FazangMereology
