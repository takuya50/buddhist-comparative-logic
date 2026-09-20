/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceModes
import BuddhistComparativeLogic.Buddhist.HeartSutra.AssumptionAudit

/-!
# Relations and reified connectors

This module provides a bounded formal audit motivated by arguments about
relations in Dharmakirti's *Sambandhapariksa*.  An ordinary binary relation is
a `Prop`-valued predicate.  A reified connector instead belongs to a separate
type and has endpoints.  The two kinds of data are independent until an
explicit representation bridge is supplied.

Two stronger consequences are kept conditional.  Related endpoints collapse
to equality from the explicit premise that a connector is identical with both
of them.  Given an active starting connector, the stated closure law yields a
hierarchy with a higher active connector at a strictly greater level for each
active connector.  Finite models show that bare relation data or bare
reification implies neither bridge, collapse, nor regress.  These interfaces
do not claim to reproduce every textual argument about `sambandha`.
-/

namespace BuddhistComparativeLogic.Sambandhapariksa

/-! ## Binary relations and connector presentations -/

/-- Ordinary relation data and reified connector data are separate fields. -/
structure Presentation (D : Type u) (C : Type v) where
  relates : D -> D -> Prop
  active : C -> Prop
  leftEndpoint : C -> D
  rightEndpoint : C -> D

namespace Presentation

variable {D : Type u} {C : Type v} (model : Presentation D C)

/-- A connector represents an ordered pair when it is active and its two
stored endpoints agree with that pair. -/
def Represents (connector : C) (left right : D) : Prop :=
  model.active connector ∧
    model.leftEndpoint connector = left ∧
    model.rightEndpoint connector = right

/-- An explicit bridge equates ordinary relatedness with the existence of a
representing connector.  It is additional structure, not part of
`Presentation`. -/
def RepresentationBridge : Prop :=
  forall left right,
    model.relates left right <->
      exists connector, model.Represents connector left right

theorem connector_implies_relation (bridge : model.RepresentationBridge)
    {connector : C} {left right : D}
    (represented : model.Represents connector left right) :
    model.relates left right :=
  (bridge left right).mpr ⟨connector, represented⟩

theorem relation_has_connector (bridge : model.RepresentationBridge)
    {left right : D} (related : model.relates left right) :
    exists connector, model.Represents connector left right :=
  (bridge left right).mp related

end Presentation

inductive Endpoint where
  | left
  | right
  deriving DecidableEq, Repr

open Endpoint

/-- A relation may hold even when the connector type has no inhabitants. -/
def ordinaryOnly : Presentation Endpoint Empty where
  relates := fun x y => x = .left ∧ y = .right
  active := fun connector => nomatch connector
  leftEndpoint := fun connector => nomatch connector
  rightEndpoint := fun connector => nomatch connector

theorem ordinary_relation_does_not_supply_a_connector :
    ordinaryOnly.relates .left .right ∧
      ¬ (exists connector,
        ordinaryOnly.Represents connector .left .right) := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rintro ⟨connector, _⟩
  exact nomatch connector

/-- Conversely, an active connector and its endpoints need not make the
ordinary relation true when no bridge has been postulated. -/
def connectorOnly : Presentation Endpoint Unit where
  relates := fun _ _ => False
  active := fun _ => True
  leftEndpoint := fun _ => .left
  rightEndpoint := fun _ => .right

theorem connector_does_not_supply_the_relation :
    connectorOnly.Represents () .left .right ∧
      ¬ connectorOnly.relates .left .right := by
  exact ⟨⟨trivial, rfl, rfl⟩, fun failure => failure⟩

/-- The two finite directions jointly refute an implicit equivalence between
ordinary relation data and reified connector data. -/
theorem bridge_is_an_additional_assumption :
    ¬ ordinaryOnly.RepresentationBridge ∧
      ¬ connectorOnly.RepresentationBridge := by
  constructor
  · intro bridge
    obtain ⟨connector, _⟩ :=
      ordinaryOnly.relation_has_connector bridge
        ordinary_relation_does_not_supply_a_connector.1
    exact nomatch connector
  · intro bridge
    exact connector_does_not_supply_the_relation.2
      (connectorOnly.connector_implies_relation bridge
        connector_does_not_supply_the_relation.1)

/-- A singleton connector can also present exactly one genuine ordinary
relation when an explicit bridge is verified. -/
def linkedPresentation : Presentation Endpoint Unit where
  relates := fun x y => x = .left ∧ y = .right
  active := fun _ => True
  leftEndpoint := fun _ => .left
  rightEndpoint := fun _ => .right

theorem linked_presentation_bridge :
    linkedPresentation.RepresentationBridge := by
  intro x y
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨(), trivial, rfl, rfl⟩
  · rintro ⟨connector, _, leftEquation, rightEquation⟩
    exact ⟨leftEquation.symm, rightEquation.symm⟩

/-! ## Identity collapse from endpoint-identification assumptions -/

/-- Here connectors and endpoints deliberately share one carrier so that an
identity claim between them can be stated. -/
structure Reified (D : Type u) where
  relates : D -> D -> Prop
  connector : D -> D -> D

namespace Reified

variable {D : Type u} (model : Reified D)

/-- The strong reduction that identifies a connector with both endpoints of
every related pair. -/
def EndpointIdentity : Prop :=
  forall left right, model.relates left right ->
    model.connector left right = left ∧
    model.connector left right = right

/-- Collapse follows from the explicit double identity. -/
theorem related_endpoints_equal (identity : model.EndpointIdentity)
    {left right : D} (related : model.relates left right) : left = right := by
  have equations := identity left right related
  exact equations.1.symm.trans equations.2

end Reified

inductive Entity where
  | left
  | right
  | link
  deriving DecidableEq, Repr

/-- A distinct link reifies one non-reflexive related pair. -/
def distinctLink : Reified Entity where
  relates := fun x y => x = .left ∧ y = .right
  connector := fun _ _ => .link

theorem reification_does_not_collapse_endpoints :
    distinctLink.relates .left .right ∧
      distinctLink.connector .left .right = .link ∧
      Entity.left ≠ Entity.right ∧
      ¬ distinctLink.EndpointIdentity := by
  refine ⟨⟨rfl, rfl⟩, rfl, by decide, ?_⟩
  intro identity
  have collapsed : Entity.left = Entity.right :=
    distinctLink.related_endpoints_equal identity ⟨rfl, rfl⟩
  cases collapsed

/-! ## Regress from an explicit higher-connector closure law -/

/-- Iterate a proposed higher-connector operation. -/
def iterateConnector {C : Type u} (next : C -> C) : Nat -> C -> C
  | 0, connector => connector
  | n + 1, connector => next (iterateConnector next n connector)

/-- A strong regress law: every active connector has an active successor at
the next natural-number level.  The level increase, rather than reification
alone, rules out finite cycling. -/
structure RegressLaw {D : Type u} {C : Type v}
    (model : Presentation D C) where
  next : C -> C
  level : C -> Nat
  nextActive : forall connector,
    model.active connector -> model.active (next connector)
  levelStep : forall connector, model.active connector ->
    level (next connector) = level connector + 1

namespace RegressLaw

variable {D : Type u} {C : Type v} {model : Presentation D C}
    (law : RegressLaw model)

theorem iterate_active {connector : C} (active : model.active connector) :
    forall n, model.active (iterateConnector law.next n connector) := by
  intro n
  induction n with
  | zero => exact active
  | succ n inductionHypothesis =>
      exact law.nextActive _ inductionHypothesis

theorem iterate_level {connector : C} (active : model.active connector) :
    forall n,
      law.level (iterateConnector law.next n connector) =
        law.level connector + n := by
  intro n
  induction n with
  | zero => simp [iterateConnector]
  | succ n inductionHypothesis =>
      rw [iterateConnector, law.levelStep _ (law.iterate_active active n),
        inductionHypothesis]
      simp [Nat.add_assoc]

/-- Under the stated closure law, every requested level offset is witnessed
by an active connector. -/
theorem hierarchy_unbounded {connector : C}
    (active : model.active connector) (n : Nat) :
    exists higher,
      model.active higher ∧
      law.level higher = law.level connector + n := by
  exact ⟨iterateConnector law.next n connector,
    law.iterate_active active n, law.iterate_level active n⟩

end RegressLaw

/-- Even a singleton presentation with a verified representation bridge is
nonempty and represents a genuine relation, but it cannot support a strictly
level-increasing closure law. -/
theorem finite_reification_does_not_force_regress :
    linkedPresentation.RepresentationBridge ∧
      linkedPresentation.relates .left .right ∧
      linkedPresentation.Represents () .left .right ∧
      ¬ Nonempty (RegressLaw linkedPresentation) := by
  refine ⟨linked_presentation_bridge, ⟨rfl, rfl⟩,
    ⟨trivial, rfl, rfl⟩, ?_⟩
  rintro ⟨law⟩
  have impossible := law.levelStep () trivial
  have sameSuccessor : law.next () = () := Subsingleton.elim _ _
  rw [sameSuccessor] at impossible
  exact (Nat.ne_of_lt (Nat.lt_succ_self (law.level ()))) impossible

/-! ## Dependence and own-being remain separately audited -/

open BuddhistComparativeLogic.DependenceModes

/-- A two-token finite model in which availability of a connector changes a
relation claim only in the conceptual mode.  Other modes are constant.
Own-being remains a parameter, so the dependence edge cannot decide it by
definition. -/
inductive Artifact where
  | relationClaim
  | connector
  deriving DecidableEq, Repr

def presentationDependence (own : Artifact -> Prop) :
    BuddhistComparativeLogic.DependenceModes.Model Artifact where
  Context := fun _ => Bool
  support := fun mode context artifact =>
    match mode, artifact with
    | .conceptual, .connector => context
    | _, _ => false
  manifest := fun mode context artifact =>
    match mode, artifact with
    | .conceptual, .relationClaim => context
    | _, _ => false
  own := own

theorem conceptual_presentation_edge (own : Artifact -> Prop) :
    (presentationDependence own).DependsAt .conceptual
      .connector .relationClaim := by
  refine ⟨by decide, false, true, ?_, ?_, ?_⟩
  · simp [presentationDependence]
  · intro artifact notConnector
    cases artifact <;> simp_all [presentationDependence]
  · simp [presentationDependence]

/-- The generic dependence API derives absence of own-being only from a
separately supplied invariance criterion. -/
theorem relation_claim_not_own_of_invariance (own : Artifact -> Prop)
    (criterion :
      (presentationDependence own).InvariantOwnAt .conceptual) :
    ¬ own .relationClaim := by
  exact (presentationDependence own).empty_of_mode_dependency .conceptual
    criterion (conceptual_presentation_edge own)

def artifactOwn : Artifact -> Prop := fun artifact => artifact = .connector

abbrev concretePresentationDependence := presentationDependence artifactOwn

theorem presentation_own_criterion :
    concretePresentationDependence.InvariantOwnAt .conceptual := by
  intro artifact own c d
  cases artifact <;> simp_all [concretePresentationDependence,
    presentationDependence, artifactOwn]

/-- The dependence edge projects to the generic `AssumptionAudit` API.  The
absence of own-being follows only after supplying the separate invariance
criterion. -/
theorem presentation_dependence_nonvacuous :
    concretePresentationDependence.DependsAt .conceptual
        .connector .relationClaim ∧
      (concretePresentationDependence.toDependenceAt .conceptual).arisen
        .relationClaim ∧
      ¬ concretePresentationDependence.own .relationClaim ∧
      concretePresentationDependence.own .connector := by
  refine ⟨conceptual_presentation_edge artifactOwn,
    ⟨.connector, conceptual_presentation_edge artifactOwn⟩, ?_, rfl⟩
  exact relation_claim_not_own_of_invariance artifactOwn
    presentation_own_criterion

/-- The mode tag carries information: the witnessed conceptual edge is not a
causal dependence edge in the same finite model. -/
theorem conceptual_dependence_does_not_imply_causal_dependence :
    concretePresentationDependence.DependsAt .conceptual
        .connector .relationClaim ∧
      ¬ concretePresentationDependence.DependsAt .causal
        .connector .relationClaim := by
  refine ⟨conceptual_presentation_edge artifactOwn, ?_⟩
  rintro ⟨_, c, d, _, _, changes⟩
  exact changes rfl

/-- The very same conceptual edge is compatible with assigning own-being to
both artifacts when the invariance criterion is absent. -/
def allArtifactsOwn : Artifact -> Prop := fun _ => True

theorem local_dependence_without_invariance_keeps_own :
    (presentationDependence allArtifactsOwn).DependsAt .conceptual
        .connector .relationClaim ∧
      (presentationDependence allArtifactsOwn).own .relationClaim ∧
      ¬ (presentationDependence allArtifactsOwn).InvariantOwnAt
        .conceptual := by
  refine ⟨conceptual_presentation_edge allArtifactsOwn, trivial, ?_⟩
  intro criterion
  exact relation_claim_not_own_of_invariance allArtifactsOwn criterion trivial

/-- Reuse the independent assumption audit: even universal non-self
dependence does not refute own-being without an exclusion bridge. -/
theorem dependence_alone_does_not_refute_own :
    BuddhistComparativeLogic.AssumptionAudit.dependentOwn.UniversalArising ∧
      ¬ BuddhistComparativeLogic.AssumptionAudit.dependentOwn.emptyOf false :=
  BuddhistComparativeLogic.AssumptionAudit.universal_arising_without_exclusion

end BuddhistComparativeLogic.Sambandhapariksa
