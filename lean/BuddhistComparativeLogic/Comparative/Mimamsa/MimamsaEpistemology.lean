/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.BeliefRevision
import BuddhistComparativeLogic.Comparative.Nyaya.Nyaya

/-!
# Defeasible qualification and distinct pramanas in a Bhāṭṭa Mīmāṃsā audit

This module isolates four proof-theoretic ideas in a Bhāṭṭa Mīmāṃsā,
Kumārila-oriented audit: a cognition's initial qualification before defeat,
later defeaters, postulation (`arthapatti`), and non-cognition
(`anupalabdhi`).  It is not an edition or a claim that every Mīmāṃsā school
accepts the same sources or gives the same account.  Initial qualification
below is an entitlement status, not truth by definition.  A separate bridge
is therefore required to derive truth from undefeated qualification.

Postulation is reconstructed by an explicit exhaustion and exclusion
certificate.  Its conclusion is checked through the repository's Nyaya
semantic-proof interface, but that extensional encoding does not identify
postulation historically with inference.  Likewise, the non-cognition result
reuses Dharmakirti's visibility schema only as a shared logical form; it does
not erase disagreements between Buddhist and Mīmāṃsā theories of pramāṇa.

Finally, a finite support model gives each of the six Bhāṭṭa sources its own
claim.  It is a consistency witness for source independence, not a historical
proof that these pramāṇas must have disjoint extensions in every epistemology.
-/

namespace BuddhistComparativeLogic.MimamsaEpistemology

universe u v

/-! ## Initial qualification, defeat, and truth -/

/-- The six sources represented here are the familiar Bhāṭṭa enumeration.
In particular, including non-cognition must not be read as attributing this
six-member list to every Mīmāṃsā school. -/
inductive BhattaPramana where
  | perception
  | inference
  | comparison
  | testimony
  | postulation
  | noncognition
  deriving DecidableEq, Repr

/-- A source-indexed cognition model.  Generation, prima-facie validity,
subsequent defeat, and truth at a state are four separate predicates. -/
structure EpistemicModel (State : Type u) (Claim : Type v) where
  generated : BhattaPramana → State → Claim → Prop
  primaFacieValid : BhattaPramana → State → Claim → Prop
  defeated : BhattaPramana → State → Claim → Prop
  trueAt : State → Claim → Prop

namespace EpistemicModel

variable {State : Type u} {Claim : Type v}
    (M : EpistemicModel State Claim)

/-- Initial qualification is the model's independent prima-facie status.  It
is not definitionally identical to generation, truth, or absence of defeat. -/
def InitiallyQualified (source : BhattaPramana) (state : State)
    (claim : Claim) :
    Prop :=
  M.primaFacieValid source state claim

/-- A proof object for the `svatah-pramanya` bridge used in this audit:
generation by a Bhāṭṭa source supplies prima-facie validity.  The bridge does
not assert truth and does not exclude later defeat. -/
structure SvatahPramanya : Prop where
  generatedIsPrimaFacieValid : ∀ {source state claim},
    M.generated source state claim →
      M.primaFacieValid source state claim

theorem initiallyQualified_of_generated (selfValidity : M.SvatahPramanya)
    {source : BhattaPramana} {state : State} {claim : Claim}
    (generated : M.generated source state claim) :
    M.InitiallyQualified source state claim :=
  selfValidity.generatedIsPrimaFacieValid generated

/-- A cognition is eligible after checking when it has prima-facie validity
and no defeater for that source-content pair is present. -/
def Undefeated (source : BhattaPramana) (state : State)
    (claim : Claim) : Prop :=
  M.primaFacieValid source state claim ∧
    ¬ M.defeated source state claim

theorem qualified_survives_without_defeater {source : BhattaPramana}
    {state : State} {claim : Claim}
    (qualified : M.InitiallyQualified source state claim)
    (notDefeated : ¬ M.defeated source state claim) :
    M.Undefeated source state claim :=
  ⟨qualified, notDefeated⟩

/-- The explicit reliability premise required to move from undefeated
entitlement to truth.  It is deliberately absent from `InitiallyQualified`. -/
structure TruthBridge : Prop where
  sound : ∀ {source state claim},
    M.Undefeated source state claim → M.trueAt state claim

theorem true_of_undefeated (bridge : M.TruthBridge)
    {source : BhattaPramana} {state : State} {claim : Claim}
    (warrant : M.Undefeated source state claim) :
    M.trueAt state claim :=
  bridge.sound warrant

end EpistemicModel

inductive AuditClaim where
  | accurate
  | sublated
  deriving DecidableEq, Repr

/-- A finite model in which a cognition is initially generated but later
defeated and false. -/
def sublationModel : EpistemicModel Unit AuditClaim where
  generated source _ claim :=
    source = .perception ∧ claim = .sublated
  primaFacieValid source _ claim :=
    source = .perception ∧ claim = .sublated
  defeated source _ claim :=
    source = .perception ∧ claim = .sublated
  trueAt _ claim := claim = .accurate

theorem sublation_svatah_pramanya : sublationModel.SvatahPramanya := by
  constructor
  intro source state claim generated
  exact generated

theorem initial_qualification_does_not_mean_indefeasible_truth :
    sublationModel.generated .perception () .sublated ∧
      sublationModel.InitiallyQualified .perception () .sublated ∧
      sublationModel.defeated .perception () .sublated ∧
      ¬ sublationModel.Undefeated .perception () .sublated ∧
      ¬ sublationModel.trueAt () .sublated := by
  simp [EpistemicModel.InitiallyQualified, EpistemicModel.Undefeated,
    sublationModel]

/-- Without a truth bridge, even the conjunction called `Undefeated` has no
semantic truth consequence in the unconstrained interface. -/
def untrackedModel : EpistemicModel Unit AuditClaim where
  generated _ _ _ := True
  primaFacieValid _ _ _ := True
  defeated _ _ _ := False
  trueAt _ claim := claim = .accurate

theorem undefeated_needs_truth_bridge :
    untrackedModel.Undefeated .testimony () .sublated ∧
      ¬ untrackedModel.trueAt () .sublated ∧
      ¬ untrackedModel.TruthBridge := by
  refine ⟨⟨trivial, by simp [untrackedModel]⟩,
    by simp [untrackedModel], ?_⟩
  intro bridge
  have falseTruth : ¬ untrackedModel.trueAt () .sublated := by
    simp [untrackedModel]
  exact falseTruth
    (bridge.sound (source := .testimony) (state := ()) (claim := .sublated)
      ⟨trivial, by simp [untrackedModel]⟩)

/-- Generation alone does not create prima-facie validity in the neutral
interface.  A `SvatahPramanya` bridge is a real premise rather than a theorem
of the bare `EpistemicModel` fields. -/
def generationOnlyModel : EpistemicModel Unit AuditClaim where
  generated source _ claim :=
    source = .perception ∧ claim = .sublated
  primaFacieValid _ _ _ := False
  defeated _ _ _ := False
  trueAt _ claim := claim = .accurate

theorem generation_alone_does_not_supply_initial_qualification :
    generationOnlyModel.generated .perception () .sublated ∧
      ¬ generationOnlyModel.InitiallyQualified .perception () .sublated ∧
      ¬ generationOnlyModel.Undefeated .perception () .sublated ∧
      ¬ generationOnlyModel.SvatahPramanya := by
  refine ⟨by simp [generationOnlyModel],
    by simp [EpistemicModel.InitiallyQualified, generationOnlyModel],
    by simp [EpistemicModel.Undefeated, generationOnlyModel], ?_⟩
  intro selfValidity
  exact selfValidity.generatedIsPrimaFacieValid
    (source := .perception) (state := ()) (claim := .sublated)
    (by simp [generationOnlyModel])

/-! ## The existing quantitative revision process as one defeater instance -/

open BuddhistComparativeLogic.BeliefRevision

/-- In the repository's score model, counterevidence defeats a positive
balance once it meets or exceeds own-being support.  This is an optional
instance of the abstract defeater idea, not a historical Mīmāṃsā equation. -/
def ScoreDefeated {State : Type u}
    (E : EvidenceProcess State) (state : State) : Prop :=
  E.ownSupport state ≤ E.emptinessEvidence state

theorem score_defeat_iff_zero_grasp {State : Type u}
    (E : EvidenceProcess State) (state : State) :
    ScoreDefeated E state ↔ E.grasp state = 0 := by
  exact (E.no_grasp_iff_evidence_sufficient state).symm

theorem score_undefeated_iff_accepts {State : Type u}
    (E : EvidenceProcess State) (state : State) :
    ¬ ScoreDefeated E state ↔ E.AcceptsOwnBeing state := by
  simp [ScoreDefeated, EvidenceProcess.AcceptsOwnBeing]

/-! ## Arthapatti as exhaustion plus exclusion -/

/-- An open postulation frame records an observation, a proposed postulate,
and a residual alternative.  `exhaustive` alone permits the residual branch;
it therefore does not yet establish the postulate. -/
structure ArthapattiFrame (World : Type u) where
  subject : World
  observed : World → Prop
  postulate : World → Prop
  residual : World → Prop
  exhaustive : ∀ world, observed world →
    postulate world ∨ residual world

namespace ArthapattiFrame

variable {World : Type u} (frame : ArthapattiFrame World)

/-- The ordinary unary argument used only to audit the certified conclusion. -/
def argument : BuddhistComparativeLogic.Hetucakra.Anumana World where
  paksa := frame.subject
  reason := frame.observed
  sadhya := frame.postulate

/-- A postulation certificate rules out the residual branch for every case
to which the observation applies. -/
structure Certificate : Prop where
  residualExcluded : ∀ world, frame.observed world →
    ¬ frame.residual world

namespace Certificate

variable {World : Type u} {frame : ArthapattiFrame World}

theorem pervasion (certificate : frame.Certificate) :
    BuddhistComparativeLogic.Nyaya.Pervasion frame.argument := by
  intro world observed
  rcases frame.exhaustive world observed with postulated | residual
  · exact postulated
  · exact False.elim (certificate.residualExcluded world observed residual)

/-- Turn the postulation certificate and the observed target into the same
two-premise semantic proof used by the public-inference module. -/
theorem toSemanticProof (certificate : frame.Certificate)
    (observed : frame.observed frame.subject) :
    BuddhistComparativeLogic.Nyaya.SemanticProof frame.argument where
  subjectReason := observed
  pervasion := certificate.pervasion

/-- Soundness of the explicit postulation reconstruction. -/
theorem sound (certificate : frame.Certificate)
    (observed : frame.observed frame.subject) :
    frame.postulate frame.subject := by
  exact certificate.toSemanticProof observed |>.sound

end Certificate

end ArthapattiFrame

inductive PostulationCase where
  | target
  | postulateOnly
  | residualOnly
  deriving DecidableEq, Repr

open PostulationCase

/-- A three-case family keeps observation, postulate, and residual extensions
distinct.  At the target, exhaustion branches on the open proposition
`claim`; a postulate-only case and a residual-only case keep both predicates
inhabited away from the observation. -/
def licensedFrame (claim : Prop) : ArthapattiFrame PostulationCase where
  subject := .target
  observed world := world = .target
  postulate world :=
    (world = .target ∧ claim) ∨ world = .postulateOnly
  residual world :=
    (world = .target ∧ ¬ claim) ∨ world = .residualOnly
  exhaustive := by
    intro world observed
    subst world
    rcases Classical.em claim with established | notEstablished
    · exact Or.inl (Or.inl ⟨rfl, established⟩)
    · exact Or.inr (Or.inl ⟨rfl, notEstablished⟩)

theorem certificate_of_claim {claim : Prop} (established : claim) :
    (licensedFrame claim).Certificate where
  residualExcluded := by
    intro world observed residual
    subst world
    simp [licensedFrame, established] at residual

/-- For this finite family, a certificate exists exactly when the target
claim holds.  The positive certificate is therefore proof-bearing rather than
an unused decoration on a frame whose observation already is its postulate. -/
theorem licensed_certificate_iff_claim (claim : Prop) :
    (licensedFrame claim).Certificate ↔ claim := by
  constructor
  · intro certificate
    have postulated := certificate.sound
      (by simp [licensedFrame])
    simpa [licensedFrame] using postulated
  · exact certificate_of_claim

theorem licensedCertificate : (licensedFrame True).Certificate :=
  certificate_of_claim trivial

/-- The positive example is nonvacuous and its extensions differ: observation
and conclusion hold at the target, a second case is postulated without being
observed, and a third residual case is neither observed nor postulated. -/
theorem licensed_postulation_nonvacuous :
    (licensedFrame True).observed (licensedFrame True).subject ∧
      (licensedFrame True).postulate (licensedFrame True).subject ∧
      (∃ world, (licensedFrame True).postulate world ∧
        ¬ (licensedFrame True).observed world) ∧
      (∃ world, (licensedFrame True).residual world ∧
        ¬ (licensedFrame True).observed world ∧
        ¬ (licensedFrame True).postulate world) := by
  refine ⟨by simp [licensedFrame],
    licensedCertificate.sound (by simp [licensedFrame]), ?_, ?_⟩
  · exact ⟨.postulateOnly, by simp [licensedFrame], by simp [licensedFrame]⟩
  · exact ⟨.residualOnly, by simp [licensedFrame],
      by simp [licensedFrame], by simp [licensedFrame]⟩

/-- This open frame leaves the residual branch true at the observed target. -/
def underdeterminedFrame : ArthapattiFrame PostulationCase :=
  licensedFrame False

/-- Observation and exhaustion do not imply the postulate when exclusion of
the residual alternative is missing.  The last conjunct proves that no closed
certificate can be manufactured for this finite frame. -/
theorem arthapatti_needs_residual_exclusion :
    underdeterminedFrame.observed underdeterminedFrame.subject ∧
      underdeterminedFrame.residual underdeterminedFrame.subject ∧
      ¬ underdeterminedFrame.postulate underdeterminedFrame.subject ∧
      ¬ underdeterminedFrame.Certificate := by
  refine ⟨by simp [underdeterminedFrame, licensedFrame],
    by simp [underdeterminedFrame, licensedFrame],
    by simp [underdeterminedFrame, licensedFrame], ?_⟩
  intro certificate
  exact (licensed_certificate_iff_claim False).mp certificate

/-! ## Anupalabdhi and its perceptibility boundary -/

/-- Reuse the existing visibility interface for the shared logical schema:
a present and perceptible item would be perceived. -/
abbrev NonCognitionModel (Object : Type u) :=
  BuddhistComparativeLogic.Dharmakirti.Anupalabdhi Object

theorem visible_noncognition_sound {Object : Type u}
    (model : NonCognitionModel Object) {object : Object}
    (perceptible : model.perceptible object)
    (notPerceived : ¬ model.perceived object) :
    ¬ model.present object :=
  model.drsyanupalabdhi_sound perceptible notPerceived

/-- The imported two-object model has an imperceptible, unperceived object
which is nevertheless present.  Thus non-cognition without perceptibility
does not prove absence. -/
theorem noncognition_needs_perceptibility :
    BuddhistComparativeLogic.Dharmakirti.here.present .ghost ∧
      ¬ BuddhistComparativeLogic.Dharmakirti.here.perceived .ghost ∧
      ¬ BuddhistComparativeLogic.Dharmakirti.here.perceptible .ghost ∧
      ¬ ((¬ BuddhistComparativeLogic.Dharmakirti.here.perceived .ghost) →
        ¬ BuddhistComparativeLogic.Dharmakirti.here.present .ghost) := by
  refine ⟨by simp [BuddhistComparativeLogic.Dharmakirti.here],
    by simp [BuddhistComparativeLogic.Dharmakirti.here],
    by simp [BuddhistComparativeLogic.Dharmakirti.here], ?_⟩
  intro absenceFromNoncognition
  exact absenceFromNoncognition
    (by simp [BuddhistComparativeLogic.Dharmakirti.here])
    (by simp [BuddhistComparativeLogic.Dharmakirti.here])

/-! ## A finite witness for Bhāṭṭa pramāṇa-source independence -/

/-- Source support profiles.  Equality of profiles is one deliberately strong
notion of reduction; the finite model below refutes its necessity. -/
structure SupportSystem (Claim : Type u) where
  supports : BhattaPramana → Claim → Prop

namespace SupportSystem

variable {Claim : Type u} (system : SupportSystem Claim)

def ReducibleTo (source target : BhattaPramana) : Prop :=
  ∀ claim, system.supports source claim ↔ system.supports target claim

def Separates (source target : BhattaPramana) : Prop :=
  ∃ claim, system.supports source claim ∧
    ¬ system.supports target claim

theorem not_reducible_of_separates {source target : BhattaPramana}
    (separation : system.Separates source target) :
    ¬ system.ReducibleTo source target := by
  rintro reduction
  rcases separation with ⟨claim, sourceSupport, noTargetSupport⟩
  exact noTargetSupport ((reduction claim).mp sourceSupport)

end SupportSystem

inductive SourceClaim where
  | seen
  | inferred
  | compared
  | reported
  | postulated
  | absent
  deriving DecidableEq, Repr

def sourceClaim : BhattaPramana → SourceClaim
  | .perception => .seen
  | .inference => .inferred
  | .comparison => .compared
  | .testimony => .reported
  | .postulation => .postulated
  | .noncognition => .absent

theorem sourceClaim_injective : Function.Injective sourceClaim := by
  intro left right equal
  cases left <;> cases right <;> simp_all [sourceClaim]

/-- Every source supports exactly its corresponding claim in this finite
consistency model. -/
def finiteSupport : SupportSystem SourceClaim where
  supports source claim := claim = sourceClaim source

theorem finite_sources_separate {source target : BhattaPramana}
    (distinct : source ≠ target) :
    finiteSupport.Separates source target := by
  refine ⟨sourceClaim source, rfl, ?_⟩
  intro equal
  exact distinct (sourceClaim_injective equal)

theorem finite_sources_not_reducible {source target : BhattaPramana}
    (distinct : source ≠ target) :
    ¬ finiteSupport.ReducibleTo source target :=
  finiteSupport.not_reducible_of_separates
    (finite_sources_separate distinct)

/-- All six support extensions are inhabited, while postulation is not
reducible to inference and non-cognition is not reducible to perception. -/
theorem finite_bhatta_pramana_independence_nonvacuous :
    (∀ source, ∃ claim, finiteSupport.supports source claim) ∧
      ¬ finiteSupport.ReducibleTo .postulation .inference ∧
      ¬ finiteSupport.ReducibleTo .noncognition .perception := by
  refine ⟨?_, finite_sources_not_reducible (by decide),
    finite_sources_not_reducible (by decide)⟩
  intro source
  exact ⟨sourceClaim source, rfl⟩

end BuddhistComparativeLogic.MimamsaEpistemology
