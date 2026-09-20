/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Yogacara.Sahopalambha

/-!
# Reflexive presentation, traces, and later memory

This module gives a bounded interface inspired by Dignaga-Dharmakirti
discussions of `svasamvedana`.  Episodes, presented objects, traces, and
memory tokens have different types.  Object presentation does not contain
self-presentation by definition: an explicit reflexivity certificate supplies
that step.  Trace formation, later retention, matching recall content, and
unique source attribution are further independent proof obligations.

The construction is not an edition of either author's texts and does not
claim that recollection is their only argument for reflexive awareness.  Its
later-memory relation is a small typed test bench.  In particular, complete
object/cognition co-apprehension still permits a model with no self-presented
episode, while equal recall output permits numerically distinct memory tokens
and an ambiguous source episode.

Source mapping (accessed 2026-09-19): the textual anchors are Dignāga,
*Pramāṇasamuccaya(vṛtti)* 1.6ab and 1.9–12, especially the recollection move
at 1.11c–d, in Ernst Steinkellner's revised 2014 hypothetical Sanskrit
reconstruction
(https://www.oeaw.ac.at/fileadmin/Institute/IKGA/PDF/digitales/dignaga_PS_1.pdf).
Chiara Mascarello, “Dignāga and Later Developments” (2025),
doi:10.30687/978-88-6969-929-0/003, supplies peer-reviewed orientation on
self-awareness, two aspects, and memory.  The module retains Sanskrit labels
but supplies its own English paraphrases.  `leavesTrace`, `carriesTrace`,
`laterThan`, and unique-source certificates are a modern typed decomposition;
they are not offered as translations of the cited verses.
-/

namespace BuddhistComparativeLogic.Svasamvedana

universe u v w z

/-! ## Four typed layers -/

/-- Raw episodic data.  None of the relations carries a law connecting it to
another field.  Those connections are stated in separate certificates below. -/
structure RecollectiveModel
    (Episode : Type u) (Object : Type v) (Trace : Type w) (Memory : Type z) where
  appearance : Episode -> Object
  nonconceptual : Object -> Prop
  selfPresented : Episode -> Prop
  leavesTrace : Episode -> Trace -> Prop
  carriesTrace : Memory -> Trace -> Prop
  laterThan : Memory -> Episode -> Prop
  recallOutput : Memory -> Object

namespace RecollectiveModel

variable {Episode : Type u} {Object : Type v}
    {Trace : Type w} {Memory : Type z}
    (M : RecollectiveModel Episode Object Trace Memory)

/-- A later memory is trace-attributed to an episode.  This definition does
not say that the source is unique. -/
def LaterSourceAttribution (memory : Memory) (episode : Episode) : Prop :=
  M.laterThan memory episode /\
    exists trace, M.leavesTrace episode trace /\ M.carriesTrace memory trace

/-- An exact source claim adds uniqueness to trace attribution. -/
def HasUniqueSource (memory : Memory) (episode : Episode) : Prop :=
  M.LaterSourceAttribution memory episode /\
    forall other, M.LaterSourceAttribution memory other -> other = episode

/-- Equal recalled content determines token identity only under this extra
extensionality principle. -/
def IdentityFromRecallOutput : Prop :=
  forall left right, M.recallOutput left = M.recallOutput right -> left = right

end RecollectiveModel

/-- The explicit step from nonconceptual object appearance to reflexive
presentation of the episode. -/
structure ReflexivityCertificate
    {Episode : Type u} {Object : Type v} {Trace : Type w} {Memory : Type z}
    (M : RecollectiveModel Episode Object Trace Memory) : Prop where
  reflexive : forall episode,
    M.nonconceptual (M.appearance episode) -> M.selfPresented episode

/-- Constructive data and laws for forming a trace and finding it in a later
memory.  `traceOf` and `memoryOf` are witnesses; the four proof fields remain
independent obligations. -/
structure TracePersistenceCertificate
    {Episode : Type u} {Object : Type v} {Trace : Type w} {Memory : Type z}
    (M : RecollectiveModel Episode Object Trace Memory) where
  traceOf : Episode -> Trace
  memoryOf : Episode -> Memory
  formation : forall episode, M.selfPresented episode ->
    M.leavesTrace episode (traceOf episode)
  retained : forall episode, M.selfPresented episode ->
    M.carriesTrace (memoryOf episode) (traceOf episode)
  later : forall episode, M.selfPresented episode ->
    M.laterThan (memoryOf episode) episode
  outputMatches : forall episode, M.selfPresented episode ->
    M.recallOutput (memoryOf episode) = M.appearance episode

/-- Conditions under which a shared retained trace identifies its episode.
This certificate is deliberately absent from the ambiguous model below. -/
structure TraceDiscrimination
    {Episode : Type u} {Object : Type v} {Trace : Type w} {Memory : Type z}
    (M : RecollectiveModel Episode Object Trace Memory) : Prop where
  sourceUnique : forall {left right trace},
    M.leavesTrace left trace -> M.leavesTrace right trace -> left = right
  memoryTraceUnique : forall {memory left right},
    M.carriesTrace memory left -> M.carriesTrace memory right -> left = right

/-! ## Positive conditional results -/

theorem object_presentation_yields_reflexivity_and_later_memory
    {Episode : Type u} {Object : Type v} {Trace : Type w} {Memory : Type z}
    {M : RecollectiveModel Episode Object Trace Memory}
    (reflexivity : ReflexivityCertificate M)
    (persistence : TracePersistenceCertificate M)
    (episode : Episode)
    (isNonconceptual : M.nonconceptual (M.appearance episode)) :
    M.selfPresented episode /\
      M.LaterSourceAttribution (persistence.memoryOf episode) episode /\
      M.recallOutput (persistence.memoryOf episode) = M.appearance episode := by
  have selfPresentation := reflexivity.reflexive episode isNonconceptual
  exact ⟨selfPresentation,
    ⟨persistence.later episode selfPresentation,
      ⟨persistence.traceOf episode,
        persistence.formation episode selfPresentation,
        persistence.retained episode selfPresentation⟩⟩,
    persistence.outputMatches episode selfPresentation⟩

theorem unique_source_of_trace_discrimination
    {Episode : Type u} {Object : Type v} {Trace : Type w} {Memory : Type z}
    {M : RecollectiveModel Episode Object Trace Memory}
    (discrimination : TraceDiscrimination M)
    {memory : Memory} {episode : Episode}
    (attribution : M.LaterSourceAttribution memory episode) :
    M.HasUniqueSource memory episode := by
  refine ⟨attribution, ?_⟩
  intro other otherAttribution
  rcases attribution.2 with ⟨episodeTrace, episodeLeaves, memoryCarriesEpisode⟩
  rcases otherAttribution.2 with
    ⟨otherTrace, otherLeaves, memoryCarriesOther⟩
  have tracesEqual : otherTrace = episodeTrace :=
    discrimination.memoryTraceUnique memoryCarriesOther memoryCarriesEpisode
  subst otherTrace
  exact discrimination.sourceUnique otherLeaves episodeLeaves

/-! ## Connection to the existing Pramanasamuccaya API -/

/-- Pairing the episode with its object prevents two episodes with the same
object from being silently identified by the adapter. -/
def toSelfAwarenessModel
    {Episode : Type u} {Object : Type v} {Trace : Type w} {Memory : Type z}
    (M : RecollectiveModel Episode Object Trace Memory)
    (certificate : ReflexivityCertificate M) :
    BuddhistComparativeLogic.Pramanasamuccaya.SelfAwarenessModel
      Episode (Episode × Object) where
  appearance episode := (episode, M.appearance episode)
  nonconceptual datum := M.nonconceptual datum.2
  aware datum := M.selfPresented datum.1
  reflexive := by
    intro episode nonconceptual
    exact certificate.reflexive episode nonconceptual

def episodeEvidence
    {Episode : Type u} {Object : Type v} {Trace : Type w} {Memory : Type z}
    {M : RecollectiveModel Episode Object Trace Memory}
    (certificate : ReflexivityCertificate M) (episode : Episode)
    (isNonconceptual : M.nonconceptual (M.appearance episode)) :
    BuddhistComparativeLogic.Pramanasamuccaya.PerceptualEvidence
      (toSelfAwarenessModel M certificate).toPerceptionModel episode where
  datum := (episode, M.appearance episode)
  presented := rfl
  nonconceptual := isNonconceptual

/-- The imported self-awareness theorem consumes the adapter's explicit
reflexivity law.  It does not derive that law from bare appearance. -/
theorem self_presentation_via_pramanasamuccaya
    {Episode : Type u} {Object : Type v} {Trace : Type w} {Memory : Type z}
    {M : RecollectiveModel Episode Object Trace Memory}
    (certificate : ReflexivityCertificate M) (episode : Episode)
    (isNonconceptual : M.nonconceptual (M.appearance episode)) :
    (toSelfAwarenessModel M certificate).aware
      (episode, M.appearance episode) :=
  BuddhistComparativeLogic.Pramanasamuccaya.self_awareness_of_explicit_model
    (toSelfAwarenessModel M certificate) episode
    (episodeEvidence certificate episode isNonconceptual)

/-! ## A finite positive model -/

inductive Episode where
  | blueSeeing
  | redSeeing
  deriving DecidableEq, Repr

inductive Object where
  | bluePatch
  | redPatch
  deriving DecidableEq, Repr

inductive Trace where
  | blueTrace
  | redTrace
  deriving DecidableEq, Repr

inductive Memory where
  | blueRecall
  | redRecall
  deriving DecidableEq, Repr

/-- Two fully inhabited paths keep episode, trace, and memory identity
distinct while preserving a one-to-one source relation. -/
def discriminatingMemory : RecollectiveModel Episode Object Trace Memory where
  appearance
    | .blueSeeing => .bluePatch
    | .redSeeing => .redPatch
  nonconceptual _ := True
  selfPresented _ := True
  leavesTrace episode trace :=
    (episode = .blueSeeing /\ trace = .blueTrace) \/
      (episode = .redSeeing /\ trace = .redTrace)
  carriesTrace memory trace :=
    (memory = .blueRecall /\ trace = .blueTrace) \/
      (memory = .redRecall /\ trace = .redTrace)
  laterThan memory episode :=
    (memory = .blueRecall /\ episode = .blueSeeing) \/
      (memory = .redRecall /\ episode = .redSeeing)
  recallOutput
    | .blueRecall => .bluePatch
    | .redRecall => .redPatch

theorem discriminatingReflexivity :
    ReflexivityCertificate discriminatingMemory where
  reflexive := by
    intro episode _nonconceptual
    trivial

def discriminatingPersistence :
    TracePersistenceCertificate discriminatingMemory where
  traceOf
    | .blueSeeing => .blueTrace
    | .redSeeing => .redTrace
  memoryOf
    | .blueSeeing => .blueRecall
    | .redSeeing => .redRecall
  formation := by
    intro episode _selfPresentation
    cases episode
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  retained := by
    intro episode _selfPresentation
    cases episode
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  later := by
    intro episode _selfPresentation
    cases episode
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  outputMatches := by
    intro episode _selfPresentation
    cases episode <;> rfl

theorem discriminatingTraceSources :
    TraceDiscrimination discriminatingMemory where
  sourceUnique := by
    intro left right trace leftLeaves rightLeaves
    cases left <;> cases right <;> cases trace <;>
      simp [discriminatingMemory] at leftLeaves rightLeaves ⊢
  memoryTraceUnique := by
    intro memory left right leftCarried rightCarried
    cases memory <;> cases left <;> cases right <;>
      simp [discriminatingMemory] at leftCarried rightCarried ⊢

theorem positive_blue_memory_is_nonvacuous :
    discriminatingMemory.selfPresented .blueSeeing /\
      discriminatingMemory.LaterSourceAttribution
        .blueRecall .blueSeeing /\
      discriminatingMemory.recallOutput .blueRecall = .bluePatch /\
      discriminatingMemory.HasUniqueSource .blueRecall .blueSeeing := by
  have result := object_presentation_yields_reflexivity_and_later_memory
    discriminatingReflexivity discriminatingPersistence .blueSeeing trivial
  refine ⟨result.1, result.2.1, result.2.2, ?_⟩
  exact unique_source_of_trace_discrimination
    discriminatingTraceSources result.2.1

theorem positive_model_contains_two_distinct_paths :
    discriminatingMemory.LaterSourceAttribution
        .blueRecall .blueSeeing /\
      discriminatingMemory.LaterSourceAttribution
        .redRecall .redSeeing /\
      (.blueSeeing : Episode) ≠ .redSeeing /\
      (.blueRecall : Memory) ≠ .redRecall := by
  refine ⟨positive_blue_memory_is_nonvacuous.2.1, ?_, by decide, by decide⟩
  exact (object_presentation_yields_reflexivity_and_later_memory
    discriminatingReflexivity discriminatingPersistence .redSeeing trivial).2.1

/-! ## Complete co-apprehension still lacks a reflexivity bridge -/

inductive SilentTrace where
  | trace
  deriving DecidableEq, Repr

inductive SilentMemory where
  | recall
  deriving DecidableEq, Repr

/-- This episode presents the same object used by the existing complete
co-apprehension model, but its self-presentation predicate is empty. -/
def coapprehendedWithoutSelf : RecollectiveModel
    BuddhistComparativeLogic.Sahopalambha.CoupledCognition
    BuddhistComparativeLogic.Sahopalambha.CoupledObject SilentTrace SilentMemory where
  appearance _ := .bluePatch
  nonconceptual _ := True
  selfPresented _ := False
  leavesTrace _ _ := False
  carriesTrace _ _ := False
  laterThan _ _ := False
  recallOutput _ := .bluePatch

/-- The old model supplies constant co-apprehension and the two object
conditions; the new episode supplies nonconceptual object presentation while
self-presentation remains false. -/
theorem complete_coapprehension_and_object_cognition_do_not_force_self_presentation :
    BuddhistComparativeLogic.Sahopalambha.coupledModel.ConstantCoapprehension
        .bluePatch .visualAwareness /\
      BuddhistComparativeLogic.Sahopalambha.coupledModel.toAlambanaModel.IsAlambana
        .bluePatch .visualAwareness /\
      coapprehendedWithoutSelf.appearance .visualAwareness = .bluePatch /\
      coapprehendedWithoutSelf.nonconceptual .bluePatch /\
      (¬ coapprehendedWithoutSelf.selfPresented .visualAwareness) := by
  exact ⟨BuddhistComparativeLogic.Sahopalambha.coupled_constant_coapprehension,
    BuddhistComparativeLogic.Sahopalambha.coapprehended_alambana_still_lacks_identity.1,
    rfl, trivial, fun selfPresentation => selfPresentation⟩

theorem coapprehension_model_has_no_reflexivity_certificate :
    ¬ ReflexivityCertificate coapprehendedWithoutSelf := by
  intro certificate
  exact complete_coapprehension_and_object_cognition_do_not_force_self_presentation.2.2.2.2
    (certificate.reflexive .visualAwareness trivial)

/-! ## Equal memory output underdetermines token and source identity -/

inductive AmbiguousEpisode where
  | first
  | second
  deriving DecidableEq, Repr

inductive AmbiguousObject where
  | patch
  deriving DecidableEq, Repr

inductive AmbiguousTrace where
  | shared
  deriving DecidableEq, Repr

inductive AmbiguousMemory where
  | firstRecall
  | secondRecall
  deriving DecidableEq, Repr

/-- Two distinct episodes deposit one shared trace.  Both later memory tokens
carry it and return the same object. -/
def ambiguousMemory : RecollectiveModel AmbiguousEpisode AmbiguousObject
    AmbiguousTrace AmbiguousMemory where
  appearance _ := .patch
  nonconceptual _ := True
  selfPresented _ := True
  leavesTrace _ _ := True
  carriesTrace _ _ := True
  laterThan _ _ := True
  recallOutput _ := .patch

theorem each_episode_is_a_source_of_the_same_later_memory :
    ambiguousMemory.LaterSourceAttribution .firstRecall .first /\
      ambiguousMemory.LaterSourceAttribution .firstRecall .second :=
  ⟨⟨trivial, ⟨.shared, trivial, trivial⟩⟩,
    ⟨trivial, ⟨.shared, trivial, trivial⟩⟩⟩

theorem first_recall_has_no_unique_source :
    ¬ exists episode,
      ambiguousMemory.HasUniqueSource .firstRecall episode := by
  rintro ⟨episode, _attribution, unique⟩
  cases episode with
  | first =>
      have equality := unique .second
        each_episode_is_a_source_of_the_same_later_memory.2
      exact AmbiguousEpisode.noConfusion equality
  | second =>
      have equality := unique .first
        each_episode_is_a_source_of_the_same_later_memory.1
      exact AmbiguousEpisode.noConfusion equality

/-- Equal outputs fail to determine both numerical identity of the memory
tokens and a unique source episode. -/
theorem same_memory_output_does_not_determine_identity_or_source :
    ambiguousMemory.LaterSourceAttribution .firstRecall .first /\
      ambiguousMemory.LaterSourceAttribution .secondRecall .second /\
      ambiguousMemory.recallOutput .firstRecall =
        ambiguousMemory.recallOutput .secondRecall /\
      (.firstRecall : AmbiguousMemory) ≠ .secondRecall /\
      (¬ ambiguousMemory.IdentityFromRecallOutput) /\
      (¬ exists episode,
        ambiguousMemory.HasUniqueSource .firstRecall episode) := by
  refine ⟨each_episode_is_a_source_of_the_same_later_memory.1,
    ⟨trivial, ⟨.shared, trivial, trivial⟩⟩, rfl, by decide, ?_,
    first_recall_has_no_unique_source⟩
  intro outputIdentity
  have tokenIdentity := outputIdentity .firstRecall .secondRecall rfl
  exact AmbiguousMemory.noConfusion tokenIdentity

end BuddhistComparativeLogic.Svasamvedana
