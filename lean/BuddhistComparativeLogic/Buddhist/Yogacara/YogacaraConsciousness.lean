/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Yogacara.YogacaraSynthesis

/-!
# Eight consciousnesses as functional roles

This module represents the eight-consciousness taxonomy by eight role labels:
five sensory roles, mental cognition, afflicted mind, and store consciousness.
The labels do not introduce eight substances.  Activity, presentation, and
support are separate predicates on the labels, and distinct roles may be
realized by the same bearer.

Store support is likewise an explicit process assumption.  The taxonomy, the
occurrence of a cognition, and even simultaneous activity of all eight roles
do not by themselves entail a store-support relation or permanent store
activity.  The final bridge to the three-nature interface states separately
when mental presentation together with afflicted appropriation counts as
projected subject/object duality.
-/

namespace BuddhistComparativeLogic.YogacaraConsciousness

open BuddhistComparativeLogic.YogacaraSynthesis

/-! ## Exact finite taxonomy -/

inductive SenseFaculty where
  | eye
  | ear
  | nose
  | tongue
  | body
  deriving DecidableEq, Repr

/-- Eight functional roles.  `sensory` contributes five constructors through
its `SenseFaculty` argument. -/
inductive ConsciousnessRole where
  | sensory (faculty : SenseFaculty)
  | mental
  | afflictedMind
  | store
  deriving DecidableEq, Repr

open SenseFaculty ConsciousnessRole

def allConsciousnessRoles : List ConsciousnessRole :=
  [.sensory .eye, .sensory .ear, .sensory .nose, .sensory .tongue,
    .sensory .body, .mental, .afflictedMind, .store]

/-- The displayed taxonomy is exhaustive, duplicate-free, and has exactly
eight entries. -/
theorem eight_roles_exact :
    (∀ role : ConsciousnessRole, role ∈ allConsciousnessRoles) ∧
      allConsciousnessRoles.Nodup ∧
      allConsciousnessRoles.length = 8 := by
  constructor
  · intro role
    cases role with
    | sensory faculty =>
        cases faculty <;> simp [allConsciousnessRoles]
    | mental => simp [allConsciousnessRoles]
    | afflictedMind => simp [allConsciousnessRoles]
    | store => simp [allConsciousnessRoles]
  · decide

def nonStoreRoles : List ConsciousnessRole :=
  [.sensory .eye, .sensory .ear, .sensory .nose, .sensory .tongue,
    .sensory .body, .mental, .afflictedMind]

/-- The seven roles other than store consciousness.  This structural
complement does not decide which roles a historical source calls manifest or
subliminal. -/
def NonStore (role : ConsciousnessRole) : Prop := role ≠ .store

theorem seven_nonstore_roles_exact :
    nonStoreRoles.Nodup ∧ nonStoreRoles.length = 7 ∧
      (∀ role, role ∈ nonStoreRoles ↔ NonStore role) := by
  refine ⟨by decide, by decide, ?_⟩
  intro role
  cases role with
  | sensory faculty =>
      cases faculty <;> simp [nonStoreRoles, NonStore]
  | mental => simp [nonStoreRoles, NonStore]
  | afflictedMind => simp [nonStoreRoles, NonStore]
  | store => simp [nonStoreRoles, NonStore]

/-! A role distinction is not a bearer distinction. -/

def unitBearer (_ : ConsciousnessRole) : Unit := ()

theorem functional_roles_do_not_force_distinct_substances :
    ¬ Function.Injective unitBearer := by
  intro injective
  have equalBearers :
      unitBearer (.sensory .eye) = unitBearer (.sensory .ear) := rfl
  have equalRoles := injective equalBearers
  exact (by decide :
    ConsciousnessRole.sensory .eye ≠
      ConsciousnessRole.sensory .ear) equalRoles

/-! ## Activity, presentation, and store support -/

/-- A functional process records which roles operate and which contents they
present.  Presentation requires activity, but the record contains no bearer
or persistence field. -/
structure FunctionalProcess (Stage : Type u) (Content : Type v) where
  active : ConsciousnessRole → Stage → Prop
  presents : ConsciousnessRole → Content → Stage → Prop
  presentationActive : ∀ {role content stage},
    presents role content stage → active role stage

/-- A support process adds only a directed support relation.  Its first
argument is the supporting role and its second is the supported role. -/
structure SupportProcess (Stage : Type u) (Content : Type v)
    extends FunctionalProcess Stage Content where
  supports : ConsciousnessRole → ConsciousnessRole → Stage → Prop

namespace SupportProcess

variable (process : SupportProcess Stage Content)

/-- An explicit ālaya-support premise for every non-store role.  Quantifying
over all seven non-store roles is a chosen interface condition, not a claim
that every Yogācāra source classifies afflicted mind as manifest. -/
def StoreSupportsNonStore : Prop :=
  ∀ role stage, NonStore role → process.active role stage →
    process.active .store stage ∧ process.supports .store role stage

/-- Permanent store activity is a further functional claim.  Even this says
nothing about numerical identity of an underlying bearer. -/
def StorePermanentlyActive : Prop :=
  ∀ stage, process.active .store stage

/-- A non-store presentation has distinct store support when, and only in this
theorem, the all-non-store support premise is supplied. -/
theorem nonstore_presentation_has_distinct_store_support
    (storeSupport : process.StoreSupportsNonStore)
    {role : ConsciousnessRole} (nonStore : NonStore role)
    {content : Content} {stage : Stage}
    (presentation : process.presents role content stage) :
    ∃ supporter : ConsciousnessRole,
      supporter = .store ∧ supporter ≠ role ∧
        process.active supporter stage ∧
        process.supports supporter role stage := by
  have active := process.presentationActive presentation
  have support := storeSupport role stage nonStore active
  refine ⟨.store, rfl, ?_, support⟩
  intro equal
  exact nonStore equal.symm

end SupportProcess

/-! ## Finite omission model -/

/-- At the first Boolean stage every role is active and presents the sole
content.  At the second no role is active.  No role supports another. -/
def episodicUnsupported : SupportProcess Bool Unit where
  active _ stage := stage = false
  presents _ _ stage := stage = false
  presentationActive := by
    intro role content stage presentation
    exact presentation
  supports _ _ _ := False

/-- Even activity of all eight roles and an actual mental presentation do not
supply the store-support law.  Activity of the store at one stage also does
not make it permanently active. -/
theorem taxonomy_and_activity_do_not_imply_support_or_permanence :
    (∀ role, episodicUnsupported.active role false) ∧
      episodicUnsupported.presents .mental () false ∧
      ¬ episodicUnsupported.StoreSupportsNonStore ∧
      episodicUnsupported.active .store false ∧
      ¬ episodicUnsupported.StorePermanentlyActive := by
  refine ⟨fun _ => rfl, rfl, ?_, rfl, ?_⟩
  · intro storeSupport
    have support := storeSupport .mental false (by simp [NonStore]) rfl
    exact support.2
  · intro permanent
    have activeLater := permanent true
    simp [episodicUnsupported] at activeLater

/-- The same model gives an explicit non-store cognition with no distinct
store supporter. -/
theorem nonstore_cognition_without_support_premise_has_no_store_support :
    episodicUnsupported.presents .mental () false ∧
      NonStore .mental ∧
      ¬ ∃ supporter : ConsciousnessRole,
        supporter = .store ∧ supporter ≠ .mental ∧
          episodicUnsupported.active supporter false ∧
          episodicUnsupported.supports supporter .mental false := by
  refine ⟨rfl, by simp [NonStore], ?_⟩
  rintro ⟨supporter, _, _, _, support⟩
  exact support

/-! ## A stated bridge to projected duality -/

/-- A minimal functional reconstruction of a subject/object episode: mental
cognition presents a content while afflicted mind is active. -/
def SubjectObjectEpisode (process : FunctionalProcess Stage Content)
    (content : Content) (stage : Stage) : Prop :=
  process.presents .mental content stage ∧
    process.active .afflictedMind stage

/-- The connection from functional coactivity to the imagined nature is kept
as an explicit bridge because neither the eight labels nor activity alone
contains semantic information about projection. -/
def ProjectionBridge (process : FunctionalProcess Stage Content)
    (analysis : Trisvabhava Phenomenon)
    (eventOf : Content → Stage → Phenomenon) : Prop :=
  ∀ content stage, SubjectObjectEpisode process content stage →
    analysis.projectedDuality (eventOf content stage)

theorem projection_bridge_yields_imagined
    (process : FunctionalProcess Stage Content)
    (analysis : Trisvabhava Phenomenon)
    (eventOf : Content → Stage → Phenomenon)
    (bridge : ProjectionBridge process analysis eventOf)
    {content : Content} {stage : Stage}
    (episode : SubjectObjectEpisode process content stage) :
    analysis.Holds .imagined (eventOf content stage) := by
  exact bridge content stage episode

def unprojectedUnit : Trisvabhava Unit where
  dependent _ := True
  projectedDuality _ := False
  suchness _ := True
  suchness_iff := by simp

/-- A finite model with mental presentation and afflicted-mind activity but
no projected duality shows why `ProjectionBridge` is a substantive premise. -/
theorem coactivity_alone_does_not_force_projected_duality :
    SubjectObjectEpisode episodicUnsupported.toFunctionalProcess () false ∧
      ¬ unprojectedUnit.Holds .imagined () := by
  constructor
  · exact ⟨rfl, rfl⟩
  · simp [Trisvabhava.Holds, unprojectedUnit]

end BuddhistComparativeLogic.YogacaraConsciousness
