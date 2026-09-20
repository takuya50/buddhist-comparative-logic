/- SPDX-License-Identifier: Apache-2.0 -/

import Std

/-!
# A two-condition reconstruction of the Alambanapariksa

This module isolates a small argument form associated with Dignaga's
*Alambanapariksa*.  It is a text-bounded reconstruction, not a claim that the
Lean predicates exhaust the historical notions.  An intentional object
(`alambana`) for one cognition must satisfy two separately supplied
conditions: it causally produces that cognition, and it resembles the image
presented in that cognition.

The proposed external object is then divided into two proxy candidates.  An
atom collection can supply causal contributors while failing to resemble the
unitary image; a composite whole can resemble the image while failing to be
an additional causal entity.  `TwoHornFailure` records those disputed bridge
premises explicitly.  The exclusion theorem follows only after both are
given.

Concrete inhabited models audit the argument's scope.  They show that either condition
can hold without the conjunction, and that failure to be the intentional
object of a particular cognition is compatible with external existence.
Consequently, the two-horn result by itself does not prove that there are no
external things, nor the minimal global-idealism proxy used below.
-/

namespace BuddhistComparativeLogic.Alambanapariksa

universe u v w

/-! ## Intentional objects require two conditions -/

/-- A deliberately minimal object/cognition interface.  `causallyProduces`
and `imageSimilar` are primitive predicates here: the reconstruction does not
derive either one from the other or identify similarity with equality. -/
structure Model (Object : Type u) (Cognition : Type v) where
  causallyProduces : Object -> Cognition -> Prop
  imageSimilar : Object -> Cognition -> Prop

namespace Model

variable {Object : Type u} {Cognition : Type v}

/-- The reconstructed two-condition test for being the intentional object of
one cognition.  This conjunction is the module's explicit proxy for the
historical object-condition, not a philological definition of `alambana`. -/
def IsAlambana (model : Model Object Cognition)
    (object : Object) (cognition : Cognition) : Prop :=
  model.causallyProduces object cognition /\
    model.imageSimilar object cognition

theorem alambana_causally_produces {model : Model Object Cognition}
    {object : Object} {cognition : Cognition}
    (isObject : model.IsAlambana object cognition) :
    model.causallyProduces object cognition :=
  isObject.1

theorem alambana_is_image_similar {model : Model Object Cognition}
    {object : Object} {cognition : Cognition}
    (isObject : model.IsAlambana object cognition) :
    model.imageSimilar object cognition :=
  isObject.2

/-- Supplying the two conditions separately is sufficient for the local
reconstructed predicate; no further ontological conclusion is built in. -/
theorem alambana_of_cause_and_similarity {model : Model Object Cognition}
    {object : Object} {cognition : Cognition}
    (cause : model.causallyProduces object cognition)
    (similarity : model.imageSimilar object cognition) :
    model.IsAlambana object cognition :=
  ⟨cause, similarity⟩

end Model

/-! ## Collection and composite candidates -/

/-- A predicate-valued collection lets the first horn refer to any proposed
set of atoms without imposing an unargued mereology. -/
abbrev PredSet (Atom : Type u) := Atom -> Prop

/-- The two candidate forms in the reconstruction.  `collection` denotes the
causally contributing atoms taken collectively; `composite` denotes a
proposed whole over and above that collection.  The inductive distinction is
a formal proxy for the dilemma, not a proof that every historical ontology
accepts this exhaustive classification. -/
inductive Candidate (Atom : Type u) (Whole : Type v) where
  | collection (members : PredSet Atom)
  | composite (whole : Whole)

/-- The two disputed horn premises.  The first says that a causally relevant
atom collection lacks resemblance to the presented image.  The second says
that an image-resembling composite is not itself a causal producer.  Both
implications are assumptions of this reconstruction and remain visible in
every use of the exclusion theorem. -/
structure TwoHornFailure {Atom : Type u} {Whole : Type v}
    {Cognition : Type w}
    (model : Model (Candidate Atom Whole) Cognition) : Prop where
  collectionLacksSimilarity :
    forall members cognition,
      model.causallyProduces (.collection members) cognition ->
        ¬ model.imageSimilar (.collection members) cognition
  compositeLacksCausation :
    forall whole cognition,
      model.imageSimilar (.composite whole) cognition ->
        ¬ model.causallyProduces (.composite whole) cognition

namespace TwoHornFailure

variable {Atom : Type u} {Whole : Type v} {Cognition : Type w}
  {model : Model (Candidate Atom Whole) Cognition}

theorem collection_horn_excluded (failure : TwoHornFailure model)
    (members : PredSet Atom) (cognition : Cognition) :
    ¬ model.IsAlambana (.collection members) cognition := by
  intro isObject
  exact failure.collectionLacksSimilarity members cognition isObject.1
    isObject.2

theorem composite_horn_excluded (failure : TwoHornFailure model)
    (whole : Whole) (cognition : Cognition) :
    ¬ model.IsAlambana (.composite whole) cognition := by
  intro isObject
  exact failure.compositeLacksCausation whole cognition isObject.2
    isObject.1

/-- The two-horn exclusion.  Its case split is exhaustive only for the
explicit `Candidate` proxy type; the theorem does not silently classify all
possible theories of objects. -/
theorem two_horn_exclusion (failure : TwoHornFailure model) :
    forall candidate cognition, ¬ model.IsAlambana candidate cognition := by
  intro candidate cognition
  cases candidate with
  | collection members =>
      exact failure.collection_horn_excluded members cognition
  | composite whole =>
      exact failure.composite_horn_excluded whole cognition

end TwoHornFailure

/-! ## A nonvacuous concrete realization of both horns -/

inductive Atom where
  | left
  | right
  deriving DecidableEq, Repr

inductive Whole where
  | unified
  deriving DecidableEq, Repr

inductive Cognition where
  | unitaryImage
  deriving DecidableEq, Repr

/-- A genuine two-member collection, used to ensure that the collection horn
is not witnessed by an empty or singleton proxy. -/
def atomPair : PredSet Atom := fun _ => True

def pairCandidate : Candidate Atom Whole :=
  .collection atomPair

def wholeCandidate : Candidate Atom Whole :=
  .composite .unified

/-- In this concrete audit model, collections are causal but not similar, while
composites are similar but not causal.  This stipulation witnesses the logical
shape of the two premises; it is not offered as independent evidence for
their historical truth. -/
def concreteHornModel : Model (Candidate Atom Whole) Cognition where
  causallyProduces
    | .collection _, _ => True
    | .composite _, _ => False
  imageSimilar
    | .collection _, _ => False
    | .composite _, _ => True

theorem atom_pair_has_two_distinct_members :
    atomPair .left /\ atomPair .right /\ Atom.left ≠ Atom.right := by
  exact ⟨trivial, trivial, by decide⟩

theorem concrete_horn_premises : TwoHornFailure concreteHornModel := by
  constructor
  · intro members cognition cause similarity
    exact similarity
  · intro whole cognition similarity cause
    exact cause

/-- Both proposed candidates are present, and each has the positive condition
characteristic of its horn. -/
theorem concrete_horns_are_nonvacuous :
    concreteHornModel.causallyProduces pairCandidate .unitaryImage /\
      concreteHornModel.imageSimilar wholeCandidate .unitaryImage /\
      pairCandidate ≠ wholeCandidate := by
  refine ⟨trivial, trivial, ?_⟩
  intro equality
  cases equality

theorem concrete_candidates_are_both_excluded :
    (¬ concreteHornModel.IsAlambana pairCandidate .unitaryImage) /\
      ¬ concreteHornModel.IsAlambana wholeCandidate .unitaryImage := by
  exact ⟨concrete_horn_premises.collection_horn_excluded
      atomPair .unitaryImage,
    concrete_horn_premises.composite_horn_excluded
      .unified .unitaryImage⟩

/-! ## Independence of the two conditions -/

/-- A one-object, one-cognition model in which causal production holds and
image similarity fails. -/
def causalOnlyModel : Model Unit Unit where
  causallyProduces := fun _ _ => True
  imageSimilar := fun _ _ => False

/-- A one-object, one-cognition model in which image similarity holds and
causal production fails. -/
def similarityOnlyModel : Model Unit Unit where
  causallyProduces := fun _ _ => False
  imageSimilar := fun _ _ => True

theorem causal_production_alone_is_insufficient :
    causalOnlyModel.causallyProduces () () /\
      ¬ causalOnlyModel.imageSimilar () () /\
      ¬ causalOnlyModel.IsAlambana () () := by
  refine ⟨trivial, ?_, ?_⟩
  · intro similarity
    exact similarity
  · intro isObject
    exact isObject.2

theorem similarity_alone_is_insufficient :
    similarityOnlyModel.imageSimilar () () /\
      ¬ similarityOnlyModel.causallyProduces () () /\
      ¬ similarityOnlyModel.IsAlambana () () := by
  refine ⟨trivial, ?_, ?_⟩
  · intro cause
    exact cause
  · intro isObject
    exact isObject.1

/-- The counterexample has inhabited object and cognition types, so it
refutes an implication rather than exploiting an empty domain. -/
theorem no_bridge_from_cause_alone :
    ¬ (forall object cognition,
      causalOnlyModel.causallyProduces object cognition ->
        causalOnlyModel.IsAlambana object cognition) := by
  intro bridge
  exact causal_production_alone_is_insufficient.2.2
    (bridge () () trivial)

/-- The converse shortcut is independently refuted on inhabited domains. -/
theorem no_bridge_from_similarity_alone :
    ¬ (forall object cognition,
      similarityOnlyModel.imageSimilar object cognition ->
        similarityOnlyModel.IsAlambana object cognition) := by
  intro bridge
  exact similarity_alone_is_insufficient.2.2
    (bridge () () trivial)

/-! ## Ontological boundary of the local test -/

/-- A world adds an external-existence predicate to the intentional-object
interface.  No field connects external existence to causal production,
similarity, or `IsAlambana`; any such bridge must be stated separately. -/
structure World (Object : Type u) (Cognition : Type v)
    extends Model Object Cognition where
  externallyExists : Object -> Prop

namespace World

variable {Object : Type u} {Cognition : Type v}

def HasExternalObject (world : World Object Cognition) : Prop :=
  Exists world.externallyExists

/-- This is intentionally only a minimal *proxy* for global idealism: it says
that the modeled domain has no externally existing objects.  It does not
encode the richer epistemic or soteriological claims of any Yogacara school. -/
def GlobalIdealismProxy (world : World Object Cognition) : Prop :=
  forall object, ¬ world.externallyExists object

theorem not_global_idealism_proxy_of_external_witness
    {world : World Object Cognition} {object : Object}
    (external : world.externallyExists object) :
    ¬ world.GlobalIdealismProxy := by
  intro denial
  exact denial object external

end World

/-! ## The full dilemma with external candidates -/

/-- Extend the same nonvacuous two-horn model with external existence for
every collection and composite candidate.  Existence remains independent of
the two intentional-object conditions. -/
def externalHornWorld : World (Candidate Atom Whole) Cognition where
  causallyProduces := concreteHornModel.causallyProduces
  imageSimilar := concreteHornModel.imageSimilar
  externallyExists := fun _ => True

theorem external_horn_premises :
    TwoHornFailure externalHornWorld.toModel :=
  concrete_horn_premises

/-- The actual two-horn premises, exclusion of every candidate in the proxy
type, and external existence of those same candidates coexist in one concrete
nonvacuous model.  Thus the full local dilemma still does not entail the stated global
idealism proxy. -/
theorem two_horn_exclusion_is_compatible_with_external_existence :
    TwoHornFailure externalHornWorld.toModel /\
      (forall candidate, externalHornWorld.externallyExists candidate) /\
      (forall candidate cognition,
        ¬ externalHornWorld.toModel.IsAlambana candidate cognition) /\
      externalHornWorld.HasExternalObject /\
      ¬ externalHornWorld.GlobalIdealismProxy := by
  refine ⟨external_horn_premises, fun _ => trivial,
    external_horn_premises.two_horn_exclusion,
    ⟨pairCandidate, trivial⟩, ?_⟩
  intro globalDenial
  exact globalDenial pairCandidate trivial

inductive BoundaryObject where
  | stone
  deriving DecidableEq, Repr

inductive BoundaryCognition where
  | blueImage
  deriving DecidableEq, Repr

/-- The stone exists externally and causes the cognition, but it fails the
similarity condition.  This provides a concrete boundary model for what the
local `IsAlambana` test can establish. -/
def boundaryWorld : World BoundaryObject BoundaryCognition where
  causallyProduces := fun _ _ => True
  imageSimilar := fun _ _ => False
  externallyExists := fun _ => True

theorem local_failure_is_compatible_with_external_existence :
    (¬ boundaryWorld.toModel.IsAlambana .stone .blueImage) /\
      boundaryWorld.externallyExists .stone /\
      boundaryWorld.HasExternalObject := by
  refine ⟨?_, trivial, ⟨.stone, trivial⟩⟩
  intro isObject
  exact isObject.2

/-- A failed intentional-object episode does not entail nonexistence of that
object.  The negated implication is witnessed by the concrete external stone,
not derived by an abstract appeal to underdetermination. -/
theorem local_failure_does_not_entail_external_nonexistence :
    ¬ ((¬ boundaryWorld.toModel.IsAlambana .stone .blueImage) ->
      ¬ boundaryWorld.externallyExists .stone) := by
  intro bridge
  exact bridge local_failure_is_compatible_with_external_existence.1
    local_failure_is_compatible_with_external_existence.2.1

/-- Nor does one failed episode entail the module's global-idealism proxy.
This is the formal boundary on reading the two-horn exclusion as a global
ontological conclusion. -/
theorem local_failure_does_not_entail_global_idealism :
    ¬ ((¬ boundaryWorld.toModel.IsAlambana .stone .blueImage) ->
      boundaryWorld.GlobalIdealismProxy) := by
  intro bridge
  have globalDenial :=
    bridge local_failure_is_compatible_with_external_existence.1
  exact globalDenial .stone
    local_failure_is_compatible_with_external_existence.2.1

end BuddhistComparativeLogic.Alambanapariksa
