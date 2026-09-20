/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.DependenceCoverage
import BuddhistComparativeLogic.Buddhist.Madhyamaka.EmptinessInference
import BuddhistComparativeLogic.Buddhist.Madhyamaka.FourfoldCausation
import BuddhistComparativeLogic.Buddhist.Pramana.InferenceScope
import BuddhistComparativeLogic.Buddhist.Madhyamaka.TwoTruths

/-!
# Reusable schemas for the arguments supporting emptiness

This module composes results that were previously available only one stage at
a time.  The statements keep four scopes separate:

* a witnessed dependence concerns one subject;
* coverage determines the domain on which non-substantiality follows;
* conventional appearance is an additional predicate, compatible with absence
  of own-being;
* a valid cell in Dignāga's wheel additionally requires a comparison subject,
  although the subject-level deduction needs only reason and pervasion.

The last sections connect fourfold non-arising to the same inference interface
and record the two failures that prevent FDE formula negation from being used as
metalevel rejection without an extra consistency or no-gap premise.
-/

namespace BuddhistComparativeLogic.SupportingArguments

open AssumptionAudit
open DependenceModes

/-! ## Scoped dependence and the two levels of the middle way -/

/-- Every member of `domain` has a dependence witness in the selected mode. -/
def ModeCoverageOn (M : DependenceModes.Model D) (mode : Mode)
    (domain : D -> Prop) : Prop :=
  forall x, domain x -> exists y, M.DependsAt mode y x

/-- Conventional presence and absence of own-being, asserted of the same
subject but at distinct explanatory levels. -/
def MiddleWayOn (M : DependenceModes.Model D) (appears domain : D -> Prop) :
    Prop :=
  ∀ x, domain x -> appears x /\ ¬ M.own x

/-- A mode-specific variation argument establishes absence of own-being on
exactly the domain supplied by its coverage premise. -/
theorem non_substantial_on_covered_domain
    (M : DependenceModes.Model D) (mode : Mode)
    (invariant : M.InvariantOwnAt mode) (domain : D -> Prop)
    (coverage : ModeCoverageOn M mode domain) :
    ∀ x, domain x -> ¬ M.own x := by
  intro x hx
  obtain ⟨y, edge⟩ := coverage x hx
  exact M.empty_of_mode_dependency mode invariant edge

/-- Adding the conventional premise yields a middle-way conclusion: the
covered subjects appear while lacking own-being. -/
theorem middle_way_on_covered_domain
    (M : DependenceModes.Model D) (mode : Mode)
    (invariant : M.InvariantOwnAt mode) (appears domain : D -> Prop)
    (coverage : ModeCoverageOn M mode domain)
    (conventional : forall x, domain x -> appears x) :
    MiddleWayOn M appears domain := by
  intro x hx
  exact ⟨conventional x hx,
    non_substantial_on_covered_domain M mode invariant domain coverage x hx⟩

/-- Coverage may use a different admitted mode for each subject. -/
theorem middle_way_on_mixed_mode_coverage
    (M : DependenceModes.Model D)
    (appears domain : D -> Prop) (allowed : Mode -> Prop)
    (invariant : forall mode, allowed mode -> M.InvariantOwnAt mode)
    (coverage : ∀ x, domain x -> M.CoveredBy allowed x)
    (conventional : ∀ x, domain x -> appears x) :
    MiddleWayOn M appears domain := by
  intro x hx
  obtain ⟨mode, admitted, source, edge⟩ := coverage x hx
  exact ⟨conventional x hx,
    M.empty_of_mode_dependency mode (invariant mode admitted) edge⟩

/-- Strengthening the admitted domain requires new coverage; restricting it
does not. -/
theorem middle_way_restrict
    (M : DependenceModes.Model D) (appears large small : D -> Prop)
    (included : forall x, small x -> large x)
    (h : MiddleWayOn M appears large) :
    MiddleWayOn M appears small :=
  fun x hx => h x (included x hx)

/-- Two separately covered domains can be combined without pretending that a
single local witness covers every subject. -/
theorem middle_way_union
    (M : DependenceModes.Model D) (appears first second : D -> Prop)
    (hfirst : MiddleWayOn M appears first)
    (hsecond : MiddleWayOn M appears second) :
    MiddleWayOn M appears (fun x => first x \/ second x) := by
  intro x hx
  cases hx with
  | inl h => exact hfirst x h
  | inr h => exact hsecond x h

def isolatedSubject : Bool -> Prop := fun x => x = false

/-- A concrete scope audit: the causal witness establishes the middle-way
claim for `false`, while the uncovered subject `true` still has own-being. -/
theorem local_argument_does_not_universalize :
    MiddleWayOn (DependenceCoverage.isolated .causal)
      (fun x =>
        (DependenceCoverage.isolated .causal).manifest .causal true x = true)
      isolatedSubject /\
    ¬ (∀ x, ¬ (DependenceCoverage.isolated .causal).own x) := by
  constructor
  · apply middle_way_on_covered_domain
      (DependenceCoverage.isolated .causal) .causal
      (DependenceModes.Model.OwnBeingCriteria.at
        (DependenceCoverage.isolated .causal)
        (DependenceCoverage.isolated_criteria .causal) .causal)
    · intro x hx
      cases hx
      exact ⟨true, DependenceCoverage.isolated_active_edge .causal⟩
    · intro x hx
      cases hx
      rfl
  · intro universal
    exact universal true rfl

/-- The mixed finite model demonstrates that universal coverage can be
assembled from different modes subject by subject. -/
theorem mixed_modes_support_universal_middle_way :
    MiddleWayOn DependenceCoverage.mixed (fun _ => True) (fun _ => True) := by
  exact middle_way_on_mixed_mode_coverage DependenceCoverage.mixed
    (fun _ => True) (fun _ => True) DependenceModes.Model.AllModes
    (fun mode _ =>
      DependenceModes.Model.OwnBeingCriteria.at DependenceCoverage.mixed
        DependenceCoverage.mixed_criteria mode)
    (fun x _ => DependenceCoverage.mixed_universal_coverage x)
    (fun _ _ => trivial)

/-! ## From a dependence witness to an inference certificate -/

/-- The Dharmakirti-style inference whose reason is dependence in one mode and
whose thesis is absence of own-being. -/
def modeInference (M : DependenceModes.Model D) (mode : Mode) (x : D) :
    Dharmakirti.Model D :=
  EmptinessInference.ofDependence (M.toDependenceAt mode) x

/-- A local edge supplies subject possession of the reason, an independently
derived pervasion, and the thesis.  No comparison subject is needed for this
deductive core. -/
theorem local_dependence_inference
    (M : DependenceModes.Model D) (mode : Mode)
    (invariant : M.InvariantOwnAt mode)
    {x y : D} (edge : M.DependsAt mode y x) :
    (modeInference M mode x).toAnumana.paksadharmata /\
      (modeInference M mode x).vyapti /\
      (modeInference M mode x).sadhya x := by
  refine ⟨?_, M.dependence_excludes_own_at mode invariant,
    M.empty_of_mode_dependency mode invariant edge⟩
  exact ⟨y, edge⟩

/-- A comparison subject is an additional dependence witness away from the
subject of inference. -/
def ComparisonWitness (M : DependenceModes.Model D) (mode : Mode) (x : D) :
    Prop :=
  ∃ z, z ≠ x /\ ∃ source, M.DependsAt mode source z

/-- For this particular inference adapter, a comparison witness is exactly
the positive-comparison (`anvaya`) mark once the own-being criterion is fixed. -/
theorem comparisonWitness_iff_anvaya
    (M : DependenceModes.Model D) (mode : Mode)
    (invariant : M.InvariantOwnAt mode) (x : D) :
    ComparisonWitness M mode x <->
      (modeInference M mode x).toAnumana.anvaya := by
  constructor
  · rintro ⟨z, hzx, source, edge⟩
    refine ⟨z, ⟨hzx, ?_⟩, ⟨source, edge⟩⟩
    exact M.empty_of_mode_dependency mode invariant edge
  · rintro ⟨z, hz, source, edge⟩
    exact ⟨z, hz.1, source, edge⟩

/-- Because the derived pervasion supplies the negative-comparison mark, wheel
validity is equivalent to the remaining comparison witness. -/
theorem wheel_valid_iff_comparison
    (M : DependenceModes.Model D) (mode : Mode)
    (invariant : M.InvariantOwnAt mode) (x : D) :
    (modeInference M mode x).toAnumana.wheelVerdict = .valid <->
      ComparisonWitness M mode x := by
  let inference := modeInference M mode x
  have pervasion : inference.vyapti :=
    M.dependence_excludes_own_at mode invariant
  constructor
  · intro verdict
    have anvaya := (inference.toAnumana.wheel_valid_iff.mp verdict).1
    exact (comparisonWitness_iff_anvaya M mode invariant x).mpr anvaya
  · intro comparison
    have anvaya : inference.toAnumana.anvaya :=
      (comparisonWitness_iff_anvaya M mode invariant x).mp comparison
    exact inference.toAnumana.wheel_valid_iff.mpr
      ⟨anvaya, inference.vyapti_gives_vyatireka pervasion⟩

/-- With a comparison witness, the local deductive certificate also satisfies
the three marks and occupies a valid cell of the wheel of reasons. -/
theorem comparison_completes_three_marks
    (M : DependenceModes.Model D) (mode : Mode)
    (invariant : M.InvariantOwnAt mode)
    {x y : D} (edge : M.DependsAt mode y x)
    (comparison : ComparisonWitness M mode x) :
    (modeInference M mode x).toAnumana.trairupya /\
      (modeInference M mode x).toAnumana.wheelVerdict = .valid /\
      (modeInference M mode x).sadhya x := by
  let inference := modeInference M mode x
  have certificate := local_dependence_inference M mode invariant edge
  obtain ⟨z, hzx, source, zedge⟩ := comparison
  have anvaya : inference.toAnumana.anvaya := by
    refine ⟨z, ⟨hzx, ?_⟩, ?_⟩
    · exact M.empty_of_mode_dependency mode invariant zedge
    · exact ⟨source, zedge⟩
  have vyatireka : inference.toAnumana.vyatireka :=
    inference.vyapti_gives_vyatireka certificate.2.1
  have marks : inference.toAnumana.trairupya :=
    ⟨certificate.1, anvaya, vyatireka⟩
  have verdict : inference.toAnumana.wheelVerdict = .valid :=
    inference.toAnumana.wheel_valid_iff.mpr ⟨anvaya, vyatireka⟩
  exact ⟨marks, verdict, certificate.2.2⟩

/-- Conversely, once the three marks are fixed, the missing global pervasion
has exactly the strength of the subject's thesis. -/
theorem pervasion_has_subject_strength_under_marks
    (a : Hetucakra.Anumana D) (marks : a.trairupya) :
    InferenceScope.Pervasion a <-> a.sadhya a.paksa :=
  InferenceScope.pervasion_iff_thesis_under_marks a marks

/-! ## Fourfold non-arising as the same non-substantiality argument -/

/-- Read event causation as dependence and intrinsic production as own-being.
This is an adapter, not an identification built into either source model. -/
def fourfoldDependence (M : FourfoldCausation.Model E K T) :
    AssumptionAudit.Dependence E where
  dep := M.causes
  own := M.intrinsic

/-- The event-level fourfold laws derive the exclusion/pervasion premise for
the adapter. -/
theorem fourfold_exclusion
    (M : FourfoldCausation.Model E K T) (laws : M.Laws) :
    (fourfoldDependence M).Exclusion := by
  intro event source _
  exact M.no_intrinsic_direct laws event

/-- The occurrence condition is precisely scoped arising for occurring event
tokens. -/
theorem fourfold_arising_on_occurrences
    (M : FourfoldCausation.Model E K T) (laws : M.Laws) :
    ∀ event, M.occurs event -> (fourfoldDependence M).arisen event := by
  intro event occurs
  exact laws.occurrenceConditioned occurs

/-- Occurring events are conventionally present and non-intrinsic under the
fourfold laws.  This conclusion does not deny their occurrence. -/
theorem fourfold_middle_way
    (M : FourfoldCausation.Model E K T) (laws : M.Laws) :
    ∀ event, M.occurs event -> M.occurs event /\ ¬ M.intrinsic event := by
  intro event occurs
  exact ⟨occurs,
    (fourfoldDependence M).empty_of_arisen (fourfold_exclusion M laws)
      (fourfold_arising_on_occurrences M laws event occurs)⟩

/-- A causal edge therefore yields the same local reason, pervasion and thesis
certificate as the dependence argument above. -/
theorem fourfold_inference
    (M : FourfoldCausation.Model E K T) (laws : M.Laws)
    {event source : E} (edge : M.causes source event) :
    (EmptinessInference.ofDependence (fourfoldDependence M) event).toAnumana.paksadharmata /\
      (EmptinessInference.ofDependence (fourfoldDependence M) event).vyapti /\
      ¬ M.intrinsic event := by
  have arising : (fourfoldDependence M).arisen event := ⟨source, edge⟩
  have exclusion := fourfold_exclusion M laws
  exact ⟨arising, exclusion,
    (fourfoldDependence M).empty_of_arisen exclusion arising⟩

/-- The finite chain witnesses that non-intrinsic arising retains occurrence,
a distinct prior condition, and sameness of event kind. -/
theorem non_intrinsic_does_not_mean_nonexistent :
    FourfoldCausation.chain.occurs true /\
      ¬ FourfoldCausation.chain.intrinsic true /\
      FourfoldCausation.chain.SameKindConditional true := by
  exact ⟨rfl,
    FourfoldCausation.chain.no_intrinsic_by_four_cases
      FourfoldCausation.chain_laws true,
    FourfoldCausation.same_kind_conditional_nonvacuous⟩

/-! ## Two truths and the scope of negation -/

/-- The four FDE conditions that jointly express conventional appearance and
ultimate emptiness without a glut at either evaluation point. -/
def TwoTruthMiddle (T : TwoTruthsFDE) (x : Dharma) : Prop :=
  mvFDE.designated (T.val .samvrti x) /\
    mvFDE.designated (neg4 (T.svAt .paramartha x)) /\
    ¬ mvFDE.designated (neg4 (T.val .samvrti x)) /\
    ¬ mvFDE.designated (T.svAt .paramartha x)

theorem two_truths_supplies_middle (T : TwoTruthsFDE) (x : Dharma) :
    TwoTruthMiddle T x :=
  ⟨T.conv_appears x, T.ult_empty x,
    T.conv_consistent x, T.ult_consistent x⟩

/-- Local consistency fixes the two queried values to classical points and
simultaneously recovers the identity, mutual, and non-separation readings. -/
theorem two_truths_normal_form (T : TwoTruthsFDE) (x : Dharma) :
    T.val .samvrti x = TV4.T /\
      T.svAt .paramartha x = TV4.F /\
      T.toTwoTruths.XIdentity x /\
      T.toTwoTruths.XMutual x /\
      T.toTwoTruths.XNotsep x := by
  exact ⟨T.conv_T x, T.ult_F x, T.hs07_two_truths x,
    T.toTwoTruths.X_mutual_always x, T.hs06_two_truths x⟩

/-- Mutual designation alone does not provide the stronger non-separation
reading; an ultimate glut is a concrete counterexample. -/
theorem mutual_reading_does_not_force_notseparation :
    (∀ x, fdeGlutEmptiness.flat.XMutual x) /\
      ¬ fdeGlutEmptiness.flat.XNotsep (Dharma.sk Skandha.rupa) := by
  exact ⟨fun x => fdeGlutEmptiness.flat.X_mutual_always x,
    ult_glut_breaks_hs06 (Dharma.sk Skandha.rupa)⟩

/-- A designated FDE negation cannot uniformly be read as metalevel exclusion:
the glut is designated together with its negation. -/
theorem no_fde_negation_to_exclusion :
    ¬ (∀ value, mvFDE.designated (neg4 value) ->
      ¬ mvFDE.designated value) := by
  intro bridge
  exact bridge TV4.B rfl rfl

/-- Metalevel rejection cannot uniformly be promoted to designated formula
negation either: the gap and its negation are both undesignated. -/
theorem no_fde_rejection_to_negation :
    ¬ (∀ value, (¬ mvFDE.designated value) ->
      mvFDE.designated (neg4 value)) := by
  intro bridge
  have rejected : ¬ mvFDE.designated TV4.N := by
    exact Bool.noConfusion
  have negated := bridge TV4.N rejected
  exact Bool.noConfusion negated

end BuddhistComparativeLogic.SupportingArguments
