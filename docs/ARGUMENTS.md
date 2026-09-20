# Arguments supporting the chosen Heart Sutra readings

Role: `supplement`

Lifecycle: `active`

## Sources and scope

This formalizes arguments relevant to the repository's chosen readings.
It does not prove historical dependence by the Heart Sutra's authors or
identify nonself, absence of own-being, and absence of existence.

Primary text inspected on 2026-09-11: the Chinese *Zhong lun*, T1564,
attributed to Nagarjuna with Qingmu's commentary, translated by Kumarajiva,
in CBETA's 2023.Q4 edition hosted by National Taiwan University:

- [Chapter 1, opening argument](https://buddhism.lib.ntu.edu.tw/FULLTEXT/sutra/chi_pdf/sutra13/T30n1564.pdf#page=7), printed page 6: the four origin cases and their discussion.
- [Chapter 15, verses 1–2 and commentary](https://buddhism.lib.ntu.edu.tw/FULLTEXT/sutra/chi_pdf/sutra13/T30n1564.pdf#page=51), printed page 50: conditioned construction is contrasted with own-being's independence.
- [Chapter 24, verses 18–19 and the cessation argument](https://buddhism.lib.ntu.edu.tw/FULLTEXT/sutra/chi_pdf/sutra13/T30n1564.pdf#page=83), printed pages 82–83: dependent arising and emptiness; fixed suffering would not cease and a fixed path would not be cultivated.

The contextual model, fourfold proof obligations and quantitative path
below are our specifications, not claimed literal translations. The
inference-scope audit concerns the existing Hetucakra encoding, not a claim
that the Heart Sutra explicitly uses Dignaga's three marks or that every
historical understanding of those marks fails deductively.

## 1. Conditional variation → no own-being → pervasion

[BuddhistComparativeLogic/Buddhist/Madhyamaka/DependentOrigination.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/DependentOrigination.lean)

Presence, enabled conditions and own-being are separate data. The
interpretive premise says own-being entails unchanged presence across
admitted contexts. Dependency is witnessed by contexts differing in exactly
one other condition, with different presence of the subject.

`variation_refutes_own` proves the reductio;
`dependence_excludes_own` derives the previous audit's exclusion law;
`contextual_pervasion` and `contextual_inference` connect it to the existing
Dharmakirti interface without assuming universal emptiness.

`invariance_needed` retains variation and own-being when the criterion is
omitted. `universalization_needs_a_premise` has both a dependent empty
subject and another subject with own-being. `empty_yet_present` preserves
ordinary presence, while `empty_does_not_supply_occurrence_or_dependence`
blocks the reverse inference from emptiness to occurrence or dependency.

The invariance criterion and admitted contexts remain modeling commitments.
No completeness theorem identifies this intervention-based relation with
every possible interpretation of dependent arising.

## 2. The obligations behind fourfold non-arising

[BuddhistComparativeLogic/Buddhist/Madhyamaka/Prasanga.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Prasanga.lean)

The target is intrinsic production, distinct from ordinary conditional
occurrence. Each case exposes the incompatible premises it requires:

| Case | Consequence premise | Incompatible premise |
| --- | --- | --- |
| From self | The producer would be prior to itself. | Priority is irreflexive. |
| From other, intrinsically | The product is independent of conditions. | Its production has a condition. |
| From both | The self-production case is included. | The self case is refuted. |
| Without cause | No condition exists. | Its production has a condition. |

The case lemmas feed `no_intrinsic_production`, with exhaustiveness as an
additional premise. `every_case_matters` and `coverage_matters` give
countermodels to the eliminator with a case or coverage omitted. They do
not establish independence of every premise in the stronger law record.

Independence cannot follow just from the word “other”.
`other_independence_is_substantive` satisfies the other seven obligations
while retaining production. `other_independence_from_context` derives
independence using section 1 only if that origin claim asserts own-being.
`fourfold_laws_nonvacuous` and `nonarising_preserves_conditional_edges`
supply a nonempty model of all laws with an ordinary dependency edge.

Logical rules are audited separately:

- `rejection_via_preservation` uses genuine preservation of designatedness
  and metalevel rejection for any designation predicate.
- `fde_mt_for_all_antecedents_iff` shows that material modus tollens works
  for every antecedent at a fixed FDE consequent exactly when the consequent
  is not a glut. For T and N the negated-consequent premise is unavailable.
- `fde_fourfold_from_local_reductios` supplies the negations to the existing
  MMK1 theorem using these local conditions.
- `fde_rejection_without_negation` exhibits a gap blocking conversion of
  rejection to formula negation; `fde_rejection_to_negation` adds no-gap.
  The existing all-glut countermodel still blocks identifying designated
  non-arising with undesignated arising.

The case principles remain contestable reconstructions. Their historical
and philosophical justification is not discharged by Lean.

## 3. What reaches the disputed subject?

[BuddhistComparativeLogic/Buddhist/Pramana/InferenceScope.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/InferenceScope.lean)

`pervasion_splits_at_subject` separates global pervasion into off-subject
and at-subject components. Under the three marks in the current encoding,
`pervasion_iff_thesis_under_marks` equates pervasion with the subject's
thesis. `uniformity_iff_thesis_under_marks` does likewise for uniformity.
These audit logical strength; independently justified pervasion need not
be epistemically circular.

`eraseSubject` deletes the thesis only at the subject.
`marks_allow_false_subject` preserves the subject, reason, three marks and
Valid wheel verdict while making its thesis false. This systematically
generalizes the existing smoke-without-fire example. An independent law,
such as section 1's contextual criterion, is needed to justify pervasion.

## 4. Cessation excludes fixed suffering

[BuddhistComparativeLogic/Buddhist/Madhyamaka/CessationArgument.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/CessationArgument.lean)

`RigidAt` says the suffering rank never changes along a process.
`positive_rigid_suffering_cannot_cease` and `cessation_refutes_rigidity`
establish the reductio. `path_refutes_rigidity` uses the
finite release theorem, under its explicit update laws and initial insight.
`path_refutes_intrinsic_suffering` rejects an independent own-being
predicate under the criterion that it entails rigidity.

Initial positive suffering matters: already-zero suffering can remain
rigid and zero. Conversely, `no_intrinsic_suffering_does_not_guarantee_release`
retains suffering forever despite denying own-being. Emptiness alone is
therefore not made a sufficient psychological cause of release.

## 5. Dependence modes, coverage, and exact origin cases

[BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceModes.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceModes.lean),
[BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceCoverage.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceCoverage.lean),
and [BuddhistComparativeLogic/Buddhist/Madhyamaka/FourfoldCausation.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/FourfoldCausation.lean)

Causal, mereological, and conceptual dependence are independent relations.
`empty_of_mode_dependency` derives absence of own-being only through the
exclusion law for the witnessed mode. `all_empty_of_coverage` adds the
separate premise that every subject has at least one mode. The countermodels
`incomplete_coverage_allows_own` and `independence_does_not_decide_own`
show why neither step can be suppressed.

The event model replaces four unstructured propositions with production
tokens carrying producer kind and time. `exact_origin_exhaustive` and
`exact_origin_unique` prove the four origin tags exhaustive and exclusive.
`no_intrinsic_by_four_cases` eliminates intrinsic production under four
explicit incompatibility laws, while `nonarising_preserves_ordinary_production`
gives a nonempty ordinary production model. The module also gives omission
models for the classification and each law.

## 6. Revision, the antidote, and the complete pipeline

[BuddhistComparativeLogic/Buddhist/HeartSutra/BeliefRevision.lean](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/BeliefRevision.lean),
[BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/CognitiveAntidote.lean](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/CognitiveAntidote.lean),
[BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/AntidoteSelection.lean](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/AntidoteSelection.lean),
and [BuddhistComparativeLogic/Buddhist/HeartSutra/ArgumentPipeline.lean](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/ArgumentPipeline.lean)

Belief revision distinguishes observing a reason, assimilating it, positive
support, and residual commitment. `rational_revision_contracts` derives the
one-step contraction used by `eventual_release_from_revision`. The finite
models `observation_without_assimilation`,
`evidence_growth_without_support_discipline`, and
`rational_revision_can_relapse` separate the assumptions needed for the
uniform guarantee.

The gate is open exactly while support for intrinsic truth exceeds admitted
counterevidence (`antidote_stops_iff_evidence_sufficient`). The form of the
response is no longer just a pair of equations: an adequate conventional
response is a least common consequence of the two assertions in the current
attachment focus, and the ultimate response reverses it. FDE proof theory
then yields `attachment_account_selects_tstep_up_to_derivability`. The exact
syntax tree follows only after the explicit canonical-form specification in
`selected_remedy_is_tstep`.

`dependence_to_bounded_release` and `fourfold_to_bounded_release` compose the
metaphysical recognition, assimilation, and quantitative path. The reverse
and shortcut claims are blocked by `insight_without_revision_does_not_release`
and `release_does_not_prove_universal_emptiness`.

## 7. Proof theory and universal designation

[BuddhistComparativeLogic/Core/FDECalculus.lean](../lean/BuddhistComparativeLogic/Core/FDECalculus.lean),
[BuddhistComparativeLogic/Core/UniversalDesignationMore.lean](../lean/BuddhistComparativeLogic/Core/UniversalDesignationMore.lean),
and [BuddhistComparativeLogic/Core/Ineffable.lean](../lean/BuddhistComparativeLogic/Core/Ineffable.lean)

`Deriv` is a lattice/De Morgan natural-deduction system. A nonempty DNF
construction proves both directions of `deriv_sound_complete`. Signed
analytic tableaux independently satisfy `tableau_sound_complete`, and
`tableau_iff_deriv` converts between their proof objects. Adding the exact
atom-containment condition yields the FDE5 results
`deriv5_sound_complete` and `tableau5_sound_complete`;
`fde5_does_not_contrapose` records the relevance boundary.

Positive universal K3 consequence is K3 itself (`pos_up_k3_is_k3`), whereas
the LP case is FDE (`pos_up_lp_is_fde`). Together with variable restriction,
these give `priest_open_question_k3` and `priest_open_question_lp`. A separate
generic construction adjoins one undesignated absorbing value to any
`MVLogic`; `pos_upentails_iff` and `upentails_iff` characterize exactly the
additional atom-coverage or positive-unsatisfiability proviso.

## 8. Dynamics and the smaller comparative arguments

[BuddhistComparativeLogic/Comparative/Jaina/NayaDynamics.lean](../lean/BuddhistComparativeLogic/Comparative/Jaina/NayaDynamics.lean),
[BuddhistComparativeLogic/Buddhist/Pramana/Momentariness.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Momentariness.lean),
[BuddhistComparativeLogic/Buddhist/Pramana/ApohaFeatures.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/ApohaFeatures.lean),
[BuddhistComparativeLogic/Buddhist/Madhyamaka/GamanaIntervals.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/GamanaIntervals.lean), and
[BuddhistComparativeLogic/Buddhist/Yogacara/VimsatikaModels.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/VimsatikaModels.lean)

Every one of the seven naya has a realizing route
(`route_realizes_mode`), and `route_is_length_minimal` proves that mixed
modes need two or three entered respects. `ExactlyLicenses` records a trace's
exact profile; the weaker `Supports` persists when observations are appended.

`causal_nonuniformity` isolates what efficacy and unique effect-time alone
prove. Finite causal chains transport effects through local continuity;
`momentary_of_rooted_causalChains` derives literal momentariness only after
every production time is rooted in such a chain. The permanent `eachMoment`
model proves that nonuniformity alone is insufficient.

For componential apoha, fixed features and requirements determine one pair
(`fixed_features_determine_unique_pair`). Higher features stop the regress at
a fixed point (`stable_requirement_stops_regress`), while a self-excluding
profile oscillates at every finite stage (`self_excluding_regress_never_stops`).

The positive interval account proves `interval_motion_traverses` and remains
compatible with pointwise path analysis. The Twenty Verses comparison proves
observational invariance of adequacy and constructs a neutral observation-token
factorization for every appearance account;
`four_conditions_do_not_decide_between_models` records equivalence with both
the `Unit`- and `Bool`-indexed accounts and the non-bijection of their carriers.

## 9. Recension alignment as checked data

[BuddhistComparativeLogic/Buddhist/HeartSutra/RecensionAlignment.lean](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/RecensionAlignment.lean)

The module supplies an executable, edition-parametric validator for source
coverage, target coverage, functionality, range, and order. Canonical-key
Sanskrit, Tibetan, and longer-frame maps pass it. Bounded excerpts from the
[GRETIL Sanskrit text](https://gretil.sub.uni-goettingen.de/gretil/1_sanskr/4_rellit/buddh/prajnhsu.htm)
and [Silk's Tibetan critical edition](https://wstb.univie.ac.at/wp-content/uploads/WSTB_34.pdf)
discharge the four central lexical obligations. The diplomatic source orders
reverse the Chinese HS06–HS07 key order; this is proved by
`sanskrit_diplomatic_not_order_preserving` and
`tibetan_diplomatic_not_order_preserving` rather than hidden by the canonical
map. `lexical_validation_is_construal_neutral` proves that the same surface
checks accept every candidate construal. The countermodels
`structural_alignment_does_not_force_character_counts` and
`structural_alignment_does_not_force_text_equivalence` prevent a structural
match from being reported as text identity or translation equivalence.

## 10. Remaining interfaces as Lean objects

[BuddhistComparativeLogic/Buddhist/Madhyamaka/SupportingArguments.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/SupportingArguments.lean),
[BuddhistComparativeLogic/Buddhist/HeartSutra/PremiseCertificates.lean](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/PremiseCertificates.lean),
[BuddhistComparativeLogic/Core/MatrixTransport.lean](../lean/BuddhistComparativeLogic/Core/MatrixTransport.lean),
[BuddhistComparativeLogic/Buddhist/Pramana/DirectedMomentariness.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/DirectedMomentariness.lean),
and [BuddhistComparativeLogic/Buddhist/Pramana/ApohaSelection.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/ApohaSelection.lean)

The supporting-argument schemas retain the domain of every dependence claim,
connect a local dependence witness to the Dharmakīrti inference interface,
and show that ordinary conditioned occurrence is compatible with fourfold
non-intrinsic production.  The two finite FDE countermodels block both
directions of an invalid identification between designated formula negation
and metalevel rejection.

Premise certificates distinguish a source locator from a proof of the stated
proposition.  `dependence_certificate_sound` and
`fourfold_certificate_sound` consume proof-bearing fields one by one;
`citation_metadata_can_accompany_a_false_claim` together with
`certified_false_is_uninhabited` proves that metadata alone cannot close the
argument.  The shipped internal locators are compiler-resolved Lean names;
external locators remain unchecked annotations.  A fourfold release
certificate additionally carries occurrence of its event, so the finite chain
example cannot issue the same certificate for its nonoccurring token
(`nonoccurring_chain_event_has_no_release_certificate`).

`MatrixIso` records a bijection preserving designation, negation, conjunction,
and disjunction.  Its transport theorems preserve ordinary consequence and
both universal-designation relations.  The Boolean truth/falsity-pair FDE
matrix is a concrete classified instance; a new named matrix still needs an
actual isomorphism or its own proof.

The momentariness bridge now needs only backward transport of an observed
effect along a rooted finite chain.  A finite model proves that forward
transport can fail while the directed theorem still applies.  Its declaration
reuses the existing momentariness theory record; that record's two-times field
is not consumed by the directed proof.  The apoha
selection layer similarly isolates admissibility, optimality, and
antisymmetry.  `selected_grounding_unique` is an at-most-one theorem and
`selected_grounding_exists` separately requires a supplied optimal candidate;
the tied model proves that admissibility alone leaves two distinct grounded
pairs.

## 11. Pramāṇa and Yogācāra synthesis

[BuddhistComparativeLogic/Buddhist/Pramana/PramanaSynthesis.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/PramanaSynthesis.lean),
[BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraSynthesis.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraSynthesis.lean),
[BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraConsciousness.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraConsciousness.lean),
and [BuddhistComparativeLogic/Buddhist/Yogacara/PramanaYogacara.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/PramanaYogacara.lean)

The pramāṇa certificate separates what derives a thesis at its subject from
what classifies a reason in a public comparison.  Subject possession plus
pervasion yields `deductive_sound`; an additional positive comparison example
yields `dialectical_trairupya` and `dialectical_wheel_valid`.  Three finite
boundaries show that the wheel does not settle the subject, vacuous pervasion
does not replace subject possession, and a subject-level sound inference need
not have a comparison case.

The Yogācāra synthesis models the three natures as analyses of one phenomenon,
composes local seed development into finite lineages, and states
transformation as a separate cut condition.  Countermodels prevent dependent
occurrence from being reported as perfected nature, causal succession as an
unchanging seed, or succession alone as transformation.  The eight
consciousnesses are an exhaustive role datatype; their connection to a store
support process and to projected subject/object duality remains explicit.

At the joint interface, observational adequacy is a reason and
`ObservationalLicense` is its pervasion.  Observation-equivalent finite
accounts disagree about both external-object existence and object count.
`three_marks_do_not_establish_external_objects` therefore has subject
possession, all three marks, and a valid wheel cell while its pervasion and
subject thesis are false.  Restricting the domain recovers only the
ontological commitment used in the restriction.  The complete audit is
[PRAMANA_YOGACARA.md](PRAMANA_YOGACARA.md).

## 12. Catuṣkoṭi, K3, and FDE

[BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean](../lean/BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean)
turns the informal comparison between the three-valued and four-valued
matrices into an explicit embedding.  `k3Embed_range_iff` identifies the image
as exactly `T`, `N`, and `F`; the connective, evaluation, designation, and
satisfaction preservation theorems make it a submatrix result rather than a
mere correspondence of three labels.

`k3_entails_iff_fde_no_gluts` identifies K3 consequence with FDE consequence
restricted to valuations that omit `B`.  Since unrestricted FDE admits more
valuations, `fde_entails_implies_k3_entails` holds.  The reverse direction is
strictly false: `explosion_strictly_separates_k3_from_fde` uses contradictory
premises, which have no K3 model but have an FDE glut model whose unrelated
conclusion is a gap.

The corner comparison is exact.  `fde_corner_injective` shows that all four FDE
values remain distinct under the classifier, while `k3_corner_image_exact`
gives only `Koti.K1`, `Koti.K2`, and `Koti.K4`; the both-designated
`Koti.K3` corner is precisely the omitted glut.  Here `K3` names the logic and
`Koti.K3` names a corner, so the shared abbreviation carries no type identity.

For sets of possible values, `empty_set_separates_universal_and_existential`
isolates the quantifier choice: the empty set makes both universal designation
conditions vacuously true and both existential conditions false.
`singleton_universal_eq_existential` proves agreement when there is exactly one
possible value.  The complete theorem inventory and interpretation boundary is
in [CATUSKOTI_K3_FDE.md](CATUSKOTI_K3_FDE.md).

## 13. Four pramāṇa treatise architectures

[BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean),
[BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean),
[BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean), and
[BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean)
reconstruct selected proof obligations rather than complete texts.

The *Pramāṇasamuccaya* layer separates perceptual evidence from conceptual
classification and subject inference from public presentation.
`raw_observation_does_not_entail_conceptual_classification` and
`public_form_and_subject_warrant_are_not_identical` give finite boundaries in
both places.  The *Pramāṇavārttika* layer defines an operational reliability
interface, derives local causal efficacy only for presented objects, and
routes intrinsic and effect reasons through explicit pervasion certificates.

The momentariness module makes `SattvaPervasion` a named bridge from existence
to numerical momentariness.  `sattva_from_rooted_transport` derives it from
rooted backward effect transport and unique effect time, while
`finite_nonuniformity_is_not_momentariness` and
`finite_root_recovery_without_uniqueness_is_insufficient` isolate the two
missing-premise failures.

The *Tattvasaṃgraha* layer uses scoped debate rules and certificates rather
than one global theory.  Composition needs both scopes and an explicit
connector.  `debate_coverage_does_not_entail_joint_consistency`,
`one_refutation_does_not_prove_all_buddhist_alternatives`, and
`chapter_local_premise_does_not_become_universal` block three invalid moves
from selected refutations to an exhaustive positive system.  Full theorem and
source boundaries are in [PRAMANA_TREATISES.md](PRAMANA_TREATISES.md).

## Verification and remaining work

Verified on 2026-09-19: all 115 Lean files passed an isolated source build
with warnings treated as errors. The checker also verified aggregate import
closure and Lake roots and rejected admitted declarations and project-defined
axioms. The name, text, machine-readable index, and whitespace guards passed.

The names cited here are checked by `tools/check_names.py`. Reproduce with:

```sh
sh tools/check-lean.sh
python3 tools/check_names.py
python3 tools/check_text.py
python3 tools/make_index.py --check
python3 tools/check_publication.py
```

What remains is premise and evidence work: supply the proof fields of the
certificates from independently motivated interpretations, establish the
rooted directed relation and concrete apoha comparison rule intended by a
reading, justify the selected pramāṇa and Yogācāra bridge premises, map the
four treatise interfaces to edition-specific passages, and
construct an explicit matrix isomorphism when classifying a new finite base.
Applying K3, FDE, or either set-quantifier policy to a historical fourfold
passage likewise requires an independently defended interpretation.
Edition-specific lexical data must be extended and maintained separately from
claims about translation or construal. Neither universal dependence, a
historically unique reading, an external-object ontology, nor an empirical
theory of release is proved here. Isabelle sources and the original
clause-coverage record are unchanged.
