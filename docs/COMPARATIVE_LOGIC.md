# Thirty-six comparative logic interfaces in Lean

Role: `supplement`

Lifecycle: `active`

Lean/static audit: 2026-09-20

Isabelle/PDF receipt: 2026-09-20 (Isabelle2025-2, 35-theory session; full
`sh verify.sh` run)

## Scope

Six batches add thirty-six Lean modules for bounded comparisons across Buddhist,
Jaina, Sāṃkhya, Vedānta, Nyāya, Mīmāṃsā, Pāṇinian grammar, Tibetan, Korean
Buddhist, Pāli Abhidhamma, Abhidharma, Later Mohist, and early Chinese argument
traditions.  Each
module states a small proof interface, proves what
follows from it, and supplies a finite model for at least one tempting
converse or omitted premise.

The names identify the historical discussions motivating the interfaces.
They do not claim critical-edition coverage, doctrinal truth, or a unique
translation into modern logic.  In particular, semantic consequence,
dialectical commitment, analogical relevance, epistemic entitlement,
coextension, and ontological identity remain different predicates.

## Autonomous inference and consequence refutation

[BuddhistComparativeLogic/Buddhist/Pramana/SvatantraPrasanga.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/SvatantraPrasanga.lean)
gives every complete inference argument its own indexed claim language and
interprets the reason, pervasion, and conclusion labels with the existing
`InferenceScope` semantics.  `challenge_sound` proves the generated
consequence sound.

A `SvatantraCertificate` then combines a `Nyaya.SemanticProof` with an actual
`TibetanDebate` state in which the opponent is committed to the subject reason
and pervasion.  `SvatantraCertificate.sound_and_acceptable` proves both the
subject thesis and legality of the acceptance move; semantic truth is never
inserted into the commitment ledger by definition.

The finite audits separate three boundaries:

- `semantic_soundness_does_not_force_dialectical_acceptance` places a sound
  smoke/fire proof in a state whose defender does not accept its pervasion;
- `missing_subject_reason_blocks_both_layers` retains pervasion and a positive
  example while the disputed subject lacks the reason and thesis; and
- `refutation_does_not_establish_an_independent_thesis` uses the generic
  `Prasanga.exhaustive_reductio` interface and refutes the transfer from an
  opponent's rejected claim to an independent proponent thesis.

This is an interface for comparing proof obligations.  It does not turn the
later Tibetan labels “Svātantrika” and “Prāsaṅgika” into two exhaustive Indian
schools or attribute this exact calculus to Bhāviveka or Candrakīrti.

## Later Mohist standards and kind extension

[BuddhistComparativeLogic/Comparative/ChineseThought/MohistCanons.lean](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/MohistCanons.lean) separates an
object's kind, a name's actual designation, and the kinds that the name
admits.  `Naming.Regular` is an auditable name-object agreement condition;
designation does not imply it by definition.

A `Standard` carries a distinct positive illustration and a selected common
kind.  `TuiLeiCertificate` additionally requires the target reason and a
kind-bounded semantic relevance rule.  Its `toSemanticProof` method reuses the
Nyāya semantic certificate only after restricting the reason to the selected
kind, and `TuiLeiCertificate.sound` establishes the target conclusion.
`global_pervasion_of_reason_confinement` gives a sufficient condition under
which the local rule may be promoted to the repository's global pervasion
predicate.

`tile_extension_nonvacuous` supplies a target, a distinct source, inhabited
name extensions, and a negative outside object.  In the opposing two-object
model, `parallel_form_and_same_kind_do_not_license_extension` retains a common
kind, a positive source, target reason, and identical expression frames while
the target conclusion and relevance rule fail.  Finally,
`mere_designation_does_not_ensure_name_object_fit` isolates name
misapplication.

The model therefore treats `tui lei` as relevance-sensitive analogical
extension.  It does not claim that the Mohist Canons contain a modern notion
of propositional consequence.

## Gaṅgeśa: pervasion, reflection, and counterconditions

[BuddhistComparativeLogic/Comparative/Nyaya/Tattvacintamani.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Tattvacintamani.lean) reuses
the common `Anumana` carrier and Nyāya pervasion while adding an explicit
condition predicate.  `restricted_vyapti_iff_conditional` identifies global
pervasion of the restricted reason with the corresponding conditional rule.

An `UpadhiDiagnostic` follows the standard extensional pattern: its condition
covers every thesis case but fails to cover a reason-bearing witness.
`UpadhiDiagnostic.witness_lacks_thesis` derives failure of the thesis at that
witness, and `defeats_unrestricted_vyapti` then refutes the unqualified rule.
A separate `RestrictionRepair` carries the stronger conditional rule needed
to recover qualified inclusion.  `RestrictionRepair.toConditionedParamarsa`
and `sound_after_adding_condition` still require the reason and condition at
the disputed subject.  A `Paramarsa`
packages those subject and pervasion obligations into the existing
`Nyaya.SemanticProof`; it excludes the three explicitly represented defects.

The four-site fire/smoke model contains wet positive sites, a dry
reason-bearing counterinstance, and a wet pond with neither reason nor thesis;
the repair condition therefore has a different extension from the thesis.
`conditional_vyapti_needs_subject_condition`,
`vyapti_without_subject_application_is_insufficient`, and
`subject_thesis_does_not_entail_vyapti_or_paramarsa` expose the three missing
directions.  The types are extensional proof interfaces rather than a complete
encoding of Navya-Nyāya technical language.

## Mīmāṃsā entitlement and independent knowledge sources

[BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaEpistemology.lean](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaEpistemology.lean)
keeps source generation, prima-facie validity, defeat, and truth independent.
The six-source enumeration is explicitly `BhattaPramana`, limiting this
interface to the Bhāṭṭa/Kumārila-oriented account.  A separate
`SvatahPramanya` bridge carries generation to initial qualification; an
`InitiallyQualified` cognition becomes `Undefeated` only after excluding a
defeater, and `EpistemicModel.true_of_undefeated` still requires a separately
stated `TruthBridge`.  `generation_alone_does_not_supply_initial_qualification`,
`initial_qualification_does_not_mean_indefeasible_truth`, and
`undefeated_needs_truth_bridge` witness the three boundaries.

Given observation at the subject, the frame's exhaustive alternative and an
`ArthapattiFrame.Certificate` excluding its residual branch reach the
postulate through `Nyaya.SemanticProof`.  In the three-case family,
`licensed_certificate_iff_claim` proves that a certificate exists exactly when
the disputed target claim holds; the postulate-only and residual-only cases
keep observation, postulation, and residual possibility extensionally apart.
`arthapatti_needs_residual_exclusion` keeps the residual alternative true in a
finite open frame.  This shared logical form does not identify historical
postulation with inference.

`visible_noncognition_sound` reuses the existing visibility theorem, and
`noncognition_needs_perceptibility` exhibits a present but imperceptible and
unperceived object.  The final `SupportSystem` supplies distinct finite
Bhāṭṭa support profiles for perception, inference, comparison, testimony,
postulation, and non-cognition.  `finite_sources_not_reducible` proves
non-reduction in this model; it is a consistency witness, not a claim that
all Mīmāṃsā accounts give the sources disjoint extensions.

## Tibetan definition certificates

[BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Definitions.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Definitions.lean)
represents a defining feature requirement, a definiendum, and a concrete
basis.  A `DefinitionCertificate` verifies coextension, basis fit, and an
independent `DefinitionStandard` license.  The license remains parameterized
so that an extensional coincidence cannot certify its own historical or
pedagogical admissibility.

`DefinitionCertificate.sound_and_grounded` builds both the existing
feature-grounded apoha pair and a `Pramanasamuccaya.GroundedConcept`.
`groundedConcept_extension_eq` checks their positive extensions agree, and
`classified_iff_not_excluded` transports the apoha exclusion theorem.

The red/ruby certificate gives an inhabited positive model.
`coextension_and_basis_do_not_entail_license` supplies a standard under which
the same proposal is unlicensed.  A separate two-object, two-feature model
proves `extension_and_basis_do_not_determine_requirement`: distinct feature
requirements can have the same extension, basis, and defining condition.

## Dharmakīrti's relation critique

[BuddhistComparativeLogic/Buddhist/Pramana/Sambandhapariksa.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Sambandhapariksa.lean)
separates an ordinary `Prop`-valued binary relation from a connector living in
another type.  `Presentation.RepresentationBridge` is the explicit extra
premise connecting them.  `ordinary_relation_does_not_supply_a_connector`,
`connector_does_not_supply_the_relation`, and
`bridge_is_an_additional_assumption` prove both directions independent;
`linked_presentation_bridge` supplies a nonempty positive instance.

`Reified.EndpointIdentity` states the strong premise identifying a connector
with both endpoints, and from that explicit premise
`Reified.related_endpoints_equal` derive collapse.  The three-element
`distinctLink` model proves `reification_does_not_collapse_endpoints`.

Likewise, `RegressLaw` explicitly supplies an active successor whose natural
level strictly increases.  Given an active starting connector,
`RegressLaw.hierarchy_unbounded` then constructs a witness at every finite
offset.  A singleton connector presentation with a verified bridge proves
`finite_reification_does_not_force_regress`.
The final examples parameterize own-being and reuse `DependenceModes` and
`AssumptionAudit` to keep conceptual dependence, causal dependence, and
exclusion of own-being apart.  `relation_claim_not_own_of_invariance` needs an
explicit invariance criterion, while
`local_dependence_without_invariance_keeps_own` retains the same dependence
edge together with own-being when that criterion is absent.

## Vādanyāya: truth, proof, and procedural result

[BuddhistComparativeLogic/Buddhist/Pramana/Vadanyaya.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Vadanyaya.lean) gives proponent and
opponent different public obligations.  `properTarget` assigns the modeled
faults by role, while `occurred`, `isRealFault`, and `classifyFault` separate a
real fault from a pseudo-fault.  `classifyFault_real_iff` and
`classifyFault_pseudo_iff` expose the Boolean check as propositions;
`fault_status_complete`, `fault_status_exclusive`, and
`role_obligations_are_asymmetric` check its two-way coverage and role split.

The independent `outcome` checker returns `proponentWon`, `proponentLost`, or
`undecided` from the public round record.  `outcome_complete`,
`outcome_unique`, `outcomes_pairwise_exclusive`, and `outcome_determined`
establish totality and determinacy.  Neither the round record nor the outcome
contains a thesis proof.  `SemanticProof` instead reuses the Nyāya certificate,
and `PubliclyAcceptable` reuses the Tibetan commitment ledger.

The finite records make every status nonempty.  More substantively,
`correct_argument_need_not_win_procedurally` pairs the valid smoke/fire proof
with a lost round, `procedural_loss_does_not_entail_false_thesis` keeps its
thesis true, and `procedural_victory_does_not_entail_true_thesis` pairs a
concession-based win with the false subject claim of the existing `nofire`
argument.  This small audit is motivated by Dharmakīrti's treatment of
role-specific grounds for defeat.  It is not a transcription of the work's
full list or an identification with Nyāya's twenty-two grounds.

## Constant co-apprehension and numerical identity

[BuddhistComparativeLogic/Buddhist/Yogacara/Sahopalambha.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Sahopalambha.lean) assigns
objects, cognitions, times, and observation tokens different types.
`ConstantCoapprehension` is tokenwise biconditional registration;
`ObservationallyNonseparate` is equality of the two traces; and
`NumericallyIdentical` uses a separate relation on the tagged object/cognition
sum.  `trace_equality_of_constant_coapprehension` and
`time_profile_of_constant_coapprehension` derive only observable
nonseparation.  `numerical_identity_of_explicit_bridges` reaches identity
for a pair with an `externallyCoupled` witness after both a
`CouplingTracksObservations` premise and the disputed `IdentityFromExtension`
principle are supplied.

The two-time `coupledModel` registers a blue patch and its awareness together
at every moment while its identity relation is actual equality on the tagged
sum.  `complete_coapprehension_does_not_force_identity` therefore retains
external coupling, complete co-apprehension, and trace equality while the two
differently tagged elements remain unequal.  In `oneWayModel`,
`one_direction_does_not_force_biconditional_or_identity` uses a
cognition-only token to refute the converse accompaniment.  Projection
theorems connect joint episodes to the existing *Ālambanaparīkṣā*,
Viṃśatikā-model, and Pramāṇasamuccaya interfaces without adding identity.
The module consequently leaves the historical force of `abheda` open between
numerical identity and weaker nonseparation readings.

## Śāntarakṣita's one-or-many argument

[BuddhistComparativeLogic/Buddhist/Madhyamaka/Ekanekaviyoga.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Ekanekaviyoga.lean) treats
`Intrinsic`, `TrulyOne`, and `TrulyMany` as primitive analytical predicates,
rather than carrier-cardinality tests.  `DilemmaPremises` records the explicit
one-or-many coverage premise and rejection of both horns;
`no_intrinsic_of_one_many_rejection` then eliminates intrinsic existence.
A separate `ConstitutionBridge` states that a truly many subject has a truly
one constituent together with a witnessed mereological dependence edge.
`rejects_many_from_constitution`, `dilemmaOfConstitution`, and
`no_intrinsic_via_constitution` show exactly how that bridge closes the many
horn.  With the existing invariance criterion,
`many_is_empty_by_mereological_dependence` yields only emptiness in the shared
dependence projection.

`horns_rejected_but_intrinsic_survives_without_coverage` supplies an intrinsic
third case when exhaustiveness is absent.  The singleton
`missingConstitutionModel` is stipulated truly many and proves both
`constitution_bridge_is_substantive` and
`many_horn_survives_without_constitution_bridge`; this also checks that
“truly many” has not been reduced to Lean cardinality.  Finally,
`no_intrinsic_and_conventional_existence_coexist` and
`no_intrinsic_does_not_deny_conventional_existence` retain a conventional
witness through the existing two-truths index.  The formalization is a scoped
proof architecture, not a claim that the modern predicates uniquely translate
the *Madhyamakālaṃkāra*.

## Pāli Yamaka as bilateral extension checking

[BuddhistComparativeLogic/Buddhist/Abhidharma/Yamaka.lean](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Yamaka.lean) stores two decidable term
extensions and an explicitly complete finite enumeration.  `leftOnly` and
`rightOnly` compute the first counterexample to each inclusion direction, and
`boundaryReport` preserves those objects.  Its `classify` function returns
`equal`, `leftProper`, `rightProper`, or `incomparable` from the two optional
witnesses.

The four `classify_*_iff` theorems characterize every result by its two
inclusions or concrete failed-inclusion witnesses.  `classification_complete`
and `classification_exclusive` prove that the executable result is total and
unambiguous.  In the two-object audit,
`reports_retain_proper_boundary` returns the surplus object, while
`one_direction_does_not_distinguish_equality_from_proper_inclusion` shows that
the same `left ⊆ right` answer occurs for both equality and strict inclusion.
`right_proper_and_incomparable_boundaries_nonvacuous` realizes the other two
categories and retains separate left-only and right-only objects in the
incomparable report.
The four constructors classify two term extensions.  They are not four truth
values and do not turn the historical *Yamaka* into a propositional matrix.

## The White Horse distinction

[BuddhistComparativeLogic/Comparative/ChineseThought/WhiteHorse.lean](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/WhiteHorse.lean) computes each
name's extension from a feature profile and a separate `SearchRequest`.
`white_horse_included_in_horse` establishes the qualified-to-unqualified
direction in a three-animal model, while the black stallion makes
`white_horse_extension_strictly_included` strict.  In the same inhabited
model, `inclusion_does_not_identify_name_meaning_or_request` retains distinct
public names, meanings, and feature requests.  `stable_naming_regular`
connects the lexicon to the Later Mohist name/object check, and
`white_horse_triad_coextensive_and_instantiated` connects it to the Tibetan
definition triad.

The converse boundary uses two feature requirements already known to generate
the same extension.  `same_extension_does_not_determine_search_request` proves
that the requests remain distinct even there.  The module therefore isolates
extension inclusion, extension equality, name identity, meaning identity, and
selection conditions without choosing among the many historical readings of
the *White Horse Discourse*.

## Jayarāśi: grounding and finite extrapolation

[BuddhistComparativeLogic/Comparative/Skepticism/Jayarasi.lean](../lean/BuddhistComparativeLogic/Comparative/Skepticism/Jayarasi.lean) first separates local
definition adequacy from the support qualifying an epistemic method.
`RankedGrounding` requires every dependency to lower a natural rank and every
dependency-free base to carry a proof-bearing `Certified` witness.
`Qualification` then permits either direct base certification or that complete
grounding.  `independent_and_ranked_routes_nonvacuous` instantiates both paths
for perception and inference.

In the two-node cycle, both local definitions are adequate but neither node is
independently based.  `circular_system_has_no_ranked_grounding`,
`circular_system_has_no_independent_certificate`, and
`circularity_alone_does_not_qualify` show that mutual reference supplies
neither permitted route.  This targets the represented circular support; it
does not refute every coherent or mutually informative definition.

The second audit defines agreement on a finite sample separately from global
pervasion.  `finite_sample_does_not_entail_global_pervasion` retains two
observed positive cases and an unseen reason-bearing counterexample.
`CoverageCertificate` combines certified sample agreement with the explicit
claim that the sample covers every reason case;
`CoverageCertificate.toGlobalPervasion` and `.toParamarsa` then reuse the
Tattvacintāmaṇi interface.  `coverage_bridge_nonvacuous` keeps two sampled
reason cases and an unsampled non-reason case.  These conditional diagnostics
are motivated by Jayarāśi's challenges to pramāṇa definitions and tests; they
do not establish unrestricted scepticism.

## Ratnakīrti: determining pervasion

[BuddhistComparativeLogic/Buddhist/Pramana/Vyaptinirnaya.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Vyaptinirnaya.lean) separates
agreement on a registered list from a global reason-to-thesis rule.  A
`CausalSchema` supplies only a conditional production rule.  Its
`ScopeCertificate` additionally covers every reason case, enables the rule in
that scope, records noncognition of a defeating condition, and states the
detection premise that makes that noncognition probative.
`ScopeCertificate.excludesUpadhi` derives scoped absence from those last two
fields; `ScopeCertificate.toPervasion` then constructs the existing global
`InferenceScope.Pervasion`.  With subject possession,
`ScopeCertificate.toDeductiveCertificate` exports the result to the common
pramāṇa-synthesis interface.

The smoke/fire model has two reason-bearing cases and a negative lake outside
the covered scope; `causal_model_nonvacuous` witnesses the complete positive
route.  In contrast,
`finite_observations_and_upadhi_search_are_insufficient` retains two observed
agreements and no observed defeater while an unseen case refutes both global
pervasion and global defeater-freedom.
`every_finite_registry_admits_an_unseen_countercase` gives the same boundary
for an arbitrary registered list by extending its carrier with one new case.
This reconstruction targets causal and scope obligations around
*Vyāptinirṇaya*; it is not a general theorem that observation determines
necessity.

## Jaina necessary connection and two-member inference

[BuddhistComparativeLogic/Comparative/Jaina/JainaInference.lean](../lean/BuddhistComparativeLogic/Comparative/Jaina/JainaInference.lean) gives a
modal model a distinguished actual world that is explicitly accessible from
itself.  `OtherwisePossibleAt` is an accessible
reason-without-thesis case, while `AnyathanupapattiAt` excludes such a case.
`ModalModel.thesis_of_reason_and_anyathanupapatti` classically uses actual
accessibility to derive the thesis at one locus.  The globally quantified
form yields ordinary actual-world inclusion through
`actualInclusion_of_globalAnyathanupapatti`.

A `TwoMemberInference` records the public thesis/reason order, the subject
reason, and the subject-specific modal link.  Its `sound` theorem needs no
example.  Export to `Nyaya.SemanticProof` requires the independent global-link
certificate `GlobalBridge`, because a subject proof does not contain global
pervasion.  The accessible
two-world model proves
`actual_inclusion_does_not_entail_modal_pervasion`: actual inclusion coexists
with an alternative countercase.  The singleton
`two_member_inference_needs_no_positive_example` supplies a sound semantic
proof while a positive example distinct from the subject is impossible.  The
modal frame is a bounded reconstruction of `anyathānupapatti`, not an
exhaustive Jaina theory of inference or a replacement for the sevenfold
predication module.

## Vasubandhu's substantial-person dispute

[BuddhistComparativeLogic/Buddhist/Abhidharma/Pudgala.lean](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Pudgala.lean) types a history of the
five aggregate dimensions separately from persons, times, and causal-profile
states.  `ConventionallyDesignated` therefore does not insert a further
substance.  `ExtraPersonCandidate` instead combines substantiality,
separateness, causal activity, and profile immutability.

`ExclusionPremises` exposes four needed bridges: causal-or-conceptual
dependence coverage, incompatibility of conceptual dependence with
separateness, a witnessed aggregate change, and propagation of that change to
active causal dependents.
`no_active_immutable_separate_substantial_person` eliminates the candidate by
the two dependence cases, while
`conventional_designation_compatible_with_exclusion` preserves the
conventional predicate.  `changing_person_positive_instance` and its
nonvacuity theorem instantiate this premise package with an active dependent
continuant and a mutable substantial proposal.

Two finite boundaries isolate the omitted steps.
`bare_dependsOn_does_not_exclude_a_stable_extra_person` retains aggregate
change, causal support, and an active immutable extra candidate when change
propagation is absent.  In a separate two-stage model,
`causal_memory_responsibility_do_not_imply_numerical_identity` preserves
causal, mnemonic, and responsibility continuity while the stages remain
unequal.  These predicates reconstruct one proof boundary in the ninth
chapter of the *Abhidharmakośabhāṣya*; they do not define a neutral historical
Pudgalavādin position or eliminate ordinary personal designation.

## Śrīharṣa: definition defects and epistemic luck

[BuddhistComparativeLogic/Comparative/Vedanta/Sriharsa.lean](../lean/BuddhistComparativeLogic/Comparative/Vedanta/Sriharsa.lean) searches explicitly
complete finite object and rule lists for underextension, overextension,
direct reciprocal definition dependencies, and nonuniform classification. Its
`DefectReport` retains the first witness of each kind, and the four local
soundness theorems validate those witnesses.
`report_clean_iff_passes_stated_checks` proves soundness and completeness of
the joint checker against extensional exactness, absence of direct reciprocal
dependencies, and the stated profile-uniformity test.
`defective_report_retains_all_witnesses` realizes all four failures, while
`clean_report_is_nonvacuous_and_complete` realizes a positive report.  The
explicit `three_step_cycle_is_outside_direct_mutual_test` boundary contains a
directed three-edge cycle that passes the pairwise dependency test; the module
therefore does not advertise general graph acyclicity.
`extensionallyExact_iff_triad_coextensive` connects only the extensional
component to the Tibetan definition interface; historical licensing remains
separate.

The second half separates local truth from a route that tracks truth across
relevant alternatives.  Both
`lucky_shell_true_but_not_reliable_or_knowledge` and
`mist_fire_true_result_is_not_reliable_knowledge` contain an actually true
affirmation and an explicit nearby failure, and the former is projected into
the Mīmāṃsā entitlement/defeater interface.  This is a finite diagnostic
inspired by the *Khaṇḍanakhaṇḍakhādya*.  It does not infer that every possible
definition fails from the represented candidates.

## Fazang's rafter-and-house mereology

[BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Fazang/Mereology.lean](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Fazang/Mereology.lean) assigns
parts, wholes, functions, and intervention contexts different types.  The six
characteristics form an explicit index, while `SixfoldProfile` gives a scoped
mathematical reading through required-function coverage, particular
contribution, co-active whole-forming status, differentiated contribution,
integration, and disintegration.

`IndispensableFor` contains a controlled part-removal witness that loses a
required function.  Given the separate disintegration law,
`whole_depends_on_indispensable_part` turns this into failure of the whole;
coverage and `RoleGrounding` then yield mutual dependence through
`sixfold_profile_with_indispensability_yields_mutual_dependence`.
That consequence uses the profile's coverage and disintegration fields; it
does not claim that all six fields are individually necessary for dependence.
`load_bearing_positive_instance` realizes the complete package with two
distinct rafters and two required functions.  Its reverse dependence witness
uses `WithdrawsOnlyWhole`, which withdraws the whole while preserving every
part-presence fact.  `CommonIdentity` additionally requires one manifested
context with both part roles active, and `DifferentiatedIdentity` requires a
function on which the two contribution predicates differ;
`differentiated_identity_excludes_strong_interpenetration` proves that this
last condition rules out full functional interchangeability.

The optional-ornament model proves
`optional_part_does_not_entail_strong_dependence`, even with a controlled
removal and coverage of all required functions.  The static two-member model
proves `mere_collection_does_not_entail_dependence_or_interpenetration` while
retaining witnessed common status and differentiated contributions.  In this
module, common identity is witnessed co-active whole-forming status and strong
interpenetration is functional interchangeability; neither is asserted to be
the unique meaning of Fazang's six characteristics.

## A staged signification reconstruction inspired by Bhartṛhari

[BuddhistComparativeLogic/Comparative/Grammar/Bhartrhari.lean](../lean/BuddhistComparativeLogic/Comparative/Grammar/Bhartrhari.lean) gives a bounded
reconstruction in which token availability and denotation are indexed by a
vocabulary stage.  `UnsignifiableAt` denies a successful designator at one
stage, whereas `AbsolutelyUnsignifiable` quantifies over every stage.  A
successful expression therefore contradicts the absolute claim by
`absolute_unsignifiability_excludes_success` but says nothing inconsistent
about an earlier vocabulary.

`FiniteVocabulary.firstSignifier` searches an explicitly complete token list;
`firstSignifier_none_iff_unsignifiable` proves the executable failure test
sound and complete.  The three-token sample preserves an ordinary base name,
adds a later-stage `avacyaName`, and proves
`base_unsignifiability_compatible_with_later_denotation`.  The target is
unexpressed in the base stage and successfully denoted in the extension, so
the distinction is inhabited rather than an empty-language artifact.  The
model calls this a vocabulary extension; it does not encode a typed
object-language/metalanguage relation.

A separate `Discourse` assigns each utterance token a stage and time and
requires references to target earlier utterances.
`finite_discourse_is_nonvacuous_and_nonselfreferential` contains a real
later-to-earlier reference while `Discourse.no_self_reference` rules out the
simultaneous diagonal case under that explicit discipline.  Finally,
`bivalent_negation_has_no_fixed_point` and
`fde_negation_has_glut_and_gap_fixed_points` compare modern matrices.  The
module expressly does not identify Bhartṛhari's analysis of *avācya* with a
language hierarchy, FDE, or dialetheism.

## Navya-Nyāya-inspired qualified absence

[BuddhistComparativeLogic/Comparative/Nyaya/NavyaNyayaAbsence.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/NavyaNyayaAbsence.lean)
assigns the locus, counterpositive, delimiter, and relation to separate types.
`QualifiedPresence` combines only the supplied relation and delimitation;
`QualifiedAbsence` negates that exactly indexed claim.  An
`AbsenceCertificate` retains perceptibility, exhaustive search, and
non-cognition as three independent premises.  Its `sound` theorem uses the
model's explicit detection law, so bare failure to cognize is never defined
as absence.

`throughMimamsaNonCognition` exports the same checked result through the
existing Mīmāṃsā non-cognition interface after the four indices are fixed.
The inhabited storeroom model contains a positively cognized cloth as well as
the certified absence of a visible pot under contact in the store.  In the
hidden-jewel model,
`noncognition_alone_does_not_entail_qualified_absence` keeps the jewel present
while it is imperceptible, unsearched, and uncognized.  The twin-index model
then proves `coextension_does_not_identify_indices`: equal qualified-presence
profiles do not identify two counterpositives, two delimiters, or two
relations.  This is a bounded modern reconstruction of relationally qualified
absence, not a complete translation of Navya-Nyāya absence terminology or an
identification with the Mīmāṃsā theory of non-cognition.

## Two bounded Mīmāṃsā sentence-meaning architectures

[BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaSentenceMeaning.lean](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaSentenceMeaning.lean)
keeps word occurrences and their roles distinct.  `Abhihitanvaya` first maps
each word to an independent lexical meaning and then composes meaning-role
pairs.  `Anvitabhidhana` lets a context supply connected occurrence meanings
before synthesis.  Their connected-meaning types need not coincide.

A `CompositionBridge` must separately decode each contextual occurrence and
show that synthesis agrees with composition after decoding.
`interpretationsAgree` derives equality only from those obligations.  The
three-word positive model realizes both architectures and the bridge, while
`without_composition_bridge_architectures_can_disagree` supplies a contextual
synthesizer with a different result.  In the role-and-order audit,
`same_lexical_extensions_do_not_determine_sentence_meaning` gives the same
ordered lexical extensions different subject and object roles, and
`reordered_sentence_uses_same_lexical_inventory` verifies by list permutation
that reordering preserves the inventory.  The former theorem packages that
permutation with the resulting change of sentence meaning.
`StagedLexicalBridge.occurrenceMeaningIsSignifiable` is a typed connection to
the Bhartṛhari-inspired vocabulary API; it does not identify Bhartṛhari with
either Mīmāṃsā account.  The module compares two small composition
architectures and does not claim that either is a complete modern semantics
or the unique historical formulation of the debate.

## Udayana's effect-to-maker inference

[BuddhistComparativeLogic/Comparative/Nyaya/Nyayakusumanjali.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Nyayakusumanjali.lean)
uses effecthood as the reason and `HasIntelligentMaker` as the deliberately
modest thesis.  A qualified maker must know the selected object's materials,
will it, and make it.  `MakerCertificate` keeps subject effecthood apart from
the universal `MakerPervasion`; its `sound` theorem reaches only the
existential subject conclusion.  `toNyayaSemanticProof` and
`toDeductiveCertificate` are typed exports to the repository's Nyāya and
pramāṇa proof APIs.

The finite workshop supplies pot and cloth effects with different artisans, a
negative stone case, a positive comparison example distinct from the subject,
and a checked pervasion.  Even there,
`one_maker_does_not_supply_omniscience_or_eternity` shows that a unique local
maker need not know every represented object's materials or exist at every
represented moment.  The mixed pot-and-sprout model proves both
`natural_effect_without_intelligent_maker` and
`positive_artifact_does_not_establish_global_pervasion`.  Finally,
`multiple_makers_do_not_supply_uniqueness_omniscience_or_eternity` realizes
two distinct makers while all three stronger properties fail.  This bounded
audit is inspired by the *kāryāt* route in Udayana's
*Nyāyakusumāñjali*; it is neither the complete work nor a proof of God.

## Reflexive presentation and later memory

[BuddhistComparativeLogic/Buddhist/Yogacara/Svasamvedana.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Svasamvedana.lean) assigns
episodes, presented objects, traces, and memories distinct types.
`ReflexivityCertificate` supplies the disputed transition from a
nonconceptual appearance to self-presentation.  `TracePersistenceCertificate`
then supplies trace formation, retention, temporal priority, and matching
recall output.  From these explicit laws,
`object_presentation_yields_reflexivity_and_later_memory` establishes a later
source attribution.  The independent `TraceDiscrimination` conditions are
sufficient for exact source uniqueness by
`unique_source_of_trace_discrimination`.

`toSelfAwarenessModel` and `self_presentation_via_pramanasamuccaya` connect
the certificate to the existing Pramāṇasamuccaya interface while retaining
the episode in the presented datum.  The positive two-path model has distinct
episodes, traces, memories, and uniquely attributable sources.  The
co-apprehension boundary proves
`complete_coapprehension_and_object_cognition_do_not_force_self_presentation`
against the existing *sahopalambha* model.  In the second boundary model,
`same_memory_output_does_not_determine_identity_or_source` keeps two memory
tokens distinct and leaves a single recall ambiguously sourced despite equal
outputs.  This is a bounded Dignāga-Dharmakīrti-inspired test bench; reflexive
awareness here is not awareness of an enduring self.

## A bounded Pāṇinian priority-rewrite interface

[BuddhistComparativeLogic/Comparative/Grammar/PaniniDerivation.lean](../lean/BuddhistComparativeLogic/Comparative/Grammar/PaniniDerivation.lean)
separates a finite raw rule inventory from an explicit priority resolver.
Every applicable rule in `FiniteRankedRewrite` must lower a natural-number
rank.  `PrioritySystem` additionally requires its chosen rule to be
applicable, complete against the inventory, and maximal under the supplied
priority.  The executable `run` and `normalize` functions therefore terminate,
and `normalize_is_normal` proves that rank-derived fuel reaches a raw normal
form.

Normal-form uniqueness is kept separate:
`deterministic_normal_forms_unique` assumes determinism of the selected step
relation.  The three-term positive model reduces input through a stem to an
output.  In `criticalPairInventory`, two individually rank-decreasing rules
send one source to two distinct raw normal forms, so
`raw_critical_pair_has_distinct_normal_forms` refutes determinism and the
unlicensed uniqueness step.  `leftBiasedResolution` shows how extra resolver
data selects one branch.  `normalized_output_denotes_bhartrhari_target`
supplies a typed projection of the sample normal form into the existing
Bhartṛhari staged-expression model.  Numeric priority and list order are
modern formal devices here; the module neither encodes the full
*Aṣṭādhyāyī* nor selects a unique historical reading of *vipratiṣedha*.

## A Wŏnhyo-inspired local-theory gluing audit

[BuddhistComparativeLogic/Buddhist/KoreanBuddhism/WonhyoHwajaeng.lean](../lean/BuddhistComparativeLogic/Buddhist/KoreanBuddhism/WonhyoHwajaeng.lean) gives
each context its own statement scope and truth predicate.  `OverlapAgreement`
requires any two contexts to agree only on shared scope, while `Covers`
requires every statement to occur somewhere.  A `GluingCertificate` contains
only these structural conditions.  It stores no selected statement and no
local conclusion.

`glued_value_extends_all` proves that the explicit global `GluedValue`
restricts to each local theory.  `glued_value_has_covered_restriction` uses
coverage to choose an actual local site for every statement and overlap
agreement to identify its value there.  `preserves_local_conclusion` then
transports a separately supplied in-scope local proof.  The three-context harmony model
checks both agreement and coverage, keeps conventional and analytic domains
different, and glues a real appearance claim.  It connects by actual types to
`StandpointFrame` through `toStandpointFrame` and to premise provenance
through `harmonyAppearanceEvidence` and
`provenance_bearing_local_conclusion_glues`.

The first finite boundary assigns `P` and the syntactic formula `¬P` to two
different locally non-opposed contexts;
`erasing_context_collects_P_and_not_P` shows that taking their unindexed union
collects both.  In the second boundary, two contexts cover the same statement
but disagree on it.  `failed_overlap_blocks_gluing` proves that coverage is
still present while neither a gluing certificate nor any common global
extension exists.  This is a modern bounded reconstruction inspired by
Wŏnhyo's *hwajaeng*.  It does not claim that every dispute is consistent,
that adding a context label settles truth, or that this gluing interface is
Wŏnhyo's own proof theory.

## Sāṃkhya latent causation and the capacity bridge

[BuddhistComparativeLogic/Comparative/Samkhya/Satkaryavada.lean](../lean/BuddhistComparativeLogic/Comparative/Samkhya/Satkaryavada.lean) keeps
`produces`, `capable`, and `latentIn` as independent relations.
`ProductionRespectsCapacity` moves from actual production to capacity, while
`CapacityGrounding` is the additional premise from capacity to latent
presence.  `Certificate.sound` composes those two bridges for one produced
effect.  `Certificate.toDeductiveCertificate` and `sound_via_pramana` export
the same proof through the existing `KaryaHetu` and pramāṇa certificate APIs.

The sesame-seed instance supplies all certificate fields and proves latent
presence of oil.  In `selectiveWithoutGrounding`, production is selective and
every actual production has matching capacity, but `latentIn` is empty.
`selective_capacity_does_not_entail_latent_preexistence` and
`selectivity_and_capacity_law_are_insufficient` therefore isolate the missing
grounding premise.  `capability_alone_does_not_entail_latency` separately
blocks the still weaker move from a bare capacity label.

This is a bounded reconstruction of one argument associated with
*Sāṃkhyakārikā* 9.  It leaves Sāṃkhya cosmology, the identity of manifest and
latent effects, and the defense of the capacity-grounding premise outside the
formal result.

## Jaina production, decay, and duration

[BuddhistComparativeLogic/Comparative/Jaina/JainaChange.lean](../lean/BuddhistComparativeLogic/Comparative/Jaina/JainaChange.lean) gives separate
predicates for carrier existence, modal occurrence, and temporal succession.
`Dhrauvya`, `Vyaya`, and `Utpada` state two-time duration, loss of an old mode,
and acquisition of a new one.  `TriadCertificate.sound` assembles the seven
endpoint facts into `TriadicTransition`; `oldMode_ne_newMode` derives modal
distinctness from loss and acquisition instead of storing it as an extra
premise.

The clay model realizes all three characteristics.  The typed aggregate-stream
adapter shows that one changing coordinate yields acquisition or loss, and
that separate old-loss and new-acquisition witnesses yield the full
certificate.  The naya adapter retains the old mode's positive-then-negative
facts while using the existing exact route for the mixed mode.  The directed
momentariness adapter states the additional existence-tracking premise under
which duration of one carrier conflicts with literal momentariness.

`replacement_without_duration` has an earlier lump and later pot carried by
different tokens, so modal replacement supplies no enduring carrier.
`duration_without_modal_change` has one carrier and one unchanged mode, so
duration alone supplies neither production nor decay.  The reconstruction is
oriented by the traditional `utpāda-vyaya-dhrauvya` formula; it does not reduce
Jaina substance to a modern bearer or derive the triad from sevenfold
predication.

## Five-part commentary certificates inspired by the Vyākhyāyukti

[BuddhistComparativeLogic/Buddhist/Hermeneutics/Vyakhyayukti.lean](../lean/BuddhistComparativeLogic/Buddhist/Hermeneutics/Vyakhyayukti.lean) represents
purpose (`prayojana`), synopsis (`piṇḍārtha`), word meaning (`padārtha`),
discourse connection (`anusandhi`), and objection handling
(`codyaparihāra`) as five independently inspectable obligations.
`CommentaryCertificate` carries all five for one passage.
`AdjacentComposition.composeAdjacent` joins two certified passages with an
explicit connection, and `preservesFivePartCoverage` exposes both sets of
local obligations together with that cross-passage edge.

Typed adapters connect the certificate to recension alignment, Tibetan
definition certificates, internal premise provenance, and a
`Tattvasamgraha.DebateCertificate`.  Concrete instances establish actual
coverage, an inhabited word meaning, and a resolving reply.  In the boundary
model, `sample_relation_readings_distinct` shows that the identity and
non-separation labels are distinct, while
`two_distinct_interpretations_are_certified` shows that both readings pass the
five-part checklist.  `certification_does_not_entail_uniqueness` and
`certification_does_not_entail_truth` separate structural completeness from
an independently supplied truth valuation.

This is an audit of a five-task commentary interface rather than an edition,
translation, or truth procedure.  The complete treatise survives in Tibetan,
and the module does not claim that its checklist fixes one historical
interpretation.

## Eleven typed deployments of non-apprehension

[BuddhistComparativeLogic/Buddhist/Pramana/AnupalabdhiKinds.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/AnupalabdhiKinds.lean) defines
eleven constructors in `Kind`; `eleven_kinds_are_distinct_and_exhaustive`
checks the finite enumeration.  `Evidence` is indexed by a constructor, so
observation, causal production, inclusion, necessary-condition, and
incompatibility premises cannot be exchanged by definitional equality.
`compile` handles every constructor and returns one `NegationCertificate`,
while `compile_sound` extracts the requested metalevel absence.

The direct, effect-absence, and pervader-absence branches pass through the
existing `Anupalabdhi`, `KaryaHetu`, `SvabhavaHetu`, and
`PramanaSynthesis` interfaces.  The remaining branches consume their typed
causal, inclusion, necessity, and incompatibility evidence directly.  Four
inhabited models show that an imperceptible object, a blocked effect, an
alternative cause, and a merely alleged rival each defeat an unqualified
negative inference.

The constructor names follow the eleven applications in the selected
*Nyāyabindu* 2.31–41 passage; 2.42 gathers the ten indirect applications under
own-nature non-apprehension.  The result is a qualified compiler for these
proof shapes; it does not identify this enumeration with shorter or later
taxonomies, or with Mīmāṃsā's treatment of non-cognition as a separate
knowledge source.

## Sensory access in the Hard and White discussion

[BuddhistComparativeLogic/Comparative/ChineseThought/HardWhite.lean](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/HardWhite.lean) separates a
substance's qualities from the senses which register them.
`SeparatelyAccessible` supplies one selective channel for each of two
qualities.  `separatelyAccessibleProfilesDistinct` proves distinct access
profiles, and detection soundness lets `coInhereOfSeparateAccess` recover the
same supplied bearer without adding a substance-separation principle.

The finite stone is white to sight and hard to touch, bears both qualities,
and is the only substance.  Thus
`sensory_separability_does_not_force_separate_substances` and
`universal_separation_to_bearers_bridge_fails` refute the promotion from
sensory distinction to distinct bearers.  Typed projections reuse
`ApohaFeatures`, `WhiteHorse.SearchRequest`, and `Sahopalambha`; the latter
recovers observational nonseparation while retaining a false cross-category
identity predicate.

The received *Hard and White* dialogue has disputed textual history and
metaphysical interpretation.  The module proves only the access-profile and
co-inherence boundary, without selecting a complete reading of the dialogue.

## Gelug-inspired calibration of the object of negation

[BuddhistComparativeLogic/Buddhist/Madhyamaka/NegandumCalibration.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/NegandumCalibration.lean)
defines `TooBroad`, `TooNarrow`, and `Calibrated` for a candidate negandum and
an intended intrinsic-existence predicate.
`candidate_eq_intrinsic_iff_calibrated` proves their extensional equivalence:
the candidate has exactly the intended extension iff it has neither an
overreach witness nor an omission witness.  Conventional retention also needs
the explicit `ConventionalIsNonIntrinsic` separation premise.

The universal candidate captures a conventional cup and is too broad; the
empty candidate leaves a projected intrinsic item and is too narrow.  A typed
adapter turns calibration with an inhabited basis into a
`TibetanDefinitions.DefinitionCertificate`.  Further theorems connect a
calibrated candidate to mode-indexed dependence and to the sutra's emptiness
model.  `fde_glut_blocks_meta_exclusion` records that formula-level emptiness
in the all-glut FDE model does not by itself provide metalevel exclusion of
designated own-being.

This calibration is scoped to a Gelug concern associated especially with
Tsongkhapa.  It is not asserted as a single Tibetan Madhyamaka analysis, and
the intended intrinsic predicate remains an interpretive input.

## Four-cell comparison in Tibetan collected topics

[BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/BsdusGrwa.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/BsdusGrwa.lean) represents two
Boolean predicates through the shared, left-only, right-only, and neither
cells in `Cell`.  `four_possibilities_iff_all_cells_inhabited` equates the
four-possibility condition with a witness in every cell, while
`left_properly_includes_iff_cells` and
`right_properly_includes_iff_cells` characterize the two strict inclusions.
`four_possibilities_implies_bidirectional_nonpervasion` extracts the two
failed inclusion directions from the one-sided witnesses.

A complete `FiniteEnumeration` computes `observedBits`.
`classifyAll_semantic_membership_iff`, `classifyAll_sound`, and
`classifyAll_complete` prove that membership in `classifyAll` is exactly the
corresponding semantic relation; `classifyAll_nodup` rules out duplicate tags.
These relations are not a disjoint partition:
`mutually_exclusive_and_left_inclusion_can_overlap` gives a one-object profile
which satisfies mutual exclusion and proper left inclusion, and the
all-matches report retains both tags.  `classifyPrimary` is deliberately an
ordered first-applicable diagnostic.  `classifyPrimary_sound` validates its
selected tag, but does not turn the overlapping relations into a unique
classification.

`coextensive_iff_definition_triad` connects coextension to the existing
Tibetan definition interface, and
`four_possibilities_refutes_both_vyapti_models` exports both failed pervasion
directions.  The finite
`neither_coextensive_nor_exclusive_does_not_give_four` model retains shared
and left-only witnesses but lacks a right-only witness.  The module therefore
formalizes one extensional collected-topics exercise, without claiming to
exhaust its intensional or pedagogical uses.

## Perception and perceptual semblance

[BuddhistComparativeLogic/Buddhist/Pramana/Pratyaksabhasa.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pratyaksabhasa.lean) keeps
conceptuality, error, and truth as independent fields of `CognitionModel`.
`DignagaCandidate` is the minimal nonconceptual criterion used here;
`DharmakirtiCandidate` adds nonerror, and
`dharmakirti_refines_dignaga` proves inclusion.  A
`StrictRefinementCertificate` carries an actual witness to failure of the
converse, which `StrictRefinementCertificate.proper_subset` exposes.  The
adapter through `toPerceptualEvidence` preserves only the stated
nonconceptuality obligation.

The operational bridge does real work.  `OperationalBridge.toPramana`
requires occurrence, novelty, and content in addition to the stricter
candidate, and explicitly applies `OperationalBridge.nonerroneousReliable`
to obtain reliability.  In the finite model, `clear_moon_is_operational_pramana`
uses `sampleOperationalBridge`, whereas
`two_moons_is_not_operational_pramana` proves that the erroneous two-moons
cognition is not a pramāṇa in that operational model.

The same model proves `two_moons_is_nonconceptual_but_erroneous`,
`true_judgment_is_conceptual_but_true`, and
`nonerror_does_not_entail_truth`.  Thus nonconceptuality, nonerror, truth, and
operational pramāṇa status are not collapsed into one predicate.  The two
candidate criteria are bounded comparison points associated with Dignāga and
Dharmakīrti, rather than complete definitions of their theories of
perception or *pratyakṣābhāsa*.

## Tarka as auxiliary counterfactual reasoning

[BuddhistComparativeLogic/Comparative/Nyaya/Tarka.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Tarka.lean) separates a
`CounterfactualStep` from a `SupportingPramana`.  A `TarkaCertificate` stores
both, but stores neither the positive target nor its double negation.
`TarkaCertificate.removes_doubt` constructively derives only rejection of the
opposite.  `TarkaCertificate.conclude_of_decidable` and
`TarkaCertificate.conclude_of_stability` expose the additional principles
needed to reach the positive target.

`TarkaCertificate.removes_doubt_via_prasanga` factors the first result through
the existing reductio interface.  After the explicit decidability bridge,
`TarkaCertificate.toParamarsa` and `certified_inference_is_sound` connect the
certificate to the shared inference machinery.  The separate
`counterfactual_alone_has_false_target` and
`support_alone_lacks_the_counterfactual` models show why neither component is
independently sufficient.  `fde_glut_does_not_supply_metalevel_exclusion`
also records that formula-level FDE emptiness does not furnish the
`Not`-valued exclusion used by this rule.  This is a bounded reconstruction of
the doubt-removing role of *tarka*, not a claim that it is an independent
pramāṇa.

## Analysis-relative existence in the Abhidharmakośabhāṣya

[BuddhistComparativeLogic/Buddhist/Abhidharma/Analysis.lean](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Analysis.lean)
distinguishes physical and mental analysis in `AnalysisKind`.  A `Framework`
separates transformation, admissibility, and continued recognition.
`ParamarthaSat` means that recognition survives every admitted analysis;
`SamvrtiSat` has a concrete admitted recognition-loss witness.
`StableResultCertificate.sound` and `DissolutionCertificate.sound` derive the
two statuses from inspectable transformation data.

For an all-and-only finite inventory with local decision procedures,
`FiniteCoverage.classification_complete` gives one of the two statuses, and
`FiniteCoverage.samvrti_iff_not_paramartha` plus
`FiniteCoverage.paramartha_iff_not_samvrti` prove complementarity.  The
pot-water-color model is summarized by `finite_examples_are_classified`:
physical destruction dissolves the pot, mental separation dissolves the
water object, and the represented color-dharma remains recognized.
`ranked_steps_correspond_to_recognition_loss` connects the two dissolutions to
the generic finite ranked-rewrite carrier.

Coverage remains a substantive premise.  In
`empty_inventory_is_vacuously_paramartha`, no analysis is admitted, and
`coarse_analysis_misclassifies_the_pot` shows how admitting inspection but
omitting destruction changes the pot's classification.  Both statuses are
therefore relative to the supplied analytical framework; the module does not
identify them with Madhyamaka's two truths or an invariant substance.

## Acceptance scopes in Xuanzang's inference

[BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Xuanzang/Inference.lean](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Xuanzang/Inference.lean)
separates public `Vocabulary` from an `AcceptanceScope` containing a domain,
party commitments, and a semantic interpretation.  `QualifiedAnumana`
additionally requires subject reason, domain-scoped pervasion, and a positive
comparison locus distinct from the subject.  `QualifiedAnumana.sound` derives
the conclusion from the semantic reason and pervasion; lexical acceptance
alone is not treated as truth.

The admitted domain becomes the locus subtype used by `toAnumana` and
`toDharmakirtiModel`, so a scoped pervasion is not silently generalized to
rejected loci.  `toDialecticalCertificate`, `sound_via_pramana`, and
`debate_challenge_sound` then export the same obligations to the repository's
inference and debate interfaces.

For paired thesis and counter-thesis arguments,
`CounterReasonPair.SharedSemantics` explicitly requires the same domain and
the same positive interpretation.  `shared_semantics_consistent` derives the
needed consistency condition from those requirements, and
`shared_interpretation_precludes_both` rules out two locally sound opposite
polarities under that shared semantics.  Conversely,
`finite_scopes_are_distinct` and
`shifted_scopes_allow_both_local_inferences` give inhabited thesis and
counter-inference scopes whose domains and interpretations differ, allowing
both local conclusions without a common-semantics contradiction.  This is an
audit interface for reconstructions of Xuanzang and Wŏnhyo, not a selection
of one historical reading.

## Ranked grounds for Mīmāṃsā viniyoga

[BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaViniyoga.lean](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaViniyoga.lean) gives
`Ground` the six constructors for *śruti*, *liṅga*, *vākya*, *prakaraṇa*,
*sthāna*, and *samākhyā*.  `Ground.strict_priority_chain` verifies the chosen
numeric ordering.  `applicableInventory`, `topRank`, and `strongest` filter a
finite evidence list before `resolve` returns a decision exactly when the
highest applicable layer is nonempty and unanimous.

`resolve_some_sound` recovers applicable maximal evidence from every
successful result.  A `UniqueStrongestCertificate` supports the stronger
`unique_strongest_resolves` theorem and the permutation result
`unique_strongest_order_invariant`.  `toPremiseCertificate` preserves the
proof as provenance-bearing evidence, while `toPaniniPrioritySystem` and
`panini_adapter_agrees_with_resolver` realize the selected decision as one
terminating rewrite step.

The finite boundaries distinguish ranking from truth and applicability.
`equal_rank_conflict_is_unresolved` leaves opposed *śruti* items undecided;
`inapplicable_stronger_does_not_defeat_applicable_weaker` lets applicable
*liṅga* evidence prevail over an inapplicable *śruti* item; and
`hierarchy_alone_is_not_a_truth_decider` lets the resolver select a decision
rejected by an independent valuation.  The ranks are thus an executable
priority convention whose historical applicability and semantic warrant
remain separate inputs.

## Dependency summary

| Interface | Positive result | Finite boundary |
| --- | --- | --- |
| Autonomous inference | semantic certificate plus accepted obligations establishes and licenses the conclusion | semantic soundness does not force opponent commitment; refutation does not assert an independent thesis |
| Mohist kind extension | common kind, target reason, and relevance establish the target | parallel wording, one source, and a shared kind do not supply relevance |
| Countercondition audit | qualified pervasion plus qualified subject application restores soundness | unqualified pervasion, subject application, and the converse from a true thesis each fail separately |
| Mīmāṃsā epistemology | undefeated entitlement plus a truth bridge yields truth; an observed target plus residual exclusion closes a postulation frame | entitlement is not truth, residual alternatives remain possible, and imperceptible absence is not known by non-cognition |
| Tibetan definition | coextension, basis fit, and license yield grounded classification | coextension does not supply license or determine a unique feature requirement |
| Relation critique | an explicit bridge, identity premise, or successor law with an active seed yields its stated consequence | relation, connector, finite reification, and conceptual dependence do not supply those stronger premises |
| Vādanyāya procedure | role-specific faults and a total outcome checker determine the public result | a correct proof can lose, loss need not mean falsity, and a win need not mean truth |
| Constant co-apprehension | co-apprehension yields trace and time-profile equality; a coupled-pair witness, coupling-to-observation bridge, and identity bridge yield identity | complete co-occurrence under actual tagged equality, or only one accompaniment direction, does not yield identity |
| One-or-many analysis | explicit exhaustiveness and two horn rejections eliminate intrinsic existence; a constitution bridge derives the many rejection | intrinsic third cases and bridge-less many cases remain possible, while conventional existence survives |
| Yamaka extension pair | the finite classifier returns exactly one of four extension relations with failed-inclusion witnesses | one inclusion direction does not distinguish equality from proper inclusion |
| White Horse distinction | feature requests generate strict qualified-to-unqualified inclusion | inclusion identifies neither name, meaning, nor request; coextension still does not identify requests |
| Jayarāśi audits | base-certified descending grounding qualifies dependencies; sample coverage promotes agreement to pervasion | bare cycles do not ground a method, and finite positive samples do not establish a global rule |
| Pervasion determination | causal production plus scope coverage, enablement, defeater noncognition, and detection yields global pervasion | finite agreement and an unsuccessful finite defeater search leave an unseen countercase possible |
| Jaina necessary connection | subject reason plus subject `anyathānupapatti` yields its thesis; a global modal bridge exports pervasion | actual inclusion does not eliminate an accessible countercase, and sound two-member inference need not carry a distinct example |
| Substantial person | exhaustive dependence, change, propagation, and the conceptual-separation exclusion eliminate the stated extra candidate | bare dependence permits a stable extra candidate, and causal, memory, and responsibility continuity do not identify stages |
| Śrīharṣa audit | the finite checker is sound and complete for extensional, direct reciprocal-dependency, and profile-uniformity tests; true cognition plus tracking yields the modeled knowledge status | all four reported defects are inhabited, a three-edge dependency cycle lies outside the pairwise check, and an actually true affirmation can fail reliability |
| Fazang mereology | coverage, indispensability, disintegration, controlled whole withdrawal, and role grounding yield mutual whole-part dependence | an optional member and a contribution-differentiated collection supply neither strong removal dependence nor functional interpenetration |
| Staged signification inspired by Bhartṛhari | a complete finite search decides stage-relative signifiability, and a temporal reference discipline excludes self-reference | base-level unsignifiability coexists with later designation; Boolean and FDE negation have different fixed-point profiles |
| Navya-Nyāya absence | typed relation, locus, counterpositive, delimiter, perceptibility, exhaustive search, and non-cognition certify one scoped absence | non-cognition without perceptibility and search is insufficient; coextensive indices need not be identical |
| Mīmāṃsā sentence meaning | explicit lexical, connection, and composition bridges make two bounded sentence-meaning architectures agree on a sentence | the same lexical outputs do not determine order-sensitive semantic roles, and a shared connection map does not guarantee agreement |
| Udayana maker inference | subject effecthood and an explicit maker-pervasion bridge yield existence of an intelligent maker | a natural effect and an isolated artifact defeat unlicensed generalization; maker existence does not yield uniqueness, omniscience, or eternity |
| Reflexive awareness and memory | reflexive presentation plus a persistent trace and retrieval bridge support later episode attribution | complete object co-apprehension does not supply self-presentation, and one memory output does not identify its source episode |
| Pāṇinian priority rewriting | decreasing rank gives bounded termination, while explicit determinism of the step relation supports a unique normal form | two decreasing rules can terminate at distinct normal forms when a critical pair is unresolved |
| Wŏnhyo-inspired scoped gluing | coverage and agreement on overlap permit a global scoped valuation that preserves in-scope local conclusions | erasing contexts conflates locally opposed claims, and failed overlap agreement blocks gluing |
| Sāṃkhya latent causation | production-to-capacity plus capacity-grounding yields latent presence and exports a shared deductive certificate | selective production and capacity remain compatible with an empty latency relation |
| Jaina production-decay-duration | one carrier, ordered endpoints, old-mode loss, and new-mode acquisition yield the triadic transition | replacement has change without duration, while an unchanged carrier has duration without modal change |
| Five-part commentary | two local five-obligation certificates plus an explicit discourse edge compose into section coverage | distinct interpretations can both be certified, and certification need not follow an external truth valuation |
| Eleven non-apprehension forms | constructor-indexed observation, causal, inclusion, necessity, and incompatibility evidence compiles to one negation certificate | imperceptibility, blocked effects, alternative causes, and compatible rivals expose missing side conditions |
| Hard and White sensory access | selective sight/touch access yields distinct profiles and, under detection soundness, co-inherence in the supplied bearer | distinct access profiles do not require distinct substances, even when the quality requests remain distinct |
| Negandum calibration | absence of overreach and omission is extensionally equivalent to exact fit; separation retains conventions | universal and empty candidates fail in opposite directions, and FDE gluts block metalevel exclusion |
| Collected-topics four cells | complete finite enumeration makes every all-matches tag sound and every satisfied semantic relation present | named relations can overlap, and failure of coextension and exclusion does not establish all four cells |
| Perceptual semblance | nonconceptual nonerror plus occurrence, novelty, content, and a reliability bridge yields an operational pramāṇa | two moons is nonconceptual but erroneous and not a pramāṇa; nonerror alone does not entail truth |
| Auxiliary tarka | a counterfactual step plus independently supported consequence rejects the opposite; stability yields the target | either component alone can coexist with a false target, and an FDE glut does not supply metalevel exclusion |
| Abhidharma analysis | complete admitted analysis coverage classifies survival or dissolution and proves their complementarity | empty and coarse inventories can label an object ultimately existent only relative to undercoverage |
| Xuanzang acceptance scopes | subject reason, scoped pervasion, and a comparison witness yield a local conclusion; shared domain and interpretation exclude the opposite pair | shifted domains and interpretations allow both local inferences without a shared-semantics contradiction |
| Mīmāṃsā viniyoga | a unanimous maximal applicable layer resolves a decision, while unique strongest evidence gives order invariance and adapters | equal-rank conflict remains unresolved, inapplicable strength has no force, and priority does not decide truth |

## Verification and remaining evidence

All thirty-six modules are Lake roots and imports of the complete
`BuddhistComparativeLogic.lean` research tree. Thirty-four are in the 110-module release
aggregate. The other two, `BuddhistComparativeLogic.Comparative.Vedanta.Sriharsa` and
`BuddhistComparativeLogic.Buddhist.KoreanBuddhism.WonhyoHwajaeng`, remain in `BuddhistComparativeLogic/Experimental.lean` pending
exact source-to-formal mapping. The 2026-09-20 full verification checked the current 115 files
with warnings treated as errors and rejected proof admissions, project
axioms/constants, opaque or unsafe declarations, partial definitions, and
native-code proof shortcuts.  It also built the Isabelle2025-2 35-theory
session and PDF and passed the release, REUSE, and CFF checks.

Reproduce from the repository root:

```sh
sh tools/check-lean.sh
python3 tools/check_names.py
python3 tools/check_text.py
python3 tools/make_index.py --check
python3 tools/check_publication.py
```

The remaining work is philological and interpretive: choose edition-specific
passages; justify each relevance, repair, identity, exhaustiveness,
constitution, grounding, and coverage condition; distinguish competing
accounts of intrinsic epistemic validity and `abheda`; state the intensional
requirements used by a particular definition or naming practice; and show
which premises each historical passage actually supports.  The third group
also leaves external the choice of causal production and defeater-detection
laws, the accessibility relation used for Jaina necessity, the exhaustive
dependence and change-propagation claims in the person argument, the relevant
alternatives used for reliability, the intervention semantics for a whole,
and the vocabulary stages used for *avācya*.
The fourth group leaves external the intended absence relation and delimiter,
the word-to-sentence architecture, the effect-to-maker pervasion, the
reflexive-awareness and memory-trace bridges, the priority resolver and
determinism premise,
and the choice of local contexts and overlaps.  These inputs must be defended
for each historical passage before the checked conditional result can be used
as an interpretation.
The fifth group leaves external the capacity-to-latency principle, the
carrier analysis of duration, the chosen commentary framework and truth
valuation, each causal or incompatibility side condition of non-apprehension,
the route from sensory difference to an ontology of qualities, and the
intended extension of intrinsic existence.  The finite models make the
failure of each omitted step executable.
The sixth group leaves external the intended collected-topics relation
vocabulary and finite comparison domain, the historical adequacy of the
perception, error, and truth predicates and their operational reliability
bridge, the independently warranted proposition and stability principle used
by *tarka*, the admitted Abhidharma analyses and recognition relation, the
domains and interpretations assigned to Xuanzang's inference and its
counter-inference, and the applicability, ranking, and semantic warrant of
the six Mīmāṃsā grounds.  The executable classifiers and resolvers expose the
effect of changing each of these inputs.

Background used to delimit the reconstructions:

- [Madhyamaka, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/madhyamaka/)
- [Mohist Canons, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/archives/sum2022/entries/mohist-canons/)
- [Analytic Philosophy in Early Modern India, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/early-modern-india/)
- [Gaṅgeśa, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/archives/sum2026/entries/gangesa/)
- [Kumārila, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/archives/fall2023/entries/kumaarila/)
- [Epistemology in Classical Indian Philosophy, Stanford Encyclopedia of Philosophy](https://plato.sydney.edu.au/entries/epistemology-india/)
- [Tibetan Epistemology and Philosophy of Language, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/epistemology-language-tibetan/)
- [Dharmakīrti's *Sambandhaparīkṣā*, Austrian Academy of Sciences](https://www.oeaw.ac.at/fileadmin/Institute/IKGA/PDF/digitales/Steinkellner_2022_SPV_translation.pdf)
- [The Theory of *Nigrahasthāna* in Dharmakīrti's *Vādanyāya*](https://www.tandfonline.com/doi/abs/10.1080/01445340.2024.2339797)
- [Yogācāra, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/yogacara/)
- [The Theory of Two Truths in India, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/twotruths-india/)
- [On the Origin of Indian Logic from the Viewpoint of the Pāli Canon](https://link.springer.com/article/10.1007/s11787-019-00225-1)
- [School of Names, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/school-names/)
- [Jayarāśi, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/jayaraasi/)
- [Cubical Type Theoretic Navya-Nyāya](https://arxiv.org/abs/2605.12548)
- [Ratnakīrti's *Vyāptinirṇaya*, Austrian Academy of Sciences](https://www.oeaw.ac.at/en/ikga/research/buddhist-studies/concluded/ratnakirtis-vyaptinirnaya)
- [Vasubandhu, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/vasubandhu/)
- [Jaina Philosophy, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/jaina-philosophy/)
- [Śrīharṣa, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/sriharsa/)
- [The architecture of Fazang's six characteristics](https://doi.org/10.1080/09608788.2018.1563768)
- [The literal-nonliteral distinction in classical Indian philosophy](https://plato.stanford.edu/entries/literal-nonliteral-india/)
- [Language and Testimony in Classical Indian Philosophy](https://plato.stanford.edu/entries/language-india/)
- [Dharmakīrti, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/dharmakiirti/)
- [Analytic Philosophy in Early Modern India](https://plato.stanford.edu/entries/early-modern-india/)
- [The *Nyāyakusumāñjali* and its first two clusters](https://www.mdpi.com/2077-1444/16/11/1336)
- [Pāṇini and the architecture of Sanskrit grammar](https://web.stanford.edu/~kiparsky/Papers/panini_hist_of_phon_handbook.pdf)
- [Korean Buddhism and Wŏnhyo's *hwajaeng*](https://plato.stanford.edu/archives/fall2024/entries/korean-buddhism/)
- [Naturalism in Classical Indian Philosophy: Sāṃkhya causation](https://plato.stanford.edu/archives/fall2022/entries/naturalism-india/)
- [Jaina Philosophy: production, destruction, and permanence](https://plato.stanford.edu/entries/jaina-philosophy/)
- [Vasubandhu's *Vyākhyāyukti* and scriptural interpretation](https://link.springer.com/article/10.1007/s10781-023-09542-8)
- [Dharmakīrti's *Nyāyabindu*, II.31–42](https://gretil.sub.uni-goettingen.de/gretil/1_sanskr/6_sastra/3_phil/buddh/dhknyayu.htm)
- [Zhihua Yao, “Non-Cognition and the Third Pramāṇa”](https://philarchive.org/rec/YAONAT)
- [The received *Hard and White* dialogue](https://ctext.org/gongsunlongzi/jian-bai-lun/ens)
- [Tsongkhapa and the object of negation](https://plato.stanford.edu/archives/spr2014/entries/tsongkhapa/)
- [Debate in the Tibetan Tradition](https://academic.oup.com/edited-volume/62249/chapter-abstract/551439251)
- [Dignāga's *Pramāṇasamuccaya*, EAST bibliographic record](https://east.ikga.oeaw.ac.at/data/1/12/)
- [Gautama's *Nyāyasūtra*, GRETIL](https://gretil.sub.uni-goettingen.de/gretil/1_sanskr/6_sastra/3_phil/nyaya/gaunys_u.htm)
- [Vasubandhu's *Abhidharmakośabhāṣya*, GRETIL](https://gretil.sub.uni-goettingen.de/gretil/corpustei/transformations/html/sa_vasubandhu-abhidharmakozabhASya.htm)
- [Materials for the Study of Xuanzang's Inference of Consciousness-only](https://www.austriaca.at/0xc1aa5572_0x003aa075.pdf)
- [Jaimini's *Mīmāṃsāsūtra*, GRETIL](https://gretil.sub.uni-goettingen.de/gretil/1_sanskr/6_sastra/3_phil/mimamsa/jaimsutu.htm)
