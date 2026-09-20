# Lean: completed interfaces and remaining evidence

Role: `supplement`

Lifecycle: `active`

Lean/static audit: 2026-09-20

Isabelle/PDF receipt: 2026-09-20 (Isabelle2025-2, 35-theory session; full
`sh verify.sh` run)

## Scope

The complete Lean tree contains 115 files: 112 subject and infrastructure
modules plus three aggregates.  The 112 substantive modules comprise 34
modules representing all 35 Isabelle theory units and 78 Lean-only
extensions.  `BuddhistComparativeLogic/Release.lean` imports the 110-module author-reviewed set;
`BuddhistComparativeLogic/Experimental.lean` imports two modules retained for exact
source-to-formal mapping review; and
`BuddhistComparativeLogic.lean` imports both sets. The Isabelle sources form a
35-theory session; the current Isabelle/PDF receipt is dated 2026-09-20.

The 78 Lean-only extensions are organized by function. Eight modules cover
assumption auditing, path dynamics, attachment-gated iteration, explicit
pervasion, dependent origination, fourfold reductio obligations, inference
scope, and cessation. Sixteen modules cover logic, argument composition, and
text alignment. Five cover premise provenance, matrix transport, directed
causal continuity, and selection. Four synthesize pramāṇa and Yogācāra, and one
connects catuṣkoṭi classification with the K3 and FDE matrices. Four modules
reconstruct selected proof architectures from the *Pramāṇasamuccaya*,
*Pramāṇavārttika*, the momentariness-proof tradition, and the
*Tattvasaṃgraha*; four cover Nyāya public inference, the
*Ālambanaparīkṣā* dilemma, Tibetan consequence debate, and other-mind
inference. The comparative modules cover autonomous and consequence reasoning,
kind extension, pervasion, epistemology, definition theory, relations, debate,
co-observation, one-or-many arguments, extension questions, definition audits,
mereology, signification, absence, sentence meaning, maker inference,
self-awareness, grammar, reconciliation, causation, change, commentary,
non-apprehension, sensory access, negandum calibration, predicate comparison,
perception, tarka, two-truths analysis, acceptance, and application priority.
These are argument-interface formalizations rather than verse-by-verse textual
encodings.

These are conditional mathematical results.  Lean checks every consequence,
countermodel, decision procedure, and proof transformation from the stated
hypotheses.  It cannot establish that an interpretation is historically
preferred, that a Sanskrit or Tibetan token span warrants a philosophical
construal, or that the psychological and causal premises are true.

## Current results

| Problem | Lean result | Boundary made explicit |
| --- | --- | --- |
| Kinds of dependence | `empty_of_mode_dependency` proves emptiness from causal, mereological, or conceptual dependence under the corresponding exclusion law. | Independence by itself does not decide own-being; each bridge is a premise. |
| Universal dependence | `all_empty_of_coverage` composes a dependency-mode coverage theorem. `incomplete_coverage_allows_own` gives the missing-case countermodel. | Universal emptiness requires coverage of every subject as well as each exclusion bridge. |
| Fourfold causation | `exact_origin_exhaustive` and `exact_origin_unique` make the four origins exhaustive and exclusive for event tokens, kinds, and times. `no_intrinsic_by_four_cases` eliminates intrinsic production while `nonarising_preserves_ordinary_production` keeps ordinary production nonempty. | The classification and four incompatibility laws remain explicit premises, each with omission tests. |
| Belief revision and release | `rational_revision_contracts` and `eventual_release_from_revision` derive contraction and bounded release from observation, assimilation, and support discipline. Countermodels separate observation, assimilation, discipline, and relapse. | Evidence arrival alone does not force belief change or permanent release. |
| Jizang's gate and remedy | `antidote_stops_iff_evidence_sufficient` interprets the gate cognitively. `attachment_account_selects_tstep_up_to_derivability` derives the response from a least common consequence of the attachment focus plus ultimate reversal; `selected_remedy_is_tstep` chooses its canonical syntax tree. | The attachment focus, evidence scores, and response adequacy principles still need textual or cognitive justification. |
| End-to-end argument | `dependence_to_bounded_release` and `fourfold_to_bounded_release` compose metaphysical recognition with revision and bounded release. `insight_without_revision_does_not_release` and `release_does_not_prove_universal_emptiness` block both invalid shortcuts. | The pipeline proves a conditional implication, not a historical claim or an empirical law. |
| FDE and FDE5 proof theory | `deriv_sound_complete` proves the lattice/De Morgan natural-deduction system sound and complete via a nonempty DNF. `tableau_sound_complete` does the same for signed analytic tableaux, while `tableau_iff_deriv` connects their proof objects. The containment-enriched FDE5 counterparts are `deriv5_sound_complete` and `tableau5_sound_complete`. | These are single-premise consequence calculi over the repository's propositional language. |
| Universal designation | `pos_up_k3_is_k3` identifies positive universal K3 consequence; `pos_up_lp_is_fde` identifies the LP case with FDE. The corresponding unrestricted results are `priest_open_question_k3` and `priest_open_question_lp`. | Identifying further named matrices still requires fixing their value set, operations, and designation convention. |
| Absorbing ineffability | `pos_upentails_iff` and `upentails_iff` characterize universal designation after adjoining one undesignated absorbing value to any base `MVLogic`; concrete classical, K3, LP, and FDE corollaries are included. | The construction is exact for this extension operation, not every philosophical use of “ineffable”. |
| Sevenfold predication | `route_realizes_mode` supplies a dynamic trace for every naya and `route_is_length_minimal` proves the trace-length lower bounds. `Supports` is monotone under appended observations; `ExactlyLicenses` records exact profiles and may cease to hold after a new respect is observed. | The transition trace does not identify a historically privileged order of respects. |
| Momentariness | `causal_nonuniformity` proves only change of causal power. `momentary_of_rooted_causalChains` reaches momentariness from efficacy, unique effect time, local two-way effect transport, and rooted causal chains. | `causal_nonuniformity_is_not_yet_momentariness` and the continuity countermodels isolate the extra bridge. |
| Componential apoha | `fixed_features_determine_unique_pair` proves conditional uniqueness. `stable_requirement_stops_regress` gives a fixed-point stopping condition for features of features; `self_excluding_regress_never_stops` gives an oscillating nontermination model. | Choosing the required features and a stable higher-level grounding remains substantive. |
| Motion over intervals | `interval_motion_traverses` supplies the positive interval account and `point_analysis_is_compatible_with_interval_motion` proves compatibility with the earlier point partition. `same_present_different_motion` separates position from motion. | The account assumes the interval and endpoint order rather than deriving a physical theory of time. |
| Twenty Verses model comparison | `adequacy_is_observation_invariant`, `every_appearance_account_has_token_factorization`, and `object_index_cardinality_is_observationally_underdetermined` compare an appearance account with neutral object-indexed factorizations. | The generic token factorization asserts neither mind-independence nor external-object existence; observational equivalence does not decide the carrier cardinality. |
| Recension alignment | `sanskrit_canonical_key_alignment_valid`, `tibetan_canonical_key_alignment_valid`, and `longer_frame_alignment_valid` check canonical structural maps. Bounded GRETIL/Silk token spans discharge all four central lexical obligations. `sanskrit_diplomatic_not_order_preserving` and its Tibetan counterpart prove that both source texts print the HS07 counterpart before HS06, reversing the Chinese clause-key order. | `lexical_validation_is_construal_neutral` blocks the token checks from selecting a philosophical reading; further editions and clauses require further evidence. |
| Supporting argument scope | `middle_way_on_covered_domain`, `comparison_completes_three_marks`, and `fourfold_middle_way` connect scoped dependence, inference, and ordinary conditioned occurrence. FDE countermodels separate formula negation from metalevel rejection. | A local edge does not establish universal dependence, and the three marks need a comparison witness plus pervasion for deductive use. |
| Premise provenance | `dependence_certificate_sound` and `fourfold_certificate_sound` consume individually referenced, proof-bearing premises and derive bounded release. Internal examples use compiler-resolved declaration names; `citation_metadata_can_accompany_a_false_claim` and `certified_false_is_uninhabited` distinguish a citation record from a proof. | External locators are unchecked annotations and source metadata does not establish its proposition; each `Certified.fact` remains an explicit input. `nonoccurring_chain_event_has_no_release_certificate` shows that the fourfold certificate also requires occurrence. |
| Matrix transport | `MatrixIso.entails_iff`, `MatrixIso.pos_upentails_iff`, and `MatrixIso.upentails_iff` preserve all three consequence notions across an explicit matrix isomorphism. `fdeBitIso` classifies the truth/falsity-bit FDE presentation. | A proposed named matrix still requires an actual isomorphism or a separate analysis; a verbal similarity is insufficient. |
| Directed momentariness | `momentary_of_rooted_directedChains` uses only backward transport of the observed effect to its root. `directed_transport_does_not_imply_forward_transport` proves that this is strictly weaker than two-way continuity. | Rootedness and unique effect time remain premises. The declaration reuses `Momentariness.Theory`, which also contains a two-times witness unused by this proof; no physical account of time is derived. |
| Apoha selection | `selected_grounding_unique` proves at-most-one selected grounded pair under antisymmetry, while `selected_grounding_exists` constructs one from a supplied optimal requirement. `admissibility_without_antisymmetry_is_underdetermined` gives a tied two-requirement countermodel. | Optimal existence, the concrete candidate filter, and the comparison rule still require independent justification. |
| Pramāṇa synthesis | `deductive_sound` derives the subject thesis from subject possession plus pervasion. `dialectical_trairupya` and `dialectical_wheel_valid` add the positive comparison example needed for public classification. | `marks_and_valid_wheel_do_not_entail_subject`, `pervasion_without_subject_reason_is_insufficient`, and `sound_subject_inference_need_not_have_valid_wheel` separate three invalid shortcuts. |
| Yogācāra synthesis | `Trisvabhava`, `SeedTrajectory`, and `TransformationAt` connect dependent occurrence, projected duality, causal lineage, and transformation through explicit bridges. | Dependent occurrence alone is not perfected nature; continuity entails neither an unchanging seed nor transformation. |
| Eight consciousnesses | `eight_roles_exact` checks five sensory roles, mental cognition, afflicted mind, and store consciousness. `nonstore_presentation_has_distinct_store_support` uses an explicit all-non-store support premise. | Functional roles are not separate substances, and taxonomy or coactivity alone entails neither store support, permanence, nor projected duality. `NonStore` is a structural complement and does not classify afflicted mind as manifest. |
| Pramāṇa–Yogācāra scope | `conclusion_of_license` exposes observational pervasion. `three_marks_do_not_establish_external_objects` and the classifier impossibility theorems use observation-equivalent finite accounts. | Adequacy does not decide external-object existence or cardinality; restricting the domain recovers only the restriction already assumed. |
| Catuṣkoṭi, K3, and FDE | `k3_entails_iff_fde_no_gluts` identifies K3 consequence with FDE consequence over valuations omitting `B`; `fde_entails_implies_k3_entails` gives the unrestricted direction and `explosion_strictly_separates_k3_from_fde` refutes its converse. `k3_corner_image_exact` computes the three-corner K3 image inside the injective FDE classifier. | These are results about the fixed matrices and designation sets. `K3` the logic and `Koti.K3` the both-designated corner are distinct objects; historical application remains interpretive. |
| Four pramāṇa treatise architectures | The modules type the separation between perception and concepts, subject-level warrants and public marked arguments, causal efficacy and momentariness, and individual debate certificates and their composition. | The neutral warrant/presentation types are not exact definitions of Dignāga's historical private/public categories. Tattvasaṃgraha topic labels are unchecked annotations. Textual attribution, the intended pervasion and causal bridge, and completeness with respect to every chapter or verse remain external evidence claims. |
| Inference and debate interfaces | `complete_presentation_sound` checks the five-member Nyāya presentation; `two_horn_exclusion` eliminates both modeled intentional-object candidates; `finite_termination_bound` bounds fresh-acceptance debate; and `behaviour_does_not_exactly_classify_other_minds` gives observational underdetermination. | One illustration does not create pervasion, the object dilemma is local to its candidate proxy, debate commitment is not truth, and identical behaviour does not decide hidden volition. |
| Public inference, concepts, and relations | Six modules certify opponent-relative public inference, relevance-sensitive kind extension, countercondition-aware pervasion, defeater-sensitive entitlement, constrained definition, and conditional relation critique. | Finite models separate semantic truth from commitment, syntax from semantic relevance, initial entitlement from truth, coextension from definition, and primitive relatedness from a reified connector. |
| Debate, co-observation, and extension | Six modules certify procedural debate results, observational nonseparation, conditional one-or-many elimination, bilateral extension classification, feature-grounded inclusion, and grounded finite extrapolation. | Finite models separate victory from truth, co-observation from identity, conventional existence from intrinsic nature, one-way inclusion from equality, extension from meaning and request, and sampled agreement from global pervasion. |
| Pervasion, person, definition, and language | Six modules certify causal or modal routes to pervasion, a bounded substantial-person exclusion, definition diagnostics, conditional whole-part dependence, and vocabulary-relative signification. | Finite models separate sampled regularity from a global rule, continuity from identity, truth from reliability, collections from strong wholes, and local from absolute unsignifiability. |
| Absence, composition, inference, and reconciliation | Six modules certify relational absence, two sentence-composition routes, a conditional maker inference, trace-based memory attribution, rank-decreasing priority rewriting, and compatible gluing of local theories. | Finite models separate bare non-cognition from qualified absence, examples from universal maker rules, lexical values from role-sensitive sentences, co-apprehension from reflexive presentation and identity, termination from uniqueness of normal form, and scoped local claims from an erased union of opposed formulas. |
| Causation, change, interpretation, and negation | Six modules certify capacity-grounded latent presence, a triadic change transition, five-part commentary coverage, eleven typed negation routes, sensory-profile distinction, and exact negandum fit. | Finite models separate production from latency, replacement from duration, checklist completion from uniqueness and truth, non-cognition from sound negation, sensory access from distinct bearers, and formula-level emptiness from metalevel exclusion. |
| Predicate, perception, analysis, and priority | Six modules certify witness-cell predicate comparisons, a strict perception-candidate refinement, tarka-assisted settlement, analysis-indexed classification, common-ground inference, and applicable-ground priority. | Finite models separate coarse predicate relations from four-cell coverage, nonconceptuality from non-error and truth, conditional supposition from independent evidence, empty analysis families from robust survival, local acceptance from shared semantics, and rank from applicability or tie resolution. |

## Logic, argument, and text-alignment modules

- [BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceModes.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceModes.lean)
- [BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceCoverage.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/DependenceCoverage.lean)
- [BuddhistComparativeLogic/Buddhist/Madhyamaka/FourfoldCausation.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/FourfoldCausation.lean)
- [BuddhistComparativeLogic/Buddhist/HeartSutra/BeliefRevision.lean](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/BeliefRevision.lean)
- [BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/CognitiveAntidote.lean](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/CognitiveAntidote.lean)
- [BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/AntidoteSelection.lean](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Jizang/AntidoteSelection.lean)
- [BuddhistComparativeLogic/Buddhist/HeartSutra/ArgumentPipeline.lean](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/ArgumentPipeline.lean)
- [BuddhistComparativeLogic/Core/FDECalculus.lean](../lean/BuddhistComparativeLogic/Core/FDECalculus.lean)
- [BuddhistComparativeLogic/Core/UniversalDesignationMore.lean](../lean/BuddhistComparativeLogic/Core/UniversalDesignationMore.lean)
- [BuddhistComparativeLogic/Core/Ineffable.lean](../lean/BuddhistComparativeLogic/Core/Ineffable.lean)
- [BuddhistComparativeLogic/Comparative/Jaina/NayaDynamics.lean](../lean/BuddhistComparativeLogic/Comparative/Jaina/NayaDynamics.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Momentariness.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Momentariness.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/ApohaFeatures.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/ApohaFeatures.lean)
- [BuddhistComparativeLogic/Buddhist/Madhyamaka/GamanaIntervals.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/GamanaIntervals.lean)
- [BuddhistComparativeLogic/Buddhist/Yogacara/VimsatikaModels.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/VimsatikaModels.lean)
- [BuddhistComparativeLogic/Buddhist/HeartSutra/RecensionAlignment.lean](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/RecensionAlignment.lean)

## Premise and selection modules

- [BuddhistComparativeLogic/Buddhist/Madhyamaka/SupportingArguments.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/SupportingArguments.lean)
- [BuddhistComparativeLogic/Buddhist/HeartSutra/PremiseCertificates.lean](../lean/BuddhistComparativeLogic/Buddhist/HeartSutra/PremiseCertificates.lean)
- [BuddhistComparativeLogic/Core/MatrixTransport.lean](../lean/BuddhistComparativeLogic/Core/MatrixTransport.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/DirectedMomentariness.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/DirectedMomentariness.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/ApohaSelection.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/ApohaSelection.lean)

## Pramāṇa and Yogācāra synthesis modules

- [BuddhistComparativeLogic/Buddhist/Pramana/PramanaSynthesis.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/PramanaSynthesis.lean)
- [BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraSynthesis.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraSynthesis.lean)
- [BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraConsciousness.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraConsciousness.lean)
- [BuddhistComparativeLogic/Buddhist/Yogacara/PramanaYogacara.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/PramanaYogacara.lean)

The combined theorem and countermodel audit is in
[PRAMANA_YOGACARA.md](PRAMANA_YOGACARA.md).

## Catuṣkoṭi, K3, and FDE synthesis module

- [BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean](../lean/BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean)

The embedding, consequence, four-corner, and set-quantifier audit is in
[CATUSKOTI_K3_FDE.md](CATUSKOTI_K3_FDE.md).

## Pramāṇa treatise modules

- [BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean)

Their theorem, countermodel, and historical-scope audit is in
[PRAMANA_TREATISES.md](PRAMANA_TREATISES.md).

## Inference and debate modules

- [BuddhistComparativeLogic/Comparative/Nyaya/Nyaya.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Nyaya.lean)
- [BuddhistComparativeLogic/Buddhist/Yogacara/Alambanapariksa.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Alambanapariksa.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Debate.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Debate.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/OtherMinds.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/OtherMinds.lean)

Their proof obligations, concrete countermodels, and historical-scope limits are
recorded in [INFERENCE_DEBATE.md](INFERENCE_DEBATE.md).

## Comparative logic modules

- [BuddhistComparativeLogic/Buddhist/Pramana/SvatantraPrasanga.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/SvatantraPrasanga.lean)
- [BuddhistComparativeLogic/Comparative/ChineseThought/MohistCanons.lean](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/MohistCanons.lean)
- [BuddhistComparativeLogic/Comparative/Nyaya/Tattvacintamani.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Tattvacintamani.lean)
- [BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaEpistemology.lean](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaEpistemology.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Definitions.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Definitions.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Sambandhapariksa.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Sambandhapariksa.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Vadanyaya.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Vadanyaya.lean)
- [BuddhistComparativeLogic/Buddhist/Yogacara/Sahopalambha.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Sahopalambha.lean)
- [BuddhistComparativeLogic/Buddhist/Madhyamaka/Ekanekaviyoga.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/Ekanekaviyoga.lean)
- [BuddhistComparativeLogic/Buddhist/Abhidharma/Yamaka.lean](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Yamaka.lean)
- [BuddhistComparativeLogic/Comparative/ChineseThought/WhiteHorse.lean](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/WhiteHorse.lean)
- [BuddhistComparativeLogic/Comparative/Skepticism/Jayarasi.lean](../lean/BuddhistComparativeLogic/Comparative/Skepticism/Jayarasi.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Vyaptinirnaya.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Vyaptinirnaya.lean)
- [BuddhistComparativeLogic/Buddhist/Abhidharma/Pudgala.lean](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Pudgala.lean)
- [BuddhistComparativeLogic/Comparative/Jaina/JainaInference.lean](../lean/BuddhistComparativeLogic/Comparative/Jaina/JainaInference.lean)
- [BuddhistComparativeLogic/Comparative/Vedanta/Sriharsa.lean](../lean/BuddhistComparativeLogic/Comparative/Vedanta/Sriharsa.lean)
- [BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Fazang/Mereology.lean](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Fazang/Mereology.lean)
- [BuddhistComparativeLogic/Comparative/Grammar/Bhartrhari.lean](../lean/BuddhistComparativeLogic/Comparative/Grammar/Bhartrhari.lean)
- [BuddhistComparativeLogic/Comparative/Nyaya/NavyaNyayaAbsence.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/NavyaNyayaAbsence.lean)
- [BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaSentenceMeaning.lean](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaSentenceMeaning.lean)
- [BuddhistComparativeLogic/Comparative/Nyaya/Nyayakusumanjali.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Nyayakusumanjali.lean)
- [BuddhistComparativeLogic/Buddhist/Yogacara/Svasamvedana.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Svasamvedana.lean)
- [BuddhistComparativeLogic/Comparative/Grammar/PaniniDerivation.lean](../lean/BuddhistComparativeLogic/Comparative/Grammar/PaniniDerivation.lean)
- [BuddhistComparativeLogic/Buddhist/KoreanBuddhism/WonhyoHwajaeng.lean](../lean/BuddhistComparativeLogic/Buddhist/KoreanBuddhism/WonhyoHwajaeng.lean)
- [BuddhistComparativeLogic/Comparative/Samkhya/Satkaryavada.lean](../lean/BuddhistComparativeLogic/Comparative/Samkhya/Satkaryavada.lean)
- [BuddhistComparativeLogic/Comparative/Jaina/JainaChange.lean](../lean/BuddhistComparativeLogic/Comparative/Jaina/JainaChange.lean)
- [BuddhistComparativeLogic/Buddhist/Hermeneutics/Vyakhyayukti.lean](../lean/BuddhistComparativeLogic/Buddhist/Hermeneutics/Vyakhyayukti.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/AnupalabdhiKinds.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/AnupalabdhiKinds.lean)
- [BuddhistComparativeLogic/Comparative/ChineseThought/HardWhite.lean](../lean/BuddhistComparativeLogic/Comparative/ChineseThought/HardWhite.lean)
- [BuddhistComparativeLogic/Buddhist/Madhyamaka/NegandumCalibration.lean](../lean/BuddhistComparativeLogic/Buddhist/Madhyamaka/NegandumCalibration.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/BsdusGrwa.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/BsdusGrwa.lean)
- [BuddhistComparativeLogic/Buddhist/Pramana/Pratyaksabhasa.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pratyaksabhasa.lean)
- [BuddhistComparativeLogic/Comparative/Nyaya/Tarka.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Tarka.lean)
- [BuddhistComparativeLogic/Buddhist/Abhidharma/Analysis.lean](../lean/BuddhistComparativeLogic/Buddhist/Abhidharma/Analysis.lean)
- [BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Xuanzang/Inference.lean](../lean/BuddhistComparativeLogic/Buddhist/ChineseBuddhism/Xuanzang/Inference.lean)
- [BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaViniyoga.lean](../lean/BuddhistComparativeLogic/Comparative/Mimamsa/MimamsaViniyoga.lean)

Their theorem, countermodel, and historical-scope audit is in
[COMPARATIVE_LOGIC.md](COMPARATIVE_LOGIC.md).

## Assumption audit

The strongest conclusions are intentionally split at the points where a
philosophical premise enters:

- Dependence is descriptive until a mode-specific exclusion law connects it
  to absence of own-being.
- Fourfold non-arising concerns intrinsic origin.  Ordinary conditioned event
  production remains possible in a model satisfying all four exclusions.
- Recognition changes a belief only through an assimilation rule, and a
  finite release bound additionally needs support discipline and persistent
  revision.
- The antidote operation is selected up to derivability from an attachment
  focus and proof-theoretic adequacy.  Exact syntax uses a canonical-form
  convention.
- Causal nonuniformity is weaker than numerical momentariness.  The last step
  requires a punctuality bridge, here derived from rooted causal chains.
- Feature grounding resolves extension choice only relative to a requirement;
  higher-level feature grounding may stabilize or regress forever.
- Canonical-key alignment and diplomatic source order are separate data.  The
  checked central Sanskrit and Tibetan spans discharge lexical obligations,
  but the validation is invariant under every candidate construal.
- Citation metadata and proof payload are separate types.  Only the latter can
  enter a soundness theorem.
- Matrix classification is transported only through a fully specified
  operation- and designation-preserving bijection.
- Backward causal transport is sufficient only together with rootedness and
  unique effect time; forward transport is not assumed.
- Apoha uniqueness is relative to an admitted antisymmetric selection rule;
  admissibility by itself leaves concrete pairs underdetermined.
- Pramāṇa subject soundness uses possession plus pervasion; a comparison
  example is required only for the dialectical three-mark and wheel layer.
- Yogācāra three-nature, seed, store-support, projection, and transformation
  connections remain individually named bridges rather than definitions of
  one another.
- Observation-only evidence cannot distinguish the supplied appearance-only,
  one-object, and two-object accounts.
- K3 is compared with FDE through an explicit operation- and
  designation-preserving embedding whose range excludes `B`; no historical
  interpretation of catuṣkoṭi is built into that algebraic result.
- The four treatise modules formalize selected argument structures.  Their
  names do not certify a complete critical edition, a unique interpretation,
  or coverage of every chapter and verse.
- The Nyāya member roles, intentional-object conditions, Tibetan reply rules,
  and behaviour-to-volition relation are explicit proxies.  Their soundness
  results do not establish a preferred historical reconstruction.
- The comparative interfaces keep an opponent's commitments, Mohist semantic
  relevance, an `upādhi` repair rule, undefeated entitlement's truth bridge,
  a definition license, and a relation-reification bridge as separate inputs.
  None is generated merely by semantic truth, parallel syntax, diagnosis,
  coextension, or the existence of a binary relation.
- The debate, co-observation, extension, and extrapolation interfaces require explicit bridges from
  co-observation to identity, from one-or-many analysis to absence of
  intrinsic nature, from local samples to global pervasion, and from local
  adequacy to noncircular support.  Its debate result and term-extension
  classifier do not identify procedural status with truth value.
- The pervasion, person, definition, mereology, and language interfaces require explicit causal or modal coverage, dependence and
  change propagation, reliability, indispensability, and vocabulary-level
  bridges.  Its examples show that observations, continuity, true belief,
  membership, and success at a later vocabulary stage do not silently provide
  them.
- The absence, composition, inference, awareness, grammar, and reconciliation interfaces require typed absence delimiters, sentence-composition
  bridges, maker pervasion, reflexive trace persistence, a deterministic
  rewrite relation, and agreement on shared local content.  The finite
  examples do not promote detection failure, a single artifact, lexical
  agreement, co-observation, termination, or context erasure into those
  stronger claims.
- The causation, change, interpretation, negation, and sensory interfaces require capacity grounding, a persisting carrier,
  passage-level commentary obligations, constructor-specific negative-reason
  evidence, detection soundness, and an intended intrinsic predicate.  Its
  finite models keep selective production, temporal replacement, checklist
  completion, non-cognition, sensory distinction, and broad or narrow
  negation predicates from supplying stronger conclusions by themselves.
- The predicate, perception, analysis, acceptance, and priority interfaces require complete witness inventories, an explicit
  error-freedom condition, independent evidence for a tarka target, a
  nondegenerate analysis family, shared acceptance scope, and an applicable
  uniquely strongest ground.  Its finite models prevent missing cells,
  nonconceptual error, bare counterfactuals, vacuous invariance, split common
  ground, or tied priorities from being read as settled conclusions.

## Verification

Lean 4.32.0 verification covers the current 115-file tree on 2026-09-20.
The full 2026-09-20 run treated warnings as errors
and verified Lake roots and the
release, experimental, and complete aggregate import closures and rejected
proof admissions, project axioms/constants, opaque or unsafe declarations,
partial definitions, and native-code proof shortcuts.  The name, text, index,
and whitespace guards also passed.  The same run built the Isabelle2025-2
35-theory session and PDF and passed release, REUSE, and CFF validation.

Run from the repository root:

```sh
sh tools/check-lean.sh
python3 tools/check_names.py
python3 tools/check_text.py
python3 tools/make_index.py --check
python3 tools/check_publication.py
```

## Remaining inputs

1. Supply the proof fields of the premise certificates by defending the
   dependency exclusions, fourfold incompatibility laws, directed rootedness,
   belief-update laws, and attachment-response account from independently
   argued interpretations.
2. Maintain and extend edition-specific Sanskrit and Tibetan token evidence,
   and explain what philosophical reading, if any, that evidence warrants.
3. For each further explicitly specified many-valued base, construct a
   `MatrixIso` to a classified base or analyze it separately when no such
   isomorphism exists.
4. Justify the selected pramāṇa pervasions and the Yogācāra three-nature,
   seed-development, store-support, projection, and transformation bridges
   from the intended textual or practice context.
5. Justify any application of K3, FDE, existential designation, or universal
   designation to a particular fourfold passage; the matrix comparison itself
   does not select that interpretation.
6. Attach edition-specific passages to each treatise interface and justify the
   intended pervasion, causal-efficacy bridge, momentariness transport, and
   cross-topic composition premises.
7. Attach sources to the four inference/debate proxies and justify the chosen
   Nyāya member semantics, intentional-object horns, Tibetan reply discipline,
   and epistemic strength of the other-mind license.

These are evidence and premise-selection tasks. The corresponding executable
Lean definitions, theorems, and countermodels are listed above.
