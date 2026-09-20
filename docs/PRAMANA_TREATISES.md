# Four pramāṇa treatise architectures in Lean

Role: `supplement`

Lifecycle: `active`

Verified: 2026-09-19

## Scope

This batch adds four Lean modules for selected argument architectures associated
with the *Pramāṇasamuccaya* (集量論), *Pramāṇavārttika* (量評釈), the
Buddhist momentariness-proof tradition represented by works called
*Kṣaṇabhaṅgasiddhi* (刹那滅論), and the *Tattvasaṃgraha* (真実綱要).

The modules are proof-obligation reconstructions.  They do not encode a
critical Sanskrit or Tibetan text, align verses, settle disputed readings, or
claim completeness for a whole work.  A name in a module title identifies the
argument family being audited.  Every passage-level attribution and every
substantive pervasion, causal, semantic, or scope premise still requires
independent historical support.

## 集量論：二量と二つの推論場面

[BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanasamuccaya.lean)
keeps four layers distinct.

`PerceptualEvidence` packages a presented datum and an explicit
nonconceptuality premise.  `SelfAwarenessModel` adds reflexive awareness as a
separate law; `self_awareness_of_explicit_model` consumes that law rather than
deriving self-awareness from presentation alone.  The tagged `Evidence` type
then prevents perceptual evidence and inferential certificates from being
silently identified.

`SubjectWarrant` contains subject possession and pervasion.
`subject_warrant_is_sound` derives the subject thesis.  A
`CertifiedPublicArgument` adds a positive comparison example, so
`certified_public_argument_is_sound_and_wheel_valid` yields both the thesis
and the valid wheel classification.  The weaker `PublicPresentation` records
the three displayed marks without adding global pervasion.  These are neutral
project interfaces; they are not definitions of Dignāga's historical
self-inference and other-directed verbal-proof categories.

`GroundedConcept` selects an extension from an explicitly supplied exemplar
and equivalence-like relation.  `grounded_extension_and_exclusion` returns
both that grounding and the complementary pair.  The relation has no causal
meaning by definition, and the complement result uses classical extensional
negation.  This optional selector is kept distinct from historical attribution.
`negative_comparison_is_exclusion` connects the comparison classes to the
existing apoha interface without extending the result to the disputed subject.

Three finite boundaries prevent stronger readings:

- `raw_observation_does_not_entail_conceptual_classification` gives two
  objects with the same perceptual datum but different conceptual classes;
- `three_marks_do_not_entail_subject_without_pervasion` reuses the finite
  three-mark model whose subject thesis is false; and
- `public_form_and_subject_warrant_are_not_identical` supplies one model in
  each direction, separating a marked public form from a subject deductive
  warrant.

## 量評釈：認識の信頼性と遍充

[BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Pramanavarttika.lean)
uses an operational surrogate for pramāṇa: an occurring, novel,
content-bearing, reliable cognition.  Reliability means that every object
presented by that cognition participates in a successful realization.  An
efficacious object is witnessed by a cognition that occurs, presents it, and
realizes it.  This is a formal interface rather than a proposed translation of
every use of *pramāṇa* in the text.

`pramana_tracks_causal_efficacy` derives efficacy only for an object that the
cognition actually presents, while `pramana_has_efficacious_content` proves
that the nonempty-content field supplies at least one such object.  The finite results
`pramana_does_not_certify_every_object`,
`reliability_and_efficacy_do_not_imply_pramana`, and
`presentation_alone_is_not_reliability` show respectively that the result is
local, novelty is independent, and mere presentation does not guarantee
success.

`IntrinsicArgument` and `ExtrinsicArgument` distinguish an inclusion-based
reason from an effect-based reason with a supplied causal law.
`intrinsic_argument_sound` and `extrinsic_argument_sound` route both through
the common possession-plus-pervasion certificate.  `PublicProof` adds a
comparison example; `comparison_marks_without_pervasion_do_not_settle_subject`
and `subject_inference_does_not_supply_public_example` prove that public
classification and subject-level soundness cannot replace one another.

The final layer retains two further boundaries.  Apoha complement structure
does not select an initial extension, and an operationally reliable cognition
does not force a later belief-revision assimilation policy.

## 刹那滅論：存在・因果効力・数的刹那性

[BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Ksanabhangasiddhi.lean)
formalizes a restrained *sattvānumāna*-style proof architecture.  The Japanese
label 刹那滅論 can refer broadly to the proof tradition, while surviving works
called *Kṣaṇabhaṅgasiddhi* are associated with more than one author.  The
module therefore models the shared proof obligations and does not present
itself as an edition of one author's work.

`exists_somewhere_iff_effective_somewhere` follows from the existing explicit
efficacy law.  The next step is deliberately named `SattvaPervasion`: every
existent in the domain is numerically momentary.  `sattva_certificate_sound`
uses subject existence and that pervasion as distinct proof fields.

`RootedTransport` is one sufficient bridge.  It assigns a root time to each
existent and transports every produced effect backward to the root through a
directed chain.  Together with the existing unique-effect-time law,
`rooted_transport_establishes_pervasion` and
`sattva_from_rooted_transport` derive numerical momentariness.  A local
certificate proves only the selected subject; it is not promoted to a global
pervasion.

The finite audits isolate both extra premises:

- `finite_nonuniformity_is_not_momentariness` exhibits an efficacious object
  with changing causal powers that exists at two times;
- `finite_existence_omits_sattva_pervasion` shows that existence supplies the
  reason while both pervasion and the thesis fail;
- `finite_model_has_no_rooted_transport` rules out the required rooted bridge
  in that model; and
- `finite_root_recovery_without_uniqueness_is_insufficient` retains backward
  root recovery while removing unique effect time, again defeating numerical
  momentariness.

## 真実綱要：範囲付き論争証明書

[BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tattvasamgraha.lean) provides
selected, scoped debate certificates motivated by the large work.  `Topic`
records eight
interfaces already supported by the repository: inference, dependent
own-being, Madhyamaka emptiness, causal origin, momentariness, three-times
activity, word meaning, and appearance/object comparison.  It is deliberately
not a chapter table.  The topic lists are unchecked descriptive annotations;
the proof fields do not establish historical provenance or coverage by the
exported adapters.

A `DebateRule` carries a topic trail, subject scope, opponent thesis, reason,
positive result, pervasion, and incompatibility proof.  A
`DebateCertificate` adds a subject, scope evidence, and reason evidence;
`DebateCertificate.sound` returns both the positive result and rejection of
the registered opponent thesis.  `DebateRule.compose` requires an explicit
connector and both scope checks, so crossing topics cannot manufacture a
premise.

Adapters reuse the audited inference, dependence, fourfold-causation,
momentariness, three-times, apoha, and appearance-model components.
Representative results include `dependence_inference_refutes_own`,
`causal_nonuniformity_refutes_intrinsic_power`,
`fixed_apoha_grounding_refutes_semantic_nonuniqueness`, and
`appearance_adequacy_does_not_fix_index_carrier_cardinality`.  The last result
concerns raw presentation-index types and does not supply object individuation.
Each conclusion keeps the scope and bridge used by its source component.

Three finite results about a separate generic registry block encyclopedic
overstatement:

- `debate_coverage_does_not_entail_joint_consistency` covers every selected
  topic while recording a direct conflict;
- `one_refutation_does_not_prove_all_buddhist_alternatives` rejects one rival
  thesis while supporting none of four listed alternatives; and
- `chapter_local_premise_does_not_become_universal` holds at the selected
  examination and fails under universal promotion.

## Cross-module dependency map

| Layer | Input exposed in Lean | Result justified by that input |
| --- | --- | --- |
| Perception | presented datum plus nonconceptuality | perceptual evidence at one object |
| Subject inference | reason at subject plus pervasion | thesis at that subject |
| Public proof | subject certificate plus comparison example | three marks and valid wheel classification |
| Concept selection | grounding, exemplar, or fixed feature requirement | one apoha extension/exclusion pair |
| Causal efficacy | reliable realization for a presented object | efficacy of that object |
| Momentariness | existence, unique effect time, rooted backward transport | one existence time for the numerical object |
| Debate composition | both scopes plus an explicit result-to-reason connector | the second registered result and refutation |

The table is a dependency audit.  It does not assert that the four historical
works form one deductive system or that a later author accepts every premise
used by an earlier interface.

## Verification and remaining evidence

All 115 Lean files compile with warnings treated as errors.  The aggregate
and Lake roots include all four files.  The checker rejects proof admissions,
project-defined axioms and constants, opaque or unsafe declarations, partial
definitions, and native-code proof shortcuts.

Reproduce from the repository root:

```sh
sh tools/check-lean.sh
python3 tools/check_names.py
python3 tools/check_text.py
python3 tools/make_index.py --check
python3 tools/check_publication.py
```

The remaining work is philological and interpretive: select an edition and
passage for each interface, defend the nonconceptuality and self-awareness
laws, justify the relevant pervasions and causal account, identify the intended
momentariness proof and identity criterion, and map the selected
*Tattvasaṃgraha* debates to chapter and verse.  Those tasks may motivate new
premises or countermodels, but the current Lean proofs do not discharge them.

Background used to delimit the reconstruction:

- [Dignāga's *Pramāṇasamuccaya*, Oxford Academic](https://academic.oup.com/book/50070/chapter-abstract/422359221)
- [Logic in Classical Indian Philosophy, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/archives/fall2016/entries/logic-india/)
- [Dharmakīrti, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/dharmakiirti/)
- [Ratnakīrti, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/ratnakirti/)
- [Ratnakīrti's *Kṣaṇabhaṅgasiddhi*, Austrian Academy EAST](https://east.ikga.oeaw.ac.at/data/32/98/)
- [Dharmottara's *Kṣaṇabhaṅgasiddhi*, Austrian Academy EAST](https://east.ikga.oeaw.ac.at/data/18/49/)
- [Śāntarakṣita, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/saantarak-sita/)
- [The *Tattvasaṃgraha* as a structured work, PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC10899820/)
- [Selected metaphysical chapters of the *Tattvasaṃgraha*, Oxford Academic](https://academic.oup.com/book/41380)
