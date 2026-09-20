# Open evidence and generalization problems

Role: `supplement`

Lifecycle: `active`

Verified: 2026-09-19

The current open work is to identify additional explicit matrices, supply and
maintain philological data, and defend the premises that connect the formal
interfaces to philosophical or cognitive claims. [`LEAN_PROGRESS.md`](LEAN_PROGRESS.md)
records the checked Lean interfaces and their remaining evidence obligations;
the `Verified:` date above records the 2026-09-19 full Isabelle2025-2/PDF
receipt.

## P1. Universal designation beyond the classified bases

The positive and unrestricted universal-designation relations are identified
for the classical, K3, LP, and FDE bases:

- `priest_open_question_classical`
- `priest_open_question_k3`
- `priest_open_question_lp`
- `priest_open_question_fde`

The first and K3 cases reduce to K3-style consequence, while the LP and FDE
cases reduce to FDE-style consequence, followed where needed by the existing
variable restriction.  `pos_upentails_iff` and `upentails_iff` additionally
give an exact theorem for adjoining one undesignated operation-absorbing value
to an arbitrary `MVLogic`: base positive consequence plus collective atom
coverage, except when the restricted base premises are positively
unsatisfiable.

`MatrixIso.entails_iff`, `MatrixIso.pos_upentails_iff`, and
`MatrixIso.upentails_iff` transport all three consequence notions across
an explicit operation- and designation-preserving bijection.  The Boolean
truth/falsity-pair presentation `fdeBitIso` is a checked instance.

Remaining work is therefore input-specific classification.  Any further
member of Priest's family must be given as an explicit finite matrix with its
exact designation convention, then equipped with a `MatrixIso` to one of
these constructions or analyzed separately.  Neither a shared number of
values nor an informal description as “ineffable” supplies that proof;
absorption, designation, and operation preservation remain hypotheses.

## P2. Justifying the argument-to-practice premises

The formal pipeline is complete as a conditional theorem.  Mode-indexed
dependence and coverage feed absence of own-being; exact fourfold origin cases
feed non-intrinsic production; observation and assimilation feed belief
revision; revision feeds bounded release.  The endpoints are
`dependence_to_bounded_release` and `fourfold_to_bounded_release`.

`middle_way_on_covered_domain`, `comparison_completes_three_marks`, and
`fourfold_middle_way` make the scope, inference, and ordinary-occurrence
steps explicit.  `DependenceReleaseCertificate` and
`FourfoldReleaseCertificate` attach individual references to each premise and
feed the same bounded-release results; the latter also requires occurrence of
its event, as checked by
`nonoccurring_chain_event_has_no_release_certificate`.  Shipped internal
locators are compiler-resolved declaration names,
while external locators are unchecked annotations.  `CitedClaim` deliberately
carries no proof: `citation_metadata_can_accompany_a_false_claim` and
`certified_false_is_uninhabited` show why a reference alone cannot inhabit a
proof-bearing `Certified` premise.

The open work is to justify the interfaces independently:

- why causal, mereological, or conceptual dependence excludes the selected
  notion of own-being;
- why the event-level origin classification is exhaustive and why each
  incompatibility law holds;
- why an observation is assimilated, why support obeys the update discipline,
  and why the resulting rank is an adequate model of attachment;
- why the two current tier assertions are the right attachment focus, and why
  a least common consequence followed by ultimate reversal is the right
  response standard.

Lean prevents these premises from being smuggled into the conclusions and
supplies independent omission models.  Historical exegesis, empirical
psychology, and premise selection require evidence outside the kernel.

The pramāṇa interface is mechanically consolidated.
`DeductiveCertificate` contains subject possession and pervasion, while
`DialecticalCertificate` adds the positive comparison example used by the
three marks and wheel.  `marks_and_valid_wheel_do_not_entail_subject` and
`three_marks_do_not_establish_external_objects` give finite witnesses against
using dialectical classification as subject-level soundness.  What remains is
to justify the selected pervasion and candidate domain in the intended debate;
the certificate makes that obligation visible but cannot discharge it.

## P3. Sanskrit and Tibetan evidence

`sanskrit_canonical_key_alignment_valid`,
`tibetan_canonical_key_alignment_valid`, and
`longer_frame_alignment_valid` check finite canonical maps. Bounded excerpts
from the GRETIL Sanskrit text and Silk's Tibetan Recension B discharge all four
central lexical obligations. `sanskrit_diplomatic_not_order_preserving` and
`tibetan_diplomatic_not_order_preserving` record that the two source texts put
the nominal HS07 counterpart before the non-separation HS06 counterpart,
opposite to the Chinese clause-key order. Missing evidence still remains an
explicit obligation in the generic interface.

`lexical_validation_is_construal_neutral`,
`structural_alignment_does_not_force_character_counts`, and
`structural_alignment_does_not_force_text_equivalence` show that structural
and surface validity entail neither a chosen construal, equal length, nor
textual identity.

The continuing task is philological rather than a missing alignment
algorithm: maintain edition identifiers and token boundaries, add witnesses
for further clauses and recensions, and argue which construal a witnessed
phrase supports.  A token match by itself does not decide identity, mutual
predication, non-separation, or an illusion comparison.

## P4. Stronger causal and semantic foundations

`causal_nonuniformity` establishes that an efficacious existent cannot retain
one intrinsic causal power at all times.  It does not establish literal
momentariness.  `momentary_of_rooted_causalChains` supplies a sufficient bridge
using unique effect time, local two-way effect transport, and a rooted finite
causal chain. A weaker formal theorem,
`momentary_of_rooted_directedChains`, uses only backward transport of each
observed effect to its root, and
`directed_transport_does_not_imply_forward_transport` supplies a finite model
where the directed theorem applies although forward transport fails.  What
remains is to justify rootedness, unique effect time, and the chosen directed
link relation for the intended causal interpretation.  The theorem is stated
over the existing `Momentariness.Theory` record, whose two-times witness is
needed elsewhere but is not used in this directed proof.

For componential apoha, `fixed_features_determine_unique_pair` gives
uniqueness relative to a chosen requirement.  `stable_requirement_stops_regress`
formalizes fixed-point termination for features of features, while
`self_excluding_regress_never_stops` supplies a two-cycle at every finite
stage.  `selected_grounding_unique` proves at-most-one selected pair when
admitted optimal requirements are antisymmetric under the comparison rule;
`selected_grounding_exists` separately constructs a pair from a supplied
optimum.  The tied finite model
`admissibility_without_antisymmetry_is_underdetermined` proves that candidate
admissibility alone cannot select a pair.  What remains is to justify the
concrete admissibility predicate, comparison rule, existence of an optimum,
and higher-level grounding for an intended apoha account.

The Yogācāra structural targets are also formalized conditionally.
`Trisvabhava` relates dependent occurrence, projected duality, and the
perfected analysis; `SeedTrajectory` composes local development without an
identity field; and `TransformationAt` states a persistent transition out of
affliction.  `eight_roles_exact` checks the eight-consciousness taxonomy as
functional roles.  Finite countermodels show that conditioned occurrence is
not yet the perfected analysis, seed continuity does not require an
unchanging seed, continuity alone does not produce transformation, and the
role taxonomy does not imply store support or permanence.

The remaining Yogācāra work is interpretive and evidential: justify the chosen
projection bridge, development relation, transformation cut, store-support
law, and their relation to particular texts or practice models.  The joint
pramāṇa module additionally proves that the current appearance and efficacy
observations decide neither external-object existence nor object-domain
cardinality.  A stronger ontological conclusion needs evidence that is not
invariant across those observation-equivalent countermodels.

## P5. Treatise-level textual alignment

The four treatise modules expose their selected formal interfaces.
Perceptual and inferential evidence have separate types; pramāṇa reliability
has explicit occurrence and novelty fields; *sattva* inference exposes its
global pervasion and a sufficient rooted-transport bridge; and selected
*Tattvasaṃgraha* debates carry topic, subject scope, reason, result, and
refutation data.

The open work is to connect each interface to evidence:

- identify the edition, chapter, verse range, and translation supporting each
  proposed rule;
- defend the chosen nonconceptuality, self-awareness, content, reliability,
  and causal-efficacy readings;
- distinguish which positive or negative momentariness proof is intended and
  justify its identity criterion, global pervasion, unique effect time, and
  directed root relation; and
- map the selected *Tattvasaṃgraha* topic registry to its actual chapter order
  and interlocutors without treating coverage as joint consistency.

Until that evidence is added, the module titles report their design target,
not critical-edition completeness or a uniquely correct historical reading.
[`PRAMANA_TREATISES.md`](PRAMANA_TREATISES.md) gives the exact theorem boundary.

## Mechanically closed targets

- **FDE/FDE5 proof calculi.** `deriv_sound_complete` proves natural-deduction
  completeness by nonempty DNF; `tableau_sound_complete` proves analytic
  tableau completeness; `tableau_iff_deriv` connects the proof objects.  The
  containment-enriched FDE5 counterparts are complete too.
- **Catuṣkoṭi–K3–FDE comparison.** `k3_entails_iff_fde_no_gluts` proves the
  exact restricted consequence equivalence; `explosion_strictly_separates_k3_from_fde`
  proves the reverse unrestricted implication false; and
  `k3_corner_image_exact` computes the embedded K3 corners.  The remaining
  question is interpretive: which matrix and which designation quantifier, if
  either, models a particular historical fourfold passage.
- **A non-definitional path layer.** `eventual_release_from_revision` gives a
  finite bound from explicit update laws, and the modules include failure
  models for observation, assimilation, support discipline, persistence, and
  relapse.
- **Dynamic naya.** `route_realizes_mode` and `route_is_length_minimal` cover
  all seven modes. `Supports` is monotone under appended observations, while
  `ExactlyLicenses` intentionally records only exact profiles.
- **Interval motion.** `interval_motion_traverses` supplies the positive
  relation over endpoints and time; `same_present_different_motion` proves
  that present position does not determine motion.
- **Twenty Verses comparison.** `every_appearance_account_has_token_factorization`
  and `object_index_cardinality_is_observationally_underdetermined` compare an
  appearance account with neutral object-indexed factorizations.  The generic
  construction does not supply mind-independence, persistence, or even an
  inhabited carrier.
- **Dharmakīrti adapter.** `empty_via_explicit_pervasion` exposes the precise
  pervasion premise used by the emptiness inference.

These closures concern formal implementation.  They do not close the evidence
and interpretation questions in P1–P4.
