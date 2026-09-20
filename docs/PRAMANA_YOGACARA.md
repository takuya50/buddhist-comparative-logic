# Pramāṇa and Yogācāra synthesis in Lean

Role: `supplement`

Lifecycle: `active`

Verified: 2026-09-19

## Scope

This batch joins the existing formalizations of Dignāga's wheel of reasons,
Dharmakīrti's three sources of pervasion, and Vasubandhu's *Viṃśatikā* without
identifying their different proof obligations.  Four Lean modules add a common
inference certificate, a conditional Yogācāra model, the eight-consciousness
taxonomy, and an observation-sensitive bridge between inference and ontology.

The result is a formal reconstruction, not a claim that one interpretation is
historically mandatory.  Pervasion, causal development, store support,
projected duality, and transformation remain named assumptions wherever the
corresponding conclusion needs them.

## 因明：主題上の推論と公開論証

[BuddhistComparativeLogic/Buddhist/Pramana/PramanaSynthesis.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/PramanaSynthesis.lean)
defines two layers:

- `DeductiveCertificate` contains possession of the reason at the subject and
  an explicit pervasion.  `deductive_sound` derives the subject thesis.
- `DialecticalCertificate` adds a positive comparison example.
  `dialectical_trairupya` and `dialectical_wheel_valid` then derive the three
  marks and a valid wheel cell.

The separation is exact enough to block three shortcuts.  A valid wheel with
all three marks may still have a false subject thesis
(`marks_and_valid_wheel_do_not_entail_subject`); pervasion may be vacuous when
the reason is absent at the subject
(`pervasion_without_subject_reason_is_insufficient`); and a sound
subject-level deduction may lack a distinct comparison subject and therefore
fail to occupy a valid wheel cell
(`sound_subject_inference_need_not_have_valid_wheel`).

The common certificate receives adapters for:

- an identity reason, through predicate inclusion (`ofSvabhavaHetu`);
- an effect reason, through a supplied causal law (`ofKaryaHetu`);
- non-apprehension of a perceptible item (`ofAnupalabdhi`);
- mode-indexed dependence and absence of own-being (`ofModeDependence`); and
- the existing Madhyamaka model (`ofMadhyamaka`).

## 唯識：三性・種子・転依

[BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraSynthesis.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraSynthesis.lean)
keeps four levels separate.

`adequate_appearance_has_matching_token_factorization` proves that an
appearance model satisfying the four *Viṃśatikā* conditions has an equally
adequate factorization through tokens copied from its observation tuples.
`ObjectIndexedAccount` does not encode mind-independence, persistence,
individuation, or a nonempty carrier.  The construction therefore establishes
only existential factorization of the presentation and efficacy predicates.

`Trisvabhava` treats the imagined, dependent, and perfected natures as three
analyses of one phenomenon.  The perfected analysis is dependent occurrence
without projected duality.  The finite `sampleTrisvabhava` model proves that
dependent and imagined analyses can coincide and that dependent occurrence
alone does not yield the perfected analysis.  The three labels are therefore
not encoded as disjoint entity classes.

`SeedTrajectory` and `EvolvesN` express finite causal lineage.  The lineage and
heredity theorems compose local development without an identity field.
`seed_continuity_does_not_require_an_unchanging_seed` gives a changing finite
trajectory, while `continuity_alone_does_not_supply_transformation` gives a
continuous afflicted trajectory with no transformation.

`TransformationAt` separately states the cut after which release and absence
of affliction persist.  `transformation_realizes_perfected_at_cut` reaches the
perfected analysis only after adding dependent occurrence and a bridge from
release to absence of projected duality.

## 八識：機能的役割

[BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraConsciousness.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/YogacaraConsciousness.lean)
represents five sensory roles, mental cognition, afflicted mind, and store
consciousness.  `eight_roles_exact` proves that the displayed list is
exhaustive, duplicate-free, and has length eight.  The roles are not declared
to be eight substances; `functional_roles_do_not_force_distinct_substances`
maps every role to one bearer and proves that the map is not injective.

`StoreSupportsNonStore` is an explicit process premise.
`nonstore_presentation_has_distinct_store_support` consumes that premise;
the finite theorem `taxonomy_and_activity_do_not_imply_support_or_permanence`
shows that all eight roles may be active while store support and permanent
store activity both fail.  `ProjectionBridge` likewise makes the move from
mental presentation plus afflicted appropriation to imagined subject/object
duality explicit, and `coactivity_alone_does_not_force_projected_duality`
shows why the bridge cannot be omitted.

The seven-entry list is named `nonStoreRoles`, and `NonStore` means only
inequality with the store role.  This avoids deciding whether afflicted mind
should be called manifest or subliminal in a particular historical account.

## 因明と唯識の接続

[BuddhistComparativeLogic/Buddhist/Yogacara/PramanaYogacara.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/PramanaYogacara.lean) turns an
observation-indexed inquiry into a `Dharmakirti.Model`.  Its pervasion is the
named `ObservationalLicense`; `conclusion_of_license` derives a target only
after that license and subject adequacy are supplied.

A `Defeater` consists of observation-equivalent adequate hypotheses that
disagree on the target.  Such a witness blocks unrestricted and improperly
restricted licenses and rules out every exact classifier computed only from
the observation record.  Concrete finite witnesses establish both boundaries:

- an appearance account with the empty carrier and an external candidate with
  the `Unit` carrier do not observationally decide inhabitedness; and
- one-object and two-object external accounts do not observationally decide
  object-domain cardinality.

`three_marks_do_not_establish_external_objects` strengthens the first witness:
subject possession, all three marks, and a valid wheel cell hold, while both
pervasion and the external-object thesis fail.  Restricting the candidate
domain to accounts already assumed external recovers exactly that scope
commitment and still does not determine cardinality.

## Verification and boundary

The batch also repairs the old observation-equivalence API so its location
type is genuinely polymorphic rather than accidentally fixed to the concrete
*Viṃśatikā* `Place` type.  All 115 Lean files compile with warnings treated as
errors.  The aggregate and Lake roots include all four new modules, and the
checker rejects admitted declarations and project-defined axioms.

Reproduce from the repository root:

```sh
sh tools/check-lean.sh
python3 tools/check_names.py
python3 tools/check_text.py
python3 tools/make_index.py --check
python3 tools/check_publication.py
```

Remaining work is evidential: defend a particular pervasion, three-nature
interpretation, seed-development relation, store-support law, projection
bridge, or transformation criterion from the intended text and practice.
Observation equivalence alone proves neither external-object existence nor
external-object absence.

Background used to delimit the reconstruction:

- [Yogācāra, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/yogacara/)
- [Dharmakīrti, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/dharmakiirti/)
- [Vasubandhu, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/vasubandhu/)
