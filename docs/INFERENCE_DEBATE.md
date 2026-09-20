# Four inference and debate interfaces in Lean

Role: `supplement`

Lifecycle: `active`

Verified: 2026-09-19

## Scope

This batch adds four Lean modules for bounded reconstructions of Nyāya public
inference, Dignāga's *Ālambanaparīkṣā*, Tibetan consequence debate, and the
Dharmakīrti–Ratnakīrti dispute about other streams of cognition.

The modules expose proof obligations and finite countermodels.  Their titles
identify the argument families under examination; they do not encode critical
editions, settle disputed interpretations, or identify the formal predicates
with every historical use of the corresponding terms.  In particular,
dialectical commitment is kept separate from semantic truth, and failure of a
local intentional-object or other-mind inference is not promoted to a global
ontological conclusion.

## Nyāya: five public members and semantic proof

[BuddhistComparativeLogic/Comparative/Nyaya/Nyaya.lean](../lean/BuddhistComparativeLogic/Comparative/Nyaya/Nyaya.lean) represents the five public
members `pratijna`, `hetu`, `udaharana`, `upanaya`, and `nigamana`.  The
ordered `PublicPresentation` contains only member labels.  A
`CompletePresentation` separately supplies reason possession at the subject,
the application, and an `Udaharana` containing both universal pervasion and a
distinct positive illustration.

`complete_presentation_sound` extracts a `SemanticProof`, whose only
deductive inputs are subject reason and pervasion.  The transformations
`CompletePresentation.compressToThree` and
`ThreeMemberPresentation.compressToTwo` remove repeated public information.
The two-member proof remains conditional on an explicit `SharedBackground`;
the positive example is never used to manufacture universal pervasion.

The concrete audit contains three boundaries:

- `smokeFire_nonvacuous` supplies positive subject and comparison cases and a
  negative comparison case;
- `one_example_does_not_entail_pervasion` gives a positive illustration with
  a counterinstance to the universal rule; and
- `missing_reason_and_application_does_not_establish_thesis` retains a valid,
  nonempty example member while the disputed subject has neither the reason
  nor the thesis.

## Ālambanaparīkṣā: causal production and image similarity

[BuddhistComparativeLogic/Buddhist/Yogacara/Alambanapariksa.lean](../lean/BuddhistComparativeLogic/Buddhist/Yogacara/Alambanapariksa.lean) defines
the local proxy `IsAlambana object cognition` as the conjunction of causal
production and image similarity.  `TwoHornFailure` keeps the two substantive
premises explicit: a causally contributing atom collection lacks the required
similarity, while an image-similar composite whole lacks independent causal
production.

`two_horn_exclusion` eliminates both constructors of the deliberately bounded
`Candidate` type.  `concrete_horns_are_nonvacuous` supplies a genuine two-atom
collection and a separate whole, so the proof is not an empty-domain result.
`causal_production_alone_is_insufficient` and
`similarity_alone_is_insufficient` independently refute either one-condition
shortcut.

The `World` extension adds external existence without defining a bridge from
it to intentional-object status.
`two_horn_exclusion_is_compatible_with_external_existence` places the actual
`TwoHornFailure` premises, exclusion of every modeled collection/composite,
and external existence of those same candidates in one concrete nonvacuous
world.  The
smaller inhabited `boundaryWorld` independently shows that an external stone
can fail the similarity condition.  Therefore
`local_failure_does_not_entail_external_nonexistence` and
`local_failure_does_not_entail_global_idealism` delimit the local dilemma's
ontological scope.

## Tibetan consequence debate: ledgers, replies, and termination

[BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Debate.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/Tibetan/Debate.lean) defines
challenger and defender roles, separate commitment ledgers, and a consequence
with subject-reason, pervasion, and conclusion labels.  The three modeled
replies are acceptance, reason not committed, and pervasion not committed.
The latter two use a closed-world ledger convention: absence means only lack
of dialectical commitment, not semantic falsity, refutation, or the historical
claim that an obligation has been disproved.  They form a selected
proof-theoretic core rather than an exhaustive historical vocabulary.

`reason_and_pervasion_acceptance_commits` and
`accepted_response_commits_conclusion` establish the commitment effect of a
legal acceptance.  The two noncommitment-target theorems identify the absent
ledger entry, while `legal_reply_exhaustive` produces a legal reply under
decidable equality.  `legal_reply_unique` proves the selected replies are
exclusive.  An atomic `Move` is legal only from an idle state, so its issue
step cannot overwrite an unresolved consequence; `resolve_extends` and
`run_extends` prove that execution does not discard earlier commitments.

Termination is strategy-relative.  A `NewCommitmentTrace` accepts only a
conclusion absent from the current defender ledger.
`conclusionTrace_nodup`, `finite_termination_bound`, and
`no_overlong_new_commitment_trace` bound such a trace by the explicit finite
language.  `arbitrarily_long_legal_loop` constructs a legal stuttering
noncommitment response of any requested length on a one-claim language when
freshness is removed.

`PramanaBridge.challenge_sound` interprets the two obligation labels using a
`Dharmakirti.Model`; `challenge_is_global_pervasion` connects the pervasion
label to the repository's audited global inference scope.  Ledger membership
itself is never asserted to be semantic truth.

## Other minds: behaviour, volition, and observational equivalence

[BuddhistComparativeLogic/Buddhist/Pramana/OtherMinds.lean](../lean/BuddhistComparativeLogic/Buddhist/Pramana/OtherMinds.lean) separates observable
behaviour from inferred volition.  `StreamModel.inference` embeds one selected
behaviour-to-volition inference into the existing `Dharmakirti.Model`.
`volition_of_license` and `has_volition_of_license` require both observed
behaviour and an explicit universal `BehaviourLicense`.
`other_stream_of_license` additionally requires distinction from the selected
self; volition alone is not labeled an other stream.

The `mindedAccount` and `automatonAccount` have definitionally identical
behaviour while disagreeing about the distinct apparent other's volition.
`behaviour_does_not_exactly_classify_other_minds` consequently rules out an
exact classifier whose only input is behaviour.  This does not rule out
defeasible or probabilistic support.  `first_person_analogy_needs_pervasion`
shows that a calibrated self case plus matching public behaviour leaves the
other-agent conclusion open, and `unmanifest_volition_boundary` shows that
absence of the selected behaviour does not establish absence of volition.

The final `StandpointAccount` records conventional and ultimate distinctness
as separate relations.  `conventional_of_license` combines an explicit
conventional-distinctness premise with the licensed observed behaviour.
`conventional_does_not_entail_ultimate_distinctness` keeps the stronger
ultimate premise separate from that derived conventional conclusion.

## Dependency summary

| Interface | Positive result | Explicit boundary |
| --- | --- | --- |
| Nyāya public proof | subject reason plus pervasion establishes the thesis | one positive example and public tags do not establish those premises |
| Intentional object | causal production plus image similarity establishes the local proxy | either condition alone fails; local failure does not entail external nonexistence |
| Consequence debate | accepted obligations add the conclusion to the defender ledger | commitment is not truth; finite language alone does not force termination |
| Other-mind inference | licensed behaviour establishes one corresponding volition | observational equivalence blocks exact behaviour-only classification |

## Verification and remaining evidence

All four modules are aggregate imports and Lake roots.  The isolated checker
checks the resulting 115-file development with warnings treated as errors
and rejects proof admissions, project axioms/constants, opaque or unsafe
declarations, partial definitions, and native-code proof shortcuts.

Reproduce from the repository root:

```sh
sh tools/check-lean.sh
python3 tools/check_names.py
python3 tools/check_text.py
python3 tools/make_index.py --check
python3 tools/check_publication.py
```

Remaining work is evidential: attach edition-specific passages to each proxy,
justify the chosen Nyāya member semantics and compression background, defend
the two *Ālambanaparīkṣā* horn premises, distinguish rules across Tibetan
manuals and institutions, and decide whether a selected other-mind argument is
deductive, defeasible, or probabilistic.  Lean verifies consequences from
those choices but does not provide the philological evidence for them.

Background used to delimit the reconstructions:

- [Nyāya, Internet Encyclopedia of Philosophy](https://iep.utm.edu/nyaya/)
- [Yogācāra, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/yogacara/)
- [Ratnakīrti, Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/ratnakirti/)
- [Tibetan Buddhist Logic, Austrian Academy of Sciences](https://www.austriaca.at/0xc1aa5576_0x003dc42b.pdf)
