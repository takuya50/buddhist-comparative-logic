# Catuṣkoṭi, K3, and FDE in Lean

Role: `supplement`

Lifecycle: `active`

Verified: 2026-09-19

## Scope

[BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean](../lean/BuddhistComparativeLogic/Core/CatuskotiK3FDE.lean)
connects three formal objects already used throughout the development:

- `Koti`, the four outcomes obtained from designation of a value and its
  negation;
- the strong Kleene K3 matrix with values true, undetermined, and false; and
- FDE with the four independent truth/falsity-bit values `T`, `B`, `N`, and
  `F`.

The namespace `K3` names the three-valued logic.  The constructor `Koti.K3`
names the third corner, where both a value and its negation are designated.
They are different Lean objects despite the shared printed abbreviation.

This is an algebraic comparison of the matrices fixed by the repository.  It
does not identify those matrices with every historical interpretation of the
four alternatives.

## K3 inside FDE

`k3Embed` maps K3 true, undetermined, and false to FDE `T`, `N`, and `F`.
`k3Embed_range_iff` proves that its image is exactly the FDE values other than
the glut `B`; `k3Embed_injective` proves that no two K3 values collapse.

Theorems `k3Embed_neg`, `k3Embed_conj`, and `k3Embed_disj` establish closure
and preservation of all three primitive connectives.  `eval_k3Embed` lifts
that result from values to every formula, while `designated_k3Embed` and
`sat_k3Embed` preserve designation and satisfaction.

Thus the phrase “K3 is the non-glut FDE submatrix” is discharged by an actual
embedding, an exact range theorem, operation preservation, and designation
preservation.

## Consequence and its strict boundary

`fdeEntailsNoGluts` quantifies over FDE valuations that assign no atom the
value `B`.  The exact scope result
`k3_entails_iff_fde_no_gluts` proves equivalence with K3 consequence for every
theory and conclusion.

Because unrestricted FDE quantifies over more valuations,
`fde_entails_implies_k3_entails` gives the sound direction from FDE consequence
to K3 consequence.  The reverse implication fails:
`explosion_strictly_separates_k3_from_fde` proves explosion from contradictory
premises in K3 and gives the FDE countervaluation with a glut premise and an
unrelated gap conclusion.

## Exact four-corner comparison

`fde_corner_table` computes:

| FDE value | Corner |
| --- | --- |
| `T` | `Koti.K1` |
| `F` | `Koti.K2` |
| `B` | `Koti.K3` |
| `N` | `Koti.K4` |

`fde_corner_injective` proves that the classifier loses no information on the
four FDE values.  `fde_both_corner_iff` and `fde_neither_corner_iff` isolate
the glut and gap corners exactly.

`k3_corner_preserved` shows that the K3 embedding commutes with corner
classification.  `k3_corner_image_exact` proves that its image realizes
exactly `Koti.K1`, `Koti.K2`, and `Koti.K4`; `k3_has_no_both_corner` rules out
`Koti.K3`.  FDE realizes all four through the existing `fde_koti_all` theorem.

## Existential and universal classification

For a set of possible values, the existing `pkoti_of` classifier asks whether
the set intersects the designated values.  `universalKoti` instead asks
whether every possible value is designated.  The positive and negative
characterization theorems expose those quantifiers directly.

`empty_set_separates_universal_and_existential` proves the sharp empty-set
boundary: universal classification returns the both corner because both
subset claims are vacuous, while existential classification returns the
neither corner because neither intersection has a witness.
`singleton_universal_eq_existential` proves that this distinction disappears
on singleton value sets.

## Verification and limits

The aggregate and Lake roots include this module.  All 115 Lean files compile
with warnings treated as errors.  The strict source gate rejects proof
admissions, project axioms/constants, opaque or unsafe declarations, partial
definitions, and native-code proof shortcuts.

The formal conclusions concern the explicitly defined matrices, designation
sets, and quantifiers.  Whether a passage should be modeled by K3, FDE, a
particular corner, existential designation, or universal designation remains
an interpretive input.

Reproduce from the repository root:

```sh
sh tools/check-lean.sh
python3 tools/check_names.py
python3 tools/check_text.py
python3 tools/make_index.py --check
python3 tools/check_publication.py
```
