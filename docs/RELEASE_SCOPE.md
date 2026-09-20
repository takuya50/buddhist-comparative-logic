<!-- SPDX-License-Identifier: CC0-1.0 -->

# Software release scope

This file records module inclusion for the planned `v0.1.0` research-software
release separately from proof status. It does not assert that the standalone
release tag exists. The code repository is currently private. All Lean files in both sets compile under
the pinned toolchain and contain no admitted declarations. “Experimental”
means that the mapping from formal predicates to historical passages still
needs work; it does not mean that Lean accepted a weaker proof.
“Author-reviewed” below is the sole author's source-and-scope classification
for this corpus. It is self-review, not independent or external peer review.

The three aggregate imports are:

- `BuddhistComparativeLogic.Release`: 110 author-reviewed subject and infrastructure modules;
- `BuddhistComparativeLogic.Experimental`: two compiling modules retained for source review;
- `BuddhistComparativeLogic`: the complete 112-module research tree, including both sets.

The table below records 22 Lean modules that meet the release source-review
criteria. Two related modules remain experimental because their exact
historical-to-formal mappings are not yet supported. None of these 24 modules
has a direct Isabelle theory counterpart. All compile and contain checked
formal results; release classification additionally requires the source basis,
passage mapping, and claim boundary recorded here and in the generated catalog.

## Author-reviewed release modules

| Module | Source basis | Claim boundary |
| --- | --- | --- |
| `BuddhistComparativeLogic.Buddhist.Abhidharma.Analysis` | *Abhidharmakośabhāṣya* VI.4 and bhāṣya, GRETIL markers 333.23–334.13 | The pot/water analysis is passage-aligned; the finite complement theorem and rewrite adapter are modern. |
| `BuddhistComparativeLogic.Buddhist.Pramana.AnupalabdhiKinds` | *Nyāyabindu* 2.31–42 | Eleven deployments and typed side conditions are auditable; the module is not a critical edition. |
| `BuddhistComparativeLogic.Comparative.Grammar.Bhartrhari` | *Vākyapadīya* 3.3.26 and secondary orientation | Language stages and the FDE comparison are labelled as modern reconstructions. |
| `BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.BsdusGrwa` | Ngag-wang-tra-shi, *Collected Topics*, chapter 1, pp. 31–32 | The four color/shape witness cells are passage-aligned; Boolean predicates are a modern extensionalization. |
| `BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Fazang.Mereology` | CBETA T45 no. 1866, 507c3–508a22, with secondary orientation | The six characteristics and rafter-house case are fixed; intervention and interpenetration predicates are operational definitions. |
| `BuddhistComparativeLogic.Comparative.ChineseThought.HardWhite` | Received *Jianbai lun*, with Graham and the University of Zurich for orientation | The sensory contrast is fixed; the one-stone model does not settle authorship, date, or intended metaphysics. |
| `BuddhistComparativeLogic.Comparative.Jaina.JainaChange` | *Tattvārthasūtra* 5.29, or 5.30 in another recension | The recension difference is recorded; the three change predicates and boundary models are explicit. |
| `BuddhistComparativeLogic.Comparative.Jaina.JainaInference` | `anyathānupapatti`, two-member inference, and a primary-text work locator | The modal semantics is bounded, and actual inclusion is separated from modal necessity. |
| `BuddhistComparativeLogic.Comparative.Mimamsa.MimamsaSentenceMeaning` | Śālikanātha, *Vākyārthamātṛkā* I, with Saxena’s study | The two historical architectures are located; the typed computation interfaces and bridge are modern. |
| `BuddhistComparativeLogic.Comparative.Mimamsa.MimamsaViniyoga` | *Mīmāṃsāsūtra* 3.3.14 | The six grounds and their relative weakening are passage-aligned; numeric ranks and the resolver are modern. |
| `BuddhistComparativeLogic.Comparative.Nyaya.NavyaNyayaAbsence` | Sen and Chatterjee pp. 83–85, Ganeri pp. 111–121, and SEP §§11.2–11.3 | Secondary orientation supports the four kinds of qualification; no primary four-place formula or historical detection law is claimed. |
| `BuddhistComparativeLogic.Buddhist.Madhyamaka.NegandumCalibration` | SEP §3 and Garfield–Thakchöe, chapter 5 | This is explicitly secondary orientation only; the extensional overreach/underreach predicates are project-authored. |
| `BuddhistComparativeLogic.Comparative.Nyaya.Nyayakusumanjali` | Received fifth section, verse 5.1 and the `kāryāt` prose, with Ruzsa 2022 | The maker-inference route is fixed; the module does not prove God or attribute uncontested authorship. |
| `BuddhistComparativeLogic.Comparative.Grammar.PaniniDerivation` | *Aṣṭādhyāyī* 1.4.2, with Rajpopat 2023 | The priority metarule motivates the interface; ranks, lists, termination, and determinism are modern infrastructure. |
| `BuddhistComparativeLogic.Buddhist.Pramana.Pratyaksabhasa` | Dignāga PS(V) 1.3c, 1.7c–8b and Dharmakīrti *Nyāyabindu* 1.4–1.6 | The narrow criteria are passage-aligned; the Boolean comparison is not a complete theory of perception. |
| `BuddhistComparativeLogic.Buddhist.Abhidharma.Pudgala` | *Abhidharmakośabhāṣya* IX and secondary locators | Conventional person and an added immutable substance remain distinct, with every exclusion bridge named. |
| `BuddhistComparativeLogic.Comparative.Samkhya.Satkaryavada` | *Sāṃkhyakārikā* 9 and secondary orientation | Production, capacity, and latent presence remain separate predicates; converses are tested rather than assumed. |
| `BuddhistComparativeLogic.Buddhist.Yogacara.Svasamvedana` | Dignāga PS(V) 1.6ab and 1.9–12, especially 1.11c–d | Self-awareness and recollection are located; trace and uniqueness fields are modern typed decompositions. |
| `BuddhistComparativeLogic.Comparative.Nyaya.Tarka` | *Nyāyasūtra* 1.1.40 and Kang 2010 | The doubt-removing orientation is fixed; the counterfactual rule and FDE comparison are modern. |
| `BuddhistComparativeLogic.Buddhist.Hermeneutics.Vyakhyayukti` | *Vyākhyāyukti* saṃgrahaśloka 1, Lee’s Tibetan edition, Ueno pp. 95–96, and folio 30b | The five tasks are passage-aligned; coverage predicates and certificates are a modern checklist. |
| `BuddhistComparativeLogic.Buddhist.Pramana.Vyaptinirnaya` | Ratnakīrti’s *Vyāptinirṇaya* and a research-project locator | Observation, causal licence, scope, and defeaters are separated in a bounded reconstruction. |
| `BuddhistComparativeLogic.Buddhist.ChineseBuddhism.Xuanzang.Inference` | Tang 2018, pp. 143–150 and edited materials Texts 1.1, 1.9, and 5.2 | The three qualifications and Wŏnhyo counter-inference are mapped while authenticity and interpretation remain contested. |

## Retained for source review

| Module | Registered evidence | Remaining reason for deferral |
| --- | --- | --- |
| `BuddhistComparativeLogic.Comparative.Vedanta.Sriharsa` | Jha, chapter I §14, paras. 257–259, and Das’s map to named *Khaṇḍanakhaṇḍakhādya* passages | No precise primary passage is mapped to underextension; direct reciprocal dependency and Boolean `sameProfile` are narrower modern surrogates for the cited criticisms. |
| `BuddhistComparativeLogic.Buddhist.KoreanBuddhism.WonhyoHwajaeng` | Muller’s translation of the fragmentary *Simmun hwajaeng non* and his 2015 study | The sources support attention to background, aims, assumptions, and divergence, but not coverage, overlap agreement, or sheaf-like gluing. |

## Promotion rule

An experimental module moves into `BuddhistComparativeLogic.Release` when its catalog entry
has a fixed primary passage or an explicit “secondary orientation only” label,
the module header states which formal predicate corresponds to which textual
claim, and its import closure contains no unrelated historical module without
an explained reusable-interface dependency. Promotion does not require a
historical interpretation to be uncontested; it requires the disagreement and
the formalization’s chosen boundary to be visible.
