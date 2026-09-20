/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Pramanasamuccaya
import BuddhistComparativeLogic.Buddhist.Pramana.Pramanavarttika

/-!
# A finite audit of perception and perceptual semblance

This module compares two deliberately narrow formal criteria associated with
Dignāga and Dharmakīrti: freedom from conceptual construction, and freedom
from error in addition to nonconceptuality.  It is not an edition or complete
interpretation of either author's account of perception or
*pratyakṣābhāsa*.  In particular, the predicates `erroneous` and `true` are
independent inputs rather than a claimed reconstruction of a single Sanskrit
term.

The refinement theorem is accompanied by a finite two-moons model.  That
model separates nonconceptuality, nonerror, and truth instead of defining one
through another.  Typed adapters reuse the existing `Pramanasamuccaya`
perception interface and the operational cognition interface in
`Pramanavarttika`; the latter derives reliability from an explicit bridge law
rather than inserting the desired pramāṇa conclusion into the model.

Source mapping (accessed 2026-09-19): Dignāga's nonconceptual criterion is
aligned with *Pramāṇasamuccaya(vṛtti)* 1.3c, and the apparent-perception list
with 1.7c–8b, in Ernst Steinkellner's revised 2014 hypothetical Sanskrit
reconstruction
(https://www.oeaw.ac.at/fileadmin/Institute/IKGA/PDF/digitales/dignaga_PS_1.pdf).
Dharmakīrti's added nonerror condition is aligned with *Nyāyabindu* 1.4–1.6
in the GRETIL text based on Dwarikadas Shastri's 1994 edition, pp. 42–50
(https://gretil.sub.uni-goettingen.de/gretil/1_sanskr/6_sastra/3_phil/buddh/bsa057_u.htm).
The module does not reproduce either source's translation: `conceptual`,
`erroneous`, and `trueCognition` are independent, project-authored predicates,
and the two-moons model is a formal boundary example rather than a rendering
of either passage.
-/

namespace BuddhistComparativeLogic.Pratyaksabhasa

/-- Three independent assessments of a cognition. -/
structure CognitionModel (Cognition : Type u) where
  conceptual : Cognition → Prop
  erroneous : Cognition → Prop
  trueCognition : Cognition → Prop

namespace CognitionModel

variable {Cognition : Type u} (model : CognitionModel Cognition)

/-- The minimal Dignāga-side candidate used here: nonconceptual cognition. -/
def DignagaCandidate (cognition : Cognition) : Prop :=
  ¬ model.conceptual cognition

/-- The stricter Dharmakīrti-side candidate used here: nonconceptual and
nonerroneous. -/
def DharmakirtiCandidate (cognition : Cognition) : Prop :=
  model.DignagaCandidate cognition ∧ ¬ model.erroneous cognition

/-- Truth is kept as a separately inspectable predicate. -/
def Veridical (cognition : Cognition) : Prop :=
  model.trueCognition cognition

theorem dharmakirti_refines_dignaga {cognition : Cognition}
    (candidate : model.DharmakirtiCandidate cognition) :
    model.DignagaCandidate cognition :=
  candidate.1

/-- Identity appearance turns a cognition into an object of the project's
existing perception interface.  Its nonconceptual predicate is exactly the
present Dignāga-side criterion. -/
def toPerceptionModel :
    BuddhistComparativeLogic.Pramanasamuccaya.PerceptionModel Cognition Cognition where
  appearance := id
  nonconceptual := model.DignagaCandidate

def toPerceptualEvidence {cognition : Cognition}
    (candidate : model.DignagaCandidate cognition) :
    BuddhistComparativeLogic.Pramanasamuccaya.PerceptualEvidence
      model.toPerceptionModel cognition where
  datum := cognition
  presented := rfl
  nonconceptual := candidate

theorem adapter_preserves_nonconceptuality {cognition : Cognition}
    (candidate : model.DignagaCandidate cognition) :
    model.toPerceptionModel.nonconceptual
      (model.toPerceptionModel.appearance cognition) :=
  (model.toPerceptualEvidence candidate).appearance_is_nonconceptual

end CognitionModel

/-- Positive evidence that the stricter criterion is a proper refinement:
every stricter candidate satisfies the weaker criterion, and an actual
weaker candidate fails the added nonerror condition. -/
structure StrictRefinementCertificate
    (model : CognitionModel Cognition) where
  inclusion : ∀ cognition,
    model.DharmakirtiCandidate cognition →
      model.DignagaCandidate cognition
  witness : Cognition
  dignagaCandidate : model.DignagaCandidate witness
  notDharmakirtiCandidate : ¬ model.DharmakirtiCandidate witness

namespace StrictRefinementCertificate

variable {Cognition : Type u} {model : CognitionModel Cognition}

theorem proper_subset (certificate : StrictRefinementCertificate model) :
    (∀ cognition, model.DharmakirtiCandidate cognition →
      model.DignagaCandidate cognition) ∧
      ∃ cognition, model.DignagaCandidate cognition ∧
        ¬ model.DharmakirtiCandidate cognition :=
  ⟨certificate.inclusion,
    ⟨certificate.witness, certificate.dignagaCandidate,
      certificate.notDharmakirtiCandidate⟩⟩

end StrictRefinementCertificate

/-! ## A nonvacuous bridge to operational cognition -/

/-- The existing operational cognition model plus one explicit law connecting
absence of error to operational reliability.  Occurrence, novelty, and
content remain separate obligations. -/
structure OperationalBridge
    (profile : CognitionModel Cognition)
    (Object : Type v) (Result : Type w) where
  operational :
    BuddhistComparativeLogic.Pramanavarttika.CognitionModel Cognition Object Result
  nonerroneousReliable : ∀ cognition,
    ¬ profile.erroneous cognition → operational.Reliable cognition

namespace OperationalBridge

variable {Cognition : Type u} {Object : Type v} {Result : Type w}
  {profile : CognitionModel Cognition}

/-- A stricter perceptual candidate becomes an operational pramāṇa only when
the independent occurrence, novelty, and content premises are also given. -/
theorem toPramana (bridge : OperationalBridge profile Object Result)
    {cognition : Cognition}
    (candidate : profile.DharmakirtiCandidate cognition)
    (occurs : bridge.operational.occurs cognition)
    (novel : bridge.operational.novel cognition)
    (content : bridge.operational.HasContent cognition) :
    bridge.operational.Pramana cognition :=
  ⟨occurs, novel, content,
    bridge.nonerroneousReliable cognition candidate.2⟩

end OperationalBridge

/-! ## Inhabited finite two-moons model -/

inductive SampleCognition where
  | clearMoon
  | twoMoons
  | trueJudgment
  | falseJudgment
  deriving DecidableEq, Repr

/-- `twoMoons` is nonconceptual but erroneous; `trueJudgment` is conceptual
but true.  `falseJudgment` supplies a nonerroneous but false cognition. -/
def twoMoonsModel : CognitionModel SampleCognition where
  conceptual
    | .clearMoon | .twoMoons => False
    | .trueJudgment | .falseJudgment => True
  erroneous
    | .twoMoons => True
    | .clearMoon | .trueJudgment | .falseJudgment => False
  trueCognition
    | .clearMoon | .trueJudgment => True
    | .twoMoons | .falseJudgment => False

theorem clear_moon_is_dharmakirti_candidate :
    twoMoonsModel.DharmakirtiCandidate .clearMoon := by
  simp [CognitionModel.DharmakirtiCandidate,
    CognitionModel.DignagaCandidate, twoMoonsModel]

theorem two_moons_is_nonconceptual_but_erroneous :
    twoMoonsModel.DignagaCandidate .twoMoons ∧
      twoMoonsModel.erroneous .twoMoons := by
  simp [CognitionModel.DignagaCandidate, twoMoonsModel]

theorem true_judgment_is_conceptual_but_true :
    twoMoonsModel.conceptual .trueJudgment ∧
      twoMoonsModel.Veridical .trueJudgment := by
  simp [CognitionModel.Veridical, twoMoonsModel]

theorem nonerror_does_not_entail_truth :
    ¬ twoMoonsModel.erroneous .falseJudgment ∧
      ¬ twoMoonsModel.Veridical .falseJudgment := by
  simp [CognitionModel.Veridical, twoMoonsModel]

theorem two_moons_is_not_dharmakirti_candidate :
    ¬ twoMoonsModel.DharmakirtiCandidate .twoMoons := by
  intro candidate
  exact candidate.2 (by simp [twoMoonsModel])

def twoMoonsRefinement : StrictRefinementCertificate twoMoonsModel where
  inclusion := fun _ candidate => candidate.1
  witness := .twoMoons
  dignagaCandidate := two_moons_is_nonconceptual_but_erroneous.1
  notDharmakirtiCandidate := two_moons_is_not_dharmakirti_candidate

/-- The named model makes strictness and finite inhabitation explicit. -/
theorem finite_strict_refinement_countermodel :
    Nonempty SampleCognition ∧
      (∀ cognition, twoMoonsModel.DharmakirtiCandidate cognition →
        twoMoonsModel.DignagaCandidate cognition) ∧
      ∃ cognition, twoMoonsModel.DignagaCandidate cognition ∧
        ¬ twoMoonsModel.DharmakirtiCandidate cognition := by
  exact ⟨⟨.clearMoon⟩, twoMoonsRefinement.proper_subset⟩

/-- A concrete operational model whose predicates do not mention either
perceptual candidate criterion.  Realization separately requires absence of
the profile's error flag, so an erroneous presentation is not automatically
reliable. -/
def sampleOperational :
    BuddhistComparativeLogic.Pramanavarttika.CognitionModel
      SampleCognition SampleCognition Unit where
  occurs _ := True
  novel _ := True
  presents cognition object := cognition = object
  realizes cognition object _ :=
    cognition = object ∧ ¬ twoMoonsModel.erroneous cognition

def sampleOperationalBridge :
    OperationalBridge twoMoonsModel SampleCognition Unit where
  operational := sampleOperational
  nonerroneousReliable := by
    intro cognition nonerroneous object presented
    exact ⟨(), presented, nonerroneous⟩

theorem clear_moon_is_operational_pramana :
    sampleOperational.Pramana .clearMoon := by
  apply sampleOperationalBridge.toPramana
    clear_moon_is_dharmakirti_candidate
  · trivial
  · trivial
  · exact ⟨.clearMoon, rfl⟩

theorem two_moons_is_not_operational_pramana :
    ¬ sampleOperational.Pramana .twoMoons := by
  intro certified
  obtain ⟨result, realized⟩ :=
    certified.2.2.2 (o := .twoMoons) rfl
  exact realized.2 (by simp [twoMoonsModel])

/-- The same finite model simultaneously witnesses the two requested
nonconflations and an inhabited positive operational certificate. -/
theorem finite_model_audit :
    twoMoonsModel.DignagaCandidate .twoMoons ∧
      twoMoonsModel.erroneous .twoMoons ∧
      twoMoonsModel.conceptual .trueJudgment ∧
      twoMoonsModel.Veridical .trueJudgment ∧
      sampleOperational.Pramana .clearMoon ∧
      ¬ sampleOperational.Pramana .twoMoons := by
  exact ⟨two_moons_is_nonconceptual_but_erroneous.1,
    two_moons_is_nonconceptual_but_erroneous.2,
    true_judgment_is_conceptual_but_true.1,
    true_judgment_is_conceptual_but_true.2,
    clear_moon_is_operational_pramana,
    two_moons_is_not_operational_pramana⟩

end BuddhistComparativeLogic.Pratyaksabhasa
