/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis

/-!
# Capacity and latent effects in satkāryavāda

This module gives a deliberately bounded reconstruction of one argument for
the Sāṃkhya doctrine commonly called *satkāryavāda*: an effect is produced
only where the cause has the corresponding capacity, and a further grounding
principle locates that capacity in the effect's latent presence in the cause.
Production, capacity, and latent presence remain three separate predicates.
Consequently the positive theorem exposes both bridges, while finite models
show that selective production or bare capacity does not supply latent
preexistence by itself.

The reconstruction is oriented by *Sāṃkhyakārikā* 9 and its traditional
arguments from selective production and causal power.  It does not formalize
the whole Sāṃkhya cosmology, identify a latent effect with a manifest token,
or establish the capacity-grounding premise from selection alone.

Historical orientation:

* https://plato.stanford.edu/archives/fall2022/entries/naturalism-india/
* https://iep.utm.edu/sankhya/
-/

namespace BuddhistComparativeLogic.Satkaryavada

universe u v

/-! ## Three independent causal predicates -/

/-- The causal vocabulary alone includes no law connecting its three
predicates.  `latentIn effect cause` is ordered oppositely from the two
cause-to-effect relations so that the claimed location remains explicit. -/
structure Model (Cause : Type u) (Effect : Type v) where
  produces : Cause -> Effect -> Prop
  capable : Cause -> Effect -> Prop
  latentIn : Effect -> Cause -> Prop

namespace Model

variable {Cause : Type u} {Effect : Type v}
    (model : Model Cause Effect)

/-- Every actual production uses a matching causal capacity. -/
def ProductionRespectsCapacity : Prop :=
  forall {cause effect}, model.produces cause effect ->
    model.capable cause effect

/-- The disputed bridge from a causal capacity to a latent effect.  It is
kept independent of both production and selectivity. -/
def CapacityGrounding : Prop :=
  forall {cause effect}, model.capable cause effect ->
    model.latentIn effect cause

/-- All effects actually produced by one cause were latent in that cause. -/
def ProductionPervasionAt (cause : Cause) : Prop :=
  forall effect, model.produces cause effect -> model.latentIn effect cause

/-- A cause is selective when it produces one effect and fails to produce a
distinct effect. -/
def SelectiveAt (cause : Cause) : Prop :=
  exists produced withheld,
    model.produces cause produced /\
      Not (model.produces cause withheld) /\ produced ≠ withheld

/-- The two explicit bridges compose to latent preexistence for every actual
effect of the selected cause. -/
theorem productionPervasionAt
    (capacity : model.ProductionRespectsCapacity)
    (grounding : model.CapacityGrounding) (cause : Cause) :
    model.ProductionPervasionAt cause := by
  intro effect produced
  exact grounding (capacity produced)

/-- Local form of the positive satkārya inference. -/
theorem latent_of_production {cause : Cause} {effect : Effect}
    (capacity : model.ProductionRespectsCapacity)
    (grounding : model.CapacityGrounding)
    (produced : model.produces cause effect) :
    model.latentIn effect cause :=
  grounding (capacity produced)

end Model

/-! ## An inspectable proof certificate and inference adapter -/

/-- The certificate records the local production and both global bridges.
Keeping the fields separate makes the capacity-grounding commitment visible
to assumption audits. -/
structure Certificate {Cause : Type u} {Effect : Type v}
    (model : Model Cause Effect) (cause : Cause) (effect : Effect) : Prop where
  produced : model.produces cause effect
  productionRespectsCapacity : model.ProductionRespectsCapacity
  capacityGrounding : model.CapacityGrounding

/-- Read production of an effect as the reason and its latent presence in the
selected cause as the thesis of an existing Dharmakīrti effect-reason model.
The `causalLaw` field is the derived production-to-latency pervasion. -/
def preexistenceKaryaHetu {Cause : Type u} {Effect : Type v}
    (model : Model Cause Effect) (cause : Cause) (subject : Effect) :
    BuddhistComparativeLogic.Dharmakirti.KaryaHetu Effect where
  paksa := subject
  sadhya := fun effect => model.latentIn effect cause
  reason := fun effect => model.produces cause effect
  causalLaw := model.ProductionPervasionAt cause
  causal_law_iff := Iff.rfl

namespace Certificate

variable {Cause : Type u} {Effect : Type v}
    {model : Model Cause Effect} {cause : Cause} {effect : Effect}

/-- Direct soundness of the three-field certificate. -/
theorem sound (certificate : Certificate model cause effect) :
    model.latentIn effect cause :=
  model.latent_of_production certificate.productionRespectsCapacity
    certificate.capacityGrounding certificate.produced

/-- Actual typed adapter to the repository-wide deductive certificate.  The
adapter composes the two causal bridges rather than replacing them with an
unexamined pervasion proof. -/
theorem toDeductiveCertificate
    (certificate : Certificate model cause effect) :
    BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (BuddhistComparativeLogic.PramanaSynthesis.karyaModel
        (preexistenceKaryaHetu model cause effect)) :=
  BuddhistComparativeLogic.PramanaSynthesis.ofKaryaHetu
    (preexistenceKaryaHetu model cause effect)
    (model.productionPervasionAt
      certificate.productionRespectsCapacity
      certificate.capacityGrounding cause)
    certificate.produced

/-- The common inference interface returns the same latent-presence thesis. -/
theorem sound_via_pramana
    (certificate : Certificate model cause effect) :
    model.latentIn effect cause := by
  exact BuddhistComparativeLogic.PramanaSynthesis.deductive_sound
    certificate.toDeductiveCertificate

end Certificate

/-! ## Finite positive instance -/

inductive SampleCause where
  | sesameSeed
  | sand
  deriving DecidableEq, Repr

inductive SampleEffect where
  | oil
  | sprout
  deriving DecidableEq, Repr

open SampleCause SampleEffect

def sampleCauses : List SampleCause := [.sesameSeed, .sand]

def sampleEffects : List SampleEffect := [.oil, .sprout]

theorem sampleCauses_complete (cause : SampleCause) :
    cause ∈ sampleCauses := by
  cases cause <;> decide

theorem sampleEffects_complete (effect : SampleEffect) :
    effect ∈ sampleEffects := by
  cases effect <;> decide

/-- A small positive instance: the sesame seed produces, is capable of, and
latently contains oil; all other pairs fail all three predicates. -/
def groundedOil : Model SampleCause SampleEffect where
  produces := fun cause effect =>
    cause = .sesameSeed /\ effect = .oil
  capable := fun cause effect =>
    cause = .sesameSeed /\ effect = .oil
  latentIn := fun effect cause =>
    cause = .sesameSeed /\ effect = .oil

theorem groundedOilCertificate :
    Certificate groundedOil .sesameSeed .oil := by
  refine {
    produced := ?_
    productionRespectsCapacity := ?_
    capacityGrounding := ?_
  }
  · exact ⟨rfl, rfl⟩
  · intro cause effect produced
    exact produced
  · intro cause effect capable
    exact capable

theorem grounded_oil_preexists :
    groundedOil.latentIn .oil .sesameSeed :=
  groundedOilCertificate.sound_via_pramana

/-! ## Finite countermodels -/

/-- Production remains selective and every production is backed by capacity,
but `latentIn` is empty.  This changes only the bridge disputed by the
positive proof. -/
def selectiveWithoutGrounding : Model SampleCause SampleEffect where
  produces := fun cause effect =>
    cause = .sesameSeed /\ effect = .oil
  capable := fun cause effect =>
    cause = .sesameSeed /\ effect = .oil
  latentIn := fun _effect _cause => False

theorem selectiveWithoutGrounding_respects_capacity :
    selectiveWithoutGrounding.ProductionRespectsCapacity := by
  intro cause effect produced
  exact produced

theorem sesame_production_is_selective :
    selectiveWithoutGrounding.SelectiveAt .sesameSeed := by
  exact ⟨.oil, .sprout, ⟨rfl, rfl⟩, by simp [selectiveWithoutGrounding],
    by decide⟩

theorem selective_model_is_inhabited_and_finite :
    Nonempty SampleCause /\ Nonempty SampleEffect /\
      (forall cause, cause ∈ sampleCauses) /\
      (forall effect, effect ∈ sampleEffects) :=
  ⟨⟨.sesameSeed⟩, ⟨.oil⟩, sampleCauses_complete,
    sampleEffects_complete⟩

/-- Selective production and a matching capacity still leave latent
preexistence false when capacity grounding is not supplied. -/
theorem selective_capacity_does_not_entail_latent_preexistence :
    selectiveWithoutGrounding.SelectiveAt .sesameSeed /\
      selectiveWithoutGrounding.ProductionRespectsCapacity /\
      selectiveWithoutGrounding.produces .sesameSeed .oil /\
      selectiveWithoutGrounding.capable .sesameSeed .oil /\
      Not (selectiveWithoutGrounding.latentIn .oil .sesameSeed) /\
      Not selectiveWithoutGrounding.CapacityGrounding := by
  refine ⟨sesame_production_is_selective,
    selectiveWithoutGrounding_respects_capacity, ⟨rfl, rfl⟩,
    ⟨rfl, rfl⟩, ?_, ?_⟩
  · simp [selectiveWithoutGrounding]
  · intro grounding
    exact grounding (cause := .sesameSeed) (effect := .oil) ⟨rfl, rfl⟩

/-- The failed implication is stated directly over the same inhabited finite
model: selection plus the production-capacity law cannot manufacture the
missing production-to-latency pervasion. -/
theorem selectivity_and_capacity_law_are_insufficient :
    Not (selectiveWithoutGrounding.SelectiveAt .sesameSeed ->
      selectiveWithoutGrounding.ProductionRespectsCapacity ->
      selectiveWithoutGrounding.ProductionPervasionAt .sesameSeed) := by
  intro claimed
  have pervasion := claimed sesame_production_is_selective
    selectiveWithoutGrounding_respects_capacity
  exact pervasion .oil ⟨rfl, rfl⟩

/-- A second finite boundary case isolates bare capacity: the sand is marked
capable of a sprout although nothing is produced and nothing is latent. -/
def bareCapacity : Model SampleCause SampleEffect where
  produces := fun _cause _effect => False
  capable := fun cause effect => cause = .sand /\ effect = .sprout
  latentIn := fun _effect _cause => False

theorem capability_alone_does_not_entail_latency :
    bareCapacity.capable .sand .sprout /\
      Not (bareCapacity.latentIn .sprout .sand) /\
      Not bareCapacity.CapacityGrounding := by
  refine ⟨⟨rfl, rfl⟩, by simp [bareCapacity], ?_⟩
  intro grounding
  exact grounding (cause := .sand) (effect := .sprout) ⟨rfl, rfl⟩

end BuddhistComparativeLogic.Satkaryavada
