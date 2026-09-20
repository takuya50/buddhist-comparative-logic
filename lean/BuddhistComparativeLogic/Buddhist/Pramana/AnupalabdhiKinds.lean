/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis

/-!
# Eleven deployment forms of non-apprehension

*Nyāyabindu* 2.31–42 presents eleven applications of non-apprehension and then
gathers the ten indirect applications under non-apprehension of an own
nature.  This module reconstructs those *deployment shapes*: it is not a
critical edition, and it does not claim that the same eleven-item taxonomy is
used in Dharmakīrti's other works or by every commentator.

The reconstruction keeps four relations apart.  A causal link, an inclusion,
a necessary condition, and an incompatibility have different types.  Indexed
evidence for each deployment form compiles to one `NegationCertificate`.
The direct, effect, and pervader cases pass through the repository's existing
`Anupalabdhi`, `KaryaHetu`, `SvabhavaHetu`, and `PramanaSynthesis` interfaces.

Finite models record four indispensable qualifications.  Non-cognition of an
imperceptible item, absence of a blocked effect, absence of one among several
possible causes, and observation of a merely alleged rival do not establish
the requested negation.
-/

namespace BuddhistComparativeLogic.AnupalabdhiKinds

universe u v

/-! ## Observation and typed relations -/

/-- A locus-indexed observation model.  Visibility supports negative
inference; perception soundness supports the positive rival cases. -/
structure ObservationModel (Locus : Type u) (Property : Type v) where
  holds : Locus -> Property -> Prop
  perceived : Locus -> Property -> Prop
  perceptible : Locus -> Property -> Prop
  visibility : forall {locus property},
    holds locus property -> perceptible locus property ->
      perceived locus property
  perceptionSound : forall {locus property},
    perceived locus property -> holds locus property

namespace ObservationModel

variable {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)

/-- Fixing a property turns the observation model into the existing
Dharmakīrti non-apprehension interface without changing its locus type. -/
def asAnupalabdhi (property : Property) :
    BuddhistComparativeLogic.Dharmakirti.Anupalabdhi Locus where
  present := fun locus => model.holds locus property
  perceived := fun locus => model.perceived locus property
  perceptible := fun locus => model.perceptible locus property
  visibility := by
    intro locus present perceptible
    exact model.visibility present perceptible

end ObservationModel

/-- Production is deliberately distinct from extensional inclusion. -/
structure CausalLink {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (cause effect : Property) : Prop where
  produces : forall locus,
    model.holds locus cause -> model.holds locus effect

/-- A certified effect sign records both physical production from cause to
effect and the warranted inferential direction from observed effect back to
cause.  Keeping both fields prevents the word `effect` from being only a
constructor label, while avoiding the claim that the effect produces its
cause. -/
structure EffectSign {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (effect cause : Property) : Prop where
  production : CausalLink model cause effect
  indicates : forall locus,
    model.holds locus effect -> model.holds locus cause

theorem EffectSign.hasPhysicalProduction
    {Locus : Type u} {Property : Type v}
    {model : ObservationModel Locus Property}
    {effect cause : Property} (sign : EffectSign model effect cause) :
    CausalLink model cause effect :=
  sign.production

/-- A pervaded property entails its pervader at every locus. -/
structure InclusionLink {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (narrow broad : Property) : Prop where
  includes : forall locus,
    model.holds locus narrow -> model.holds locus broad

/-- The first property requires the second.  This field prevents absence of
one optional cause from being mistaken for absence of its possible effect. -/
structure NecessaryLink {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (dependent necessary : Property) : Prop where
  requires : forall locus,
    model.holds locus dependent -> model.holds locus necessary

/-- An oriented incompatibility certificate.  Symmetry, when intended, must
be supplied separately rather than being hidden in the definition. -/
structure Incompatibility {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (left right : Property) : Prop where
  excludes : forall locus,
    model.holds locus left -> Not (model.holds locus right)

/-! ## The qualified eleven-item classification -/

/-- Names follow the sequence of applications in *Nyāyabindu* 2.31–41.
The constructors label formal proof shapes, not claims about a unique later
commentarial classification. -/
inductive Kind where
  | svabhavaAnupalabdhi
  | karyaAnupalabdhi
  | vyapakaAnupalabdhi
  | svabhavaViruddhopalabdhi
  | viruddhaKaryopalabdhi
  | viruddhaVyaptopalabdhi
  | karyaViruddhopalabdhi
  | vyapakaViruddhopalabdhi
  | karanaAnupalabdhi
  | karanaViruddhopalabdhi
  | karanaViruddhaKaryopalabdhi
  deriving DecidableEq, Repr

def allKinds : List Kind :=
  [.svabhavaAnupalabdhi, .karyaAnupalabdhi,
    .vyapakaAnupalabdhi, .svabhavaViruddhopalabdhi,
    .viruddhaKaryopalabdhi, .viruddhaVyaptopalabdhi,
    .karyaViruddhopalabdhi, .vyapakaViruddhopalabdhi,
    .karanaAnupalabdhi, .karanaViruddhopalabdhi,
    .karanaViruddhaKaryopalabdhi]

theorem eleven_kinds_are_distinct_and_exhaustive :
    allKinds.length = 11 /\ allKinds.Nodup /\
      forall kind, kind ∈ allKinds := by
  constructor
  · decide
  constructor
  · decide
  · intro kind
    cases kind <;> decide

/-! ## A common certificate and adapters to the shared inference API -/

/-- A one-subject Dharmakīrti model whose thesis is the requested metalevel
negation.  Its pervasion field retains the proof rather than defining absence
as a syntactic complement. -/
def conclusionModel {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (locus : Locus) (target : Property) :
    BuddhistComparativeLogic.Dharmakirti.Model Unit where
  paksa := ()
  sadhya := fun _ => Not (model.holds locus target)
  reason := fun _ => True
  vyapti := Not (model.holds locus target)
  vyapti_iff := by
    constructor
    · intro absent _ _
      exact absent
    · intro pervasion
      exact pervasion () trivial

/-- Every deployment form returns the same auditable deductive interface. -/
structure NegationCertificate {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (locus : Locus) (target : Property) : Prop where
  deductive : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
    (conclusionModel model locus target)

namespace NegationCertificate

variable {Locus : Type u} {Property : Type v}
    {model : ObservationModel Locus Property}
    {locus : Locus} {target : Property}

theorem sound
    (certificate : NegationCertificate model locus target) :
    Not (model.holds locus target) :=
  BuddhistComparativeLogic.PramanaSynthesis.deductive_sound certificate.deductive

theorem ofProof (absent : Not (model.holds locus target)) :
    NegationCertificate model locus target where
  deductive := {
    subjectReason := trivial
    pervasion := absent
  }

/-- Adapter from the repository's perceptible non-apprehension certificate. -/
theorem ofAnupalabdhi
    (certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (BuddhistComparativeLogic.PramanaSynthesis.anupalabdhiModel
        (model.asAnupalabdhi target) locus)) :
    NegationCertificate model locus target :=
  ofProof (BuddhistComparativeLogic.PramanaSynthesis.deductive_sound certificate)

end NegationCertificate

/-- The effect-absence argument as an actual `KaryaHetu`.  Its causal law is
constructively converted to the contrapositive needed for negation. -/
def effectAbsenceKarya {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (target effect : Property) (link : CausalLink model target effect)
    (subject : Locus) : BuddhistComparativeLogic.Dharmakirti.KaryaHetu Locus where
  paksa := subject
  sadhya := fun locus => Not (model.holds locus target)
  reason := fun locus => Not (model.holds locus effect)
  causalLaw := True
  causal_law_iff := by
    constructor
    · intro _ locus effectAbsent targetPresent
      exact effectAbsent (link.produces locus targetPresent)
    · intro _
      trivial

/-- An observed effect sign as the repository's positive `KaryaHetu`
interface.  `EffectSign.production` certifies the physical direction, while
the `indicates` field supplies the inferential direction used here. -/
def effectSignKarya {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (effect cause : Property) (link : EffectSign model effect cause)
    (subject : Locus) : BuddhistComparativeLogic.Dharmakirti.KaryaHetu Locus where
  paksa := subject
  sadhya := fun locus => model.holds locus cause
  reason := fun locus => model.holds locus effect
  causalLaw := True
  causal_law_iff := by
    constructor
    · intro _
      exact link.indicates
    · intro _
      trivial

/-- The pervader-absence argument as an actual `SvabhavaHetu`. -/
def pervaderAbsenceSvabhava {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (target pervader : Property)
    (link : InclusionLink model target pervader)
    (subject : Locus) : BuddhistComparativeLogic.Dharmakirti.SvabhavaHetu Locus where
  paksa := subject
  sadhya := fun locus => Not (model.holds locus target)
  reason := fun locus => Not (model.holds locus pervader)
  vyapti := True
  vyapti_iff := by
    constructor
    · intro _ locus pervaderAbsent targetPresent
      exact pervaderAbsent (link.includes locus targetPresent)
    · intro _
      trivial
  inclusion := by
    intro locus pervaderAbsent targetPresent
    exact pervaderAbsent (link.includes locus targetPresent)

/-- A necessary-condition absence has the same inclusion proof shape, while
retaining a different input type from pervasion. -/
def necessaryAbsenceSvabhava {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (target necessary : Property)
    (link : NecessaryLink model target necessary)
    (subject : Locus) : BuddhistComparativeLogic.Dharmakirti.SvabhavaHetu Locus where
  paksa := subject
  sadhya := fun locus => Not (model.holds locus target)
  reason := fun locus => Not (model.holds locus necessary)
  vyapti := True
  vyapti_iff := by
    constructor
    · intro _ locus necessaryAbsent targetPresent
      exact necessaryAbsent (link.requires locus targetPresent)
    · intro _
      trivial
  inclusion := by
    intro locus necessaryAbsent targetPresent
    exact necessaryAbsent (link.requires locus targetPresent)

namespace NegationCertificate

variable {Locus : Type u} {Property : Type v}
    {model : ObservationModel Locus Property}
    {locus : Locus} {target effect pervader necessary : Property}

/-- Adapter from the causal-law certificate, after non-apprehension has
established absence of the effect sign. -/
theorem ofKarya
    (link : CausalLink model target effect)
    (certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (BuddhistComparativeLogic.PramanaSynthesis.karyaModel
        (effectAbsenceKarya model target effect link locus))) :
    NegationCertificate model locus target :=
  ofProof (BuddhistComparativeLogic.PramanaSynthesis.deductive_sound certificate)

/-- Adapter from predicate inclusion used by the pervader deployment. -/
theorem ofPervader
    (link : InclusionLink model target pervader)
    (certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (pervaderAbsenceSvabhava model target pervader link locus).toModel) :
    NegationCertificate model locus target :=
  ofProof (BuddhistComparativeLogic.PramanaSynthesis.deductive_sound certificate)

/-- Adapter from the explicitly typed necessary-condition deployment. -/
theorem ofNecessary
    (link : NecessaryLink model target necessary)
    (certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (necessaryAbsenceSvabhava model target necessary link locus).toModel) :
    NegationCertificate model locus target :=
  ofProof (BuddhistComparativeLogic.PramanaSynthesis.deductive_sound certificate)

end NegationCertificate

/-! ## Constructor-specific evidence and its total compiler -/

/-- Evidence is indexed by the deployment form.  Similar-looking constructors
therefore cannot exchange a causal proof for an inclusion or necessary-link
proof by definitional equality. -/
inductive Evidence {Locus : Type u} {Property : Type v}
    (model : ObservationModel Locus Property)
    (locus : Locus) (target : Property) : Kind -> Type (max u v) where
  | svabhavaAnupalabdhi
      (perceptible : model.perceptible locus target)
      (unperceived : Not (model.perceived locus target)) :
      Evidence model locus target .svabhavaAnupalabdhi
  | karyaAnupalabdhi
      (effect : Property) (link : CausalLink model target effect)
      (perceptible : model.perceptible locus effect)
      (unperceived : Not (model.perceived locus effect)) :
      Evidence model locus target .karyaAnupalabdhi
  | vyapakaAnupalabdhi
      (pervader : Property) (link : InclusionLink model target pervader)
      (perceptible : model.perceptible locus pervader)
      (unperceived : Not (model.perceived locus pervader)) :
      Evidence model locus target .vyapakaAnupalabdhi
  | svabhavaViruddhopalabdhi
      (rival : Property) (observed : model.perceived locus rival)
      (conflict : Incompatibility model rival target) :
      Evidence model locus target .svabhavaViruddhopalabdhi
  | viruddhaKaryopalabdhi
      (sign rival : Property) (observed : model.perceived locus sign)
      (effectSign : EffectSign model sign rival)
      (conflict : Incompatibility model rival target) :
      Evidence model locus target .viruddhaKaryopalabdhi
  | viruddhaVyaptopalabdhi
      (sign rival : Property) (observed : model.perceived locus sign)
      (pervasion : InclusionLink model sign rival)
      (conflict : Incompatibility model rival target) :
      Evidence model locus target .viruddhaVyaptopalabdhi
  | karyaViruddhopalabdhi
      (effect rival : Property) (observed : model.perceived locus rival)
      (production : CausalLink model target effect)
      (conflict : Incompatibility model rival effect) :
      Evidence model locus target .karyaViruddhopalabdhi
  | vyapakaViruddhopalabdhi
      (pervader rival : Property) (observed : model.perceived locus rival)
      (pervasion : InclusionLink model target pervader)
      (conflict : Incompatibility model rival pervader) :
      Evidence model locus target .vyapakaViruddhopalabdhi
  | karanaAnupalabdhi
      (cause : Property) (necessity : NecessaryLink model target cause)
      (perceptible : model.perceptible locus cause)
      (unperceived : Not (model.perceived locus cause)) :
      Evidence model locus target .karanaAnupalabdhi
  | karanaViruddhopalabdhi
      (cause rival : Property) (observed : model.perceived locus rival)
      (necessity : NecessaryLink model target cause)
      (conflict : Incompatibility model rival cause) :
      Evidence model locus target .karanaViruddhopalabdhi
  | karanaViruddhaKaryopalabdhi
      (cause rivalCause sign : Property)
      (observed : model.perceived locus sign)
      (necessity : NecessaryLink model target cause)
      (effectSign : EffectSign model sign rivalCause)
      (conflict : Incompatibility model rivalCause cause) :
      Evidence model locus target .karanaViruddhaKaryopalabdhi

/-- Every one of the eleven evidence forms compiles to the same explicit
subject-level negation certificate. -/
theorem compile {Locus : Type u} {Property : Type v}
    {model : ObservationModel Locus Property}
    {locus : Locus} {target : Property} {kind : Kind}
    (evidence : Evidence model locus target kind) :
    NegationCertificate model locus target := by
  cases evidence with
  | svabhavaAnupalabdhi perceptible unperceived =>
      exact NegationCertificate.ofAnupalabdhi
        (BuddhistComparativeLogic.PramanaSynthesis.ofAnupalabdhi
          (model.asAnupalabdhi target) locus perceptible unperceived)
  | karyaAnupalabdhi effect link perceptible unperceived =>
      have effectAbsent : Not (model.holds locus effect) :=
        BuddhistComparativeLogic.PramanaSynthesis.anupalabdhi_conclusion
          (model.asAnupalabdhi effect) locus perceptible unperceived
      exact NegationCertificate.ofKarya link
        (BuddhistComparativeLogic.PramanaSynthesis.ofKaryaHetu
          (effectAbsenceKarya model target effect link locus)
          trivial effectAbsent)
  | vyapakaAnupalabdhi pervader link perceptible unperceived =>
      have pervaderAbsent : Not (model.holds locus pervader) :=
        BuddhistComparativeLogic.PramanaSynthesis.anupalabdhi_conclusion
          (model.asAnupalabdhi pervader) locus perceptible unperceived
      exact NegationCertificate.ofPervader link
        (BuddhistComparativeLogic.PramanaSynthesis.ofSvabhavaHetu
          (pervaderAbsenceSvabhava model target pervader link locus)
          pervaderAbsent)
  | svabhavaViruddhopalabdhi rival observed conflict =>
      exact NegationCertificate.ofProof
        (conflict.excludes locus (model.perceptionSound observed))
  | viruddhaKaryopalabdhi sign rival observed effectSign conflict =>
      have signPresent := model.perceptionSound observed
      have rivalPresent : model.holds locus rival :=
        BuddhistComparativeLogic.PramanaSynthesis.deductive_sound
          (BuddhistComparativeLogic.PramanaSynthesis.ofKaryaHetu
            (effectSignKarya model sign rival effectSign locus)
            trivial signPresent)
      exact NegationCertificate.ofProof
        (conflict.excludes locus rivalPresent)
  | viruddhaVyaptopalabdhi sign rival observed pervasion conflict =>
      have signPresent := model.perceptionSound observed
      have rivalPresent := pervasion.includes locus signPresent
      exact NegationCertificate.ofProof
        (conflict.excludes locus rivalPresent)
  | karyaViruddhopalabdhi effect rival observed production conflict =>
      have rivalPresent := model.perceptionSound observed
      exact NegationCertificate.ofProof (by
        intro targetPresent
        exact conflict.excludes locus rivalPresent
          (production.produces locus targetPresent))
  | vyapakaViruddhopalabdhi pervader rival observed pervasion conflict =>
      have rivalPresent := model.perceptionSound observed
      exact NegationCertificate.ofProof (by
        intro targetPresent
        exact conflict.excludes locus rivalPresent
          (pervasion.includes locus targetPresent))
  | karanaAnupalabdhi cause necessity perceptible unperceived =>
      have causeAbsent : Not (model.holds locus cause) :=
        BuddhistComparativeLogic.PramanaSynthesis.anupalabdhi_conclusion
          (model.asAnupalabdhi cause) locus perceptible unperceived
      exact NegationCertificate.ofNecessary necessity
        (BuddhistComparativeLogic.PramanaSynthesis.ofSvabhavaHetu
          (necessaryAbsenceSvabhava model target cause necessity locus)
          causeAbsent)
  | karanaViruddhopalabdhi cause rival observed necessity conflict =>
      have rivalPresent := model.perceptionSound observed
      exact NegationCertificate.ofProof (by
        intro targetPresent
        exact conflict.excludes locus rivalPresent
          (necessity.requires locus targetPresent))
  | karanaViruddhaKaryopalabdhi cause rivalCause sign observed necessity
      effectSign conflict =>
      have signPresent := model.perceptionSound observed
      have rivalCausePresent : model.holds locus rivalCause :=
        BuddhistComparativeLogic.PramanaSynthesis.deductive_sound
          (BuddhistComparativeLogic.PramanaSynthesis.ofKaryaHetu
            (effectSignKarya model sign rivalCause effectSign locus)
            trivial signPresent)
      exact NegationCertificate.ofProof (by
        intro targetPresent
        exact conflict.excludes locus rivalCausePresent
          (necessity.requires locus targetPresent))

theorem compile_sound {Locus : Type u} {Property : Type v}
    {model : ObservationModel Locus Property}
    {locus : Locus} {target : Property} {kind : Kind}
    (evidence : Evidence model locus target kind) :
    Not (model.holds locus target) :=
  (compile evidence).sound

/-! ## Finite omission countermodels -/

inductive HiddenProperty where
  | jewel
  deriving DecidableEq, Repr

/-- A present jewel is hidden.  Visibility is satisfied vacuously because it
is not perceptible. -/
def hiddenModel : ObservationModel Unit HiddenProperty where
  holds := fun _ _ => True
  perceived := fun _ _ => False
  perceptible := fun _ _ => False
  visibility := by
    intro _ _ _ perceptible
    exact False.elim perceptible
  perceptionSound := by
    intro _ _ perceived
    exact False.elim perceived

theorem imperceptibility_omission_countermodel :
    hiddenModel.holds () .jewel /\
      Not (hiddenModel.perceived () .jewel) /\
      Not (hiddenModel.perceptible () .jewel) /\
      Not (Not (hiddenModel.perceived () .jewel) ->
        Not (hiddenModel.holds () .jewel)) := by
  refine ⟨trivial, by simp [hiddenModel], by simp [hiddenModel], ?_⟩
  intro shortcut
  exact shortcut (by simp [hiddenModel]) trivial

inductive BlockedProperty where
  | producingCause
  | expectedEffect
  deriving DecidableEq, Repr

/-- The cause is present while its normally expected effect is blocked. -/
def blockedEffectModel : ObservationModel Unit BlockedProperty where
  holds
    | _, .producingCause => True
    | _, .expectedEffect => False
  perceived
    | _, .producingCause => True
    | _, .expectedEffect => False
  perceptible := fun _ _ => True
  visibility := by
    intro locus property present _
    cases property <;> exact present
  perceptionSound := by
    intro locus property perceived
    cases property <;> exact perceived

theorem blocked_effect_omits_causal_link :
    blockedEffectModel.holds () .producingCause /\
      Not (blockedEffectModel.holds () .expectedEffect) /\
      Not (CausalLink blockedEffectModel
        .producingCause .expectedEffect) /\
      Not (Not (blockedEffectModel.holds () .expectedEffect) ->
        Not (blockedEffectModel.holds () .producingCause)) := by
  refine ⟨trivial, by simp [blockedEffectModel], ?_, ?_⟩
  · intro link
    exact link.produces () trivial
  · intro shortcut
    exact shortcut (by simp [blockedEffectModel]) trivial

inductive AlternativeProperty where
  | observedEffect
  | allegedCause
  | alternativeCause
  deriving DecidableEq, Repr

/-- The effect has an alternative source, so absence of the alleged cause is
compatible with presence of the effect. -/
def alternativeCauseModel : ObservationModel Unit AlternativeProperty where
  holds
    | _, .observedEffect => True
    | _, .allegedCause => False
    | _, .alternativeCause => True
  perceived
    | _, .observedEffect => True
    | _, .allegedCause => False
    | _, .alternativeCause => True
  perceptible := fun _ _ => True
  visibility := by
    intro locus property present _
    cases property <;> exact present
  perceptionSound := by
    intro locus property perceived
    cases property <;> exact perceived

theorem alternative_cause_omits_necessity :
    alternativeCauseModel.holds () .observedEffect /\
      Not (alternativeCauseModel.holds () .allegedCause) /\
      CausalLink alternativeCauseModel
        .alternativeCause .observedEffect /\
      Not (NecessaryLink alternativeCauseModel
        .observedEffect .allegedCause) /\
      Not (Not (alternativeCauseModel.holds () .allegedCause) ->
        Not (alternativeCauseModel.holds () .observedEffect)) := by
  refine ⟨trivial, by simp [alternativeCauseModel], ?_, ?_, ?_⟩
  · exact ⟨by
      intro locus present
      cases locus
      exact present⟩
  · intro link
    exact link.requires () trivial
  · intro shortcut
    exact shortcut (by simp [alternativeCauseModel]) trivial

inductive RivalProperty where
  | target
  | allegedRival
  deriving DecidableEq, Repr

/-- Both properties are perceived together; perception cannot manufacture an
unproved incompatibility premise. -/
def compatibleRivalsModel : ObservationModel Unit RivalProperty where
  holds := fun _ _ => True
  perceived := fun _ _ => True
  perceptible := fun _ _ => True
  visibility := by
    intro _ _ _ _
    trivial
  perceptionSound := by
    intro _ _ _
    trivial

theorem unproved_incompatibility_countermodel :
    compatibleRivalsModel.perceived () .target /\
      compatibleRivalsModel.perceived () .allegedRival /\
      Not (Incompatibility compatibleRivalsModel
        .allegedRival .target) /\
      Not (compatibleRivalsModel.perceived () .allegedRival ->
        Not (compatibleRivalsModel.holds () .target)) := by
  refine ⟨trivial, trivial, ?_, ?_⟩
  · intro conflict
    exact conflict.excludes () trivial trivial
  · intro shortcut
    exact shortcut trivial trivial

end BuddhistComparativeLogic.AnupalabdhiKinds
