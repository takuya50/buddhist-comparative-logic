/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis
import BuddhistComparativeLogic.Buddhist.Pramana.DirectedMomentariness

/-!
# Premise audit for momentariness inference

This module formalizes a restrained `sattvānumāna`-style argument: an
existent is causally efficacious, and the proposed thesis is numerical
momentariness.  The first equivalence follows from the explicit `efficacy`
field of `Momentariness.Theory`.  The second step is represented by an
explicit global pervasion premise; a rooted directed transport certificate is
one sufficient way to prove it.

The result is a proof-obligation analysis rather than a complete historical
formalization of any one work called a `Kṣaṇabhaṅgasiddhi`.  In particular,
causal nonuniformity is kept distinct from the statement that one numerical
object exists at exactly one time.  Finite countermodels show what happens
when rooted transport or uniqueness of an effect's production time is
omitted.
-/

namespace BuddhistComparativeLogic.Ksanabhangasiddhi

open BuddhistComparativeLogic.Momentariness

universe u v w

variable {D : Type u} {E : Type v} {T : Type w}

/-! ## Existence, efficacy and the numerical thesis -/

def ExistsSomewhere (M : Theory D E T) (d : D) : Prop :=
  ∃ t, M.existsAt d t

def EffectiveSomewhere (M : Theory D E T) (d : D) : Prop :=
  ∃ t, M.Efficacious d t

def CausalNonuniform (M : Theory D E T) (d : D) : Prop :=
  ¬ M.IntrinsicPower d

/-- `NumericallyMomentary` uses the identity criterion already encoded by
`Theory.Momentary`: all existence times of the same `d` equal one witness. -/
def NumericallyMomentary (M : Theory D E T) (d : D) : Prop :=
  M.Momentary d

theorem exists_somewhere_iff_effective_somewhere
    (M : Theory D E T) (d : D) :
    ExistsSomewhere M d ↔ EffectiveSomewhere M d := by
  constructor
  · rintro ⟨t, existsAt⟩
    exact ⟨t, (M.efficacious_iff_exists d t).mpr existsAt⟩
  · rintro ⟨t, effective⟩
    exact ⟨t, (M.efficacious_iff_exists d t).mp effective⟩

theorem numerical_momentariness_iff_unique_existence_time
    (M : Theory D E T) (d : D) :
    NumericallyMomentary M d ↔
      ∃ t, M.existsAt d t ∧ ∀ t', M.existsAt d t' → t' = t :=
  Iff.rfl

/-- The global bridge required by the `sattva` inference. -/
abbrev SattvaPervasion (M : Theory D E T) : Prop :=
  ∀ d, ExistsSomewhere M d → NumericallyMomentary M d

/-- The reason is existence and the thesis is numerical momentariness.  The
model's `vyapti` field is exactly the disputed global bridge. -/
def sattvaInference (M : Theory D E T) (subject : D) :
    BuddhistComparativeLogic.Dharmakirti.Model D where
  paksa := subject
  sadhya := NumericallyMomentary M
  reason := ExistsSomewhere M
  vyapti := SattvaPervasion M
  vyapti_iff := Iff.rfl

theorem sattva_reason_iff_causal_efficacy
    (M : Theory D E T) (subject d : D) :
    (sattvaInference M subject).reason d ↔ EffectiveSomewhere M d :=
  exists_somewhere_iff_effective_somewhere M d

theorem sattva_subject_reason (M : Theory D E T) {subject : D}
    (hexists : ExistsSomewhere M subject) :
    (sattvaInference M subject).toAnumana.paksadharmata :=
  hexists

theorem sattva_certificate_sound (M : Theory D E T) {subject : D}
    (certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (sattvaInference M subject)) :
    NumericallyMomentary M subject :=
  BuddhistComparativeLogic.PramanaSynthesis.deductive_sound certificate

/-! ## Rooted directed transport supplies the pervasion -/

/-- A root is selected for each existent, and every actual production can be
transported backwards along a directed chain to that root. -/
structure RootedTransport (M : Theory D E T)
    (C : BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion M) where
  root : D → T
  rootExists : ∀ {d}, ExistsSomewhere M d → M.existsAt d (root d)
  rooted : ∀ {d e t}, M.produces d e t →
    BuddhistComparativeLogic.DirectedMomentariness.DirectedChain C d (root d) t

theorem rooted_transport_makes_each_existent_momentary
    (M : Theory D E T)
    (C : BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion M)
    (bridge : RootedTransport M C) {d : D}
    (hexists : ExistsSomewhere M d) : NumericallyMomentary M d := by
  exact BuddhistComparativeLogic.DirectedMomentariness.momentary_of_rooted_directedChains
    C (bridge.rootExists hexists) (fun produced => bridge.rooted produced)

theorem rooted_transport_establishes_pervasion
    (M : Theory D E T)
    (C : BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion M)
    (bridge : RootedTransport M C) (subject : D) :
    (sattvaInference M subject).vyapti := by
  intro d hexists
  exact rooted_transport_makes_each_existent_momentary M C bridge hexists

/-- The subject's existence and the global directed bridge form the common
deductive certificate.  The existence field and pervasion field remain
separate proof terms. -/
theorem rooted_transport_certificate
    (M : Theory D E T)
    (C : BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion M)
    (bridge : RootedTransport M C) {subject : D}
    (hexists : ExistsSomewhere M subject) :
    BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate
      (sattvaInference M subject) where
  subjectReason := sattva_subject_reason M hexists
  pervasion := rooted_transport_establishes_pervasion M C bridge subject

theorem sattva_from_rooted_transport
    (M : Theory D E T)
    (C : BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion M)
    (bridge : RootedTransport M C) {subject : D}
    (hexists : ExistsSomewhere M subject) :
    NumericallyMomentary M subject :=
  sattva_certificate_sound M
    (rooted_transport_certificate M C bridge hexists)

/-! ## A local certificate and the older two-way criterion -/

/-- A subject-local version does not pretend to establish pervasion for every
object in the domain. -/
structure LocalSattvaCertificate (M : Theory D E T)
    (C : BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion M)
    (d : D) where
  root : T
  existsAtRoot : M.existsAt d root
  rooted : ∀ {e t}, M.produces d e t →
    BuddhistComparativeLogic.DirectedMomentariness.DirectedChain C d root t

theorem local_sattva_certificate_sound
    (M : Theory D E T)
    (C : BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion M)
    {d : D} (certificate : LocalSattvaCertificate M C d) :
    NumericallyMomentary M d := by
  exact BuddhistComparativeLogic.DirectedMomentariness.momentary_of_rooted_directedChains
    C certificate.existsAtRoot certificate.rooted

theorem two_way_rooted_transport_is_sufficient
    (M : Theory D E T) (C : M.ContinuityCriterion) {d : D} {root : T}
    (here : M.existsAt d root)
    (rooted : ∀ {e t}, M.produces d e t → M.CausalChain C d root t) :
    NumericallyMomentary M d :=
  BuddhistComparativeLogic.DirectedMomentariness.momentary_of_twoWay_rootedChains
    M C here rooted

/-! ## Finite countermodel: nonuniformity is weaker than momentariness -/

/-- The object exists at both Boolean times and produces a different Boolean
effect at each.  It is causally nonuniform, yet it is not numerically
momentary. -/
theorem finite_nonuniformity_is_not_momentariness :
    ExistsSomewhere BuddhistComparativeLogic.Momentariness.twoExistenceTimes () ∧
      EffectiveSomewhere BuddhistComparativeLogic.Momentariness.twoExistenceTimes () ∧
      CausalNonuniform BuddhistComparativeLogic.Momentariness.twoExistenceTimes () ∧
      ¬ NumericallyMomentary
        BuddhistComparativeLogic.Momentariness.twoExistenceTimes () := by
  have audit := BuddhistComparativeLogic.Momentariness.punctuality_is_needed_for_the_last_step
  have hexists : ExistsSomewhere
      BuddhistComparativeLogic.Momentariness.twoExistenceTimes () :=
    ⟨false, audit.1⟩
  exact ⟨hexists,
    (exists_somewhere_iff_effective_somewhere
      BuddhistComparativeLogic.Momentariness.twoExistenceTimes ()).mp hexists,
    audit.2.1, audit.2.2.2⟩

/-- In the same finite model, existence supplies the subject reason but does
not supply either the global pervasion or the subject thesis. -/
theorem finite_existence_omits_sattva_pervasion :
    (sattvaInference BuddhistComparativeLogic.Momentariness.twoExistenceTimes ()).toAnumana.paksadharmata ∧
      ¬ (sattvaInference
        BuddhistComparativeLogic.Momentariness.twoExistenceTimes ()).vyapti ∧
      ¬ (sattvaInference BuddhistComparativeLogic.Momentariness.twoExistenceTimes ()).sadhya
        (sattvaInference BuddhistComparativeLogic.Momentariness.twoExistenceTimes ()).paksa := by
  have audit := BuddhistComparativeLogic.Momentariness.punctuality_is_needed_for_the_last_step
  have hexists : ExistsSomewhere
      BuddhistComparativeLogic.Momentariness.twoExistenceTimes () := ⟨false, audit.1⟩
  have notMomentary : ¬ NumericallyMomentary
      BuddhistComparativeLogic.Momentariness.twoExistenceTimes () := audit.2.2.2
  refine ⟨hexists, ?_, notMomentary⟩
  intro pervasion
  exact notMomentary (pervasion () hexists)

/-- No directed criterion can meet the required rooted condition for this
two-time object.  Otherwise the existing directed theorem would contradict
the finite non-momentariness proof. -/
theorem finite_model_has_no_rooted_transport :
    ¬ ∃ (C : BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion
        BuddhistComparativeLogic.Momentariness.twoExistenceTimes) (root : Bool),
      BuddhistComparativeLogic.Momentariness.twoExistenceTimes.existsAt () root ∧
        (∀ {e t}, BuddhistComparativeLogic.Momentariness.twoExistenceTimes.produces () e t →
          BuddhistComparativeLogic.DirectedMomentariness.DirectedChain C () root t) := by
  rintro ⟨C, root, here, rooted⟩
  have momentary :=
    BuddhistComparativeLogic.DirectedMomentariness.momentary_of_rooted_directedChains
      C here rooted
  exact BuddhistComparativeLogic.Momentariness.punctuality_is_needed_for_the_last_step.2.2.2
    momentary

/-! ## Finite countermodel when effect-time uniqueness is omitted -/

/-- The causal interface before the unique-effect-time premise is added. -/
structure WeakTheory (D : Type u) (E : Type v) (T : Type w) where
  existsAt : D → T → Prop
  produces : D → E → T → Prop
  efficacy : ∀ d t, existsAt d t ↔ ∃ e, produces d e t

namespace WeakTheory

variable (M : WeakTheory D E T)

def Momentary (d : D) : Prop :=
  ∃ t, M.existsAt d t ∧ ∀ t', M.existsAt d t' → t' = t

abbrev UniqueEffectTime : Prop :=
  ∀ {d e t t'}, M.produces d e t → M.produces d e t' → t = t'

/-- This is the endpoint consequence delivered by rooted backward transport:
every actual effect can also be produced at the selected root. -/
def RootRecoverable (d : D) (root : T) : Prop :=
  ∀ {e t}, M.produces d e t → M.produces d e root

theorem momentary_of_unique_root_recovery {d : D} {root : T}
    (here : M.existsAt d root) (unique : M.UniqueEffectTime)
    (recover : M.RootRecoverable d root) : M.Momentary d := by
  refine ⟨root, here, ?_⟩
  intro t existsAt
  obtain ⟨e, produced⟩ := (M.efficacy d t).mp existsAt
  exact unique produced (recover produced)

end WeakTheory

/-- The sole object exists and produces the sole effect at both Boolean
times.  Root recovery and efficacy hold, but effect-time uniqueness fails. -/
def persistentWeak : WeakTheory Unit Unit Bool where
  existsAt _ _ := True
  produces _ _ _ := True
  efficacy _ _ := ⟨fun _ => ⟨(), trivial⟩, fun _ => trivial⟩

theorem finite_root_recovery_without_uniqueness_is_insufficient :
    persistentWeak.existsAt () false ∧
      persistentWeak.existsAt () true ∧
      persistentWeak.RootRecoverable () false ∧
      ¬ persistentWeak.UniqueEffectTime ∧
      ¬ persistentWeak.Momentary () := by
  refine ⟨trivial, trivial, ?_, ?_, ?_⟩
  · intro e t produced
    trivial
  · intro unique
    have impossible := unique (d := ()) (e := ()) (t := false) (t' := true)
      trivial trivial
    exact Bool.noConfusion impossible
  · rintro ⟨root, existsAt, onlyRoot⟩
    cases root
    · exact Bool.noConfusion (onlyRoot true trivial)
    · exact Bool.noConfusion (onlyRoot false trivial)

end BuddhistComparativeLogic.Ksanabhangasiddhi
