/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Jaina.NayaDynamics
import BuddhistComparativeLogic.Buddhist.Abhidharma.Pudgala
import BuddhistComparativeLogic.Buddhist.Pramana.DirectedMomentariness

/-!
# Origination, decay, and duration in Jaina change

This module gives a typed transition semantics for the Jaina triad *utpāda*,
*vyaya*, and *dhrauvya*: a carrier is present at two successive times, an old
mode is lost, and a new mode is acquired.  A certificate keeps these facts
independent.  Finite countermodels then distinguish replacement without a
persisting carrier from duration without change of mode.

The formal target is the conjunction expressed in the traditional formula
that what is real is associated with origination, decay, and persistence,
commonly cited from *Tattvārthasūtra* 5.29 (5.30 in another recension).  The
model does not decide whether a historical Jaina substance is best read as a
modern bearer, make duration into absolute immutability, or derive the triad
from the sevenfold predication scheme.

Historical orientation:

* https://plato.stanford.edu/entries/jaina-philosophy/
* https://www.cambridge.org/core/journals/religious-studies/article/selfhood-persistence-and-immortality-in-jaina-philosophy/D25383354E1CE8C863B27F27E3CBD9D4
-/

namespace BuddhistComparativeLogic.JainaChange

universe u v w x

/-! ## A carrier with time-indexed modes -/

/-- Carrier existence, occurrence of a mode, and temporal succession are kept
independent.  In particular, `follows` does not itself assert persistence. -/
structure Model (Carrier : Type u) (Mode : Type v) (Time : Type w) where
  existsAt : Carrier -> Time -> Prop
  hasMode : Carrier -> Mode -> Time -> Prop
  follows : Time -> Time -> Prop

namespace Model

variable {Carrier : Type u} {Mode : Type v} {Time : Type w}
    (model : Model Carrier Mode Time)

/-- `dhrauvya`: the same carrier is admitted at both endpoints. -/
def Dhrauvya (carrier : Carrier) (earlier later : Time) : Prop :=
  model.existsAt carrier earlier /\ model.existsAt carrier later

/-- *Utpāda*: a selected mode is absent first and present later. -/
def Utpada (carrier : Carrier) (mode : Mode)
    (earlier later : Time) : Prop :=
  Not (model.hasMode carrier mode earlier) /\
    model.hasMode carrier mode later

/-- `vyaya`: a selected mode is present first and absent later. -/
def Vyaya (carrier : Carrier) (mode : Mode)
    (earlier later : Time) : Prop :=
  model.hasMode carrier mode earlier /\
    Not (model.hasMode carrier mode later)

/-- One transition realizes succession, duration, decay of the old mode, and
origination of the new mode. -/
def TriadicTransition (carrier : Carrier) (oldMode newMode : Mode)
    (earlier later : Time) : Prop :=
  model.follows earlier later /\
    model.Dhrauvya carrier earlier later /\
    model.Vyaya carrier oldMode earlier later /\
    model.Utpada carrier newMode earlier later

/-- Loss and acquisition in a triadic transition force the selected modes to
be distinct; distinctness is not hidden as an extra certificate field. -/
theorem oldMode_ne_newMode {carrier : Carrier} {oldMode newMode : Mode}
    {earlier later : Time}
    (transition : model.TriadicTransition carrier oldMode newMode
      earlier later) : oldMode ≠ newMode := by
  intro same
  subst newMode
  exact transition.2.2.2.1 transition.2.2.1.1

end Model

/-! ## Transition certificate -/

/-- An inspectable certificate for the three characteristics.  Each endpoint
fact is stored separately so replacement and stasis cannot satisfy it by
definition. -/
structure TriadCertificate {Carrier : Type u} {Mode : Type v}
    {Time : Type w} (model : Model Carrier Mode Time)
    (carrier : Carrier) (oldMode newMode : Mode)
    (earlier later : Time) : Prop where
  succession : model.follows earlier later
  carrierEarlier : model.existsAt carrier earlier
  carrierLater : model.existsAt carrier later
  oldEarlier : model.hasMode carrier oldMode earlier
  oldAbsentLater : Not (model.hasMode carrier oldMode later)
  newAbsentEarlier : Not (model.hasMode carrier newMode earlier)
  newLater : model.hasMode carrier newMode later

namespace TriadCertificate

variable {Carrier : Type u} {Mode : Type v} {Time : Type w}
    {model : Model Carrier Mode Time} {carrier : Carrier}
    {oldMode newMode : Mode} {earlier later : Time}

/-- The seven fields assemble into the positive transition theorem. -/
theorem sound
    (certificate : TriadCertificate model carrier oldMode newMode
      earlier later) :
    model.TriadicTransition carrier oldMode newMode earlier later :=
  ⟨certificate.succession,
    ⟨certificate.carrierEarlier, certificate.carrierLater⟩,
    ⟨certificate.oldEarlier, certificate.oldAbsentLater⟩,
    ⟨certificate.newAbsentEarlier, certificate.newLater⟩⟩

/-! ### Adapter to ordered naya observations -/

/-- The canonical positive-then-negative route used by the existing ordered
observation API.  The route by itself fixes only an observation profile; the
agreement theorem below supplies its interpretation through the certified
old-mode facts. -/
def nayaTrace
    (_certificate : TriadCertificate model carrier oldMode newMode
      earlier later) :
    List BuddhistComparativeLogic.Saptabhangi.Respect3 :=
  BuddhistComparativeLogic.Saptabhangi.Dynamics.route .B3

/-- Semantic agreement between the two observed respects and one old-mode
predicate at the two endpoints.  Both equivalences concern the same trace,
carrier, and mode. -/
def OldModeTraceAgreement
    (certificate : TriadCertificate model carrier oldMode newMode
      earlier later) : Prop :=
  (BuddhistComparativeLogic.Saptabhangi.Dynamics.Seen .positive certificate.nayaTrace <->
      model.hasMode carrier oldMode earlier) /\
    (BuddhistComparativeLogic.Saptabhangi.Dynamics.Seen .negative certificate.nayaTrace <->
      Not (model.hasMode carrier oldMode later))

/-- The canonical route contains both required respects, while the
certificate supplies their endpoint interpretation for the old mode. -/
theorem oldModeTraceAgreement
    (certificate : TriadCertificate model carrier oldMode newMode
      earlier later) : certificate.OldModeTraceAgreement := by
  have seesPositive :
      BuddhistComparativeLogic.Saptabhangi.Dynamics.Seen
        .positive certificate.nayaTrace := by
    simp [nayaTrace, BuddhistComparativeLogic.Saptabhangi.Dynamics.Seen,
      BuddhistComparativeLogic.Saptabhangi.Dynamics.route]
  have seesNegative :
      BuddhistComparativeLogic.Saptabhangi.Dynamics.Seen
        .negative certificate.nayaTrace := by
    simp [nayaTrace, BuddhistComparativeLogic.Saptabhangi.Dynamics.Seen,
      BuddhistComparativeLogic.Saptabhangi.Dynamics.route]
  exact ⟨⟨fun _seen => certificate.oldEarlier,
      fun _oldEarlier => seesPositive⟩,
    ⟨fun _seen => certificate.oldAbsentLater,
      fun _oldAbsentLater => seesNegative⟩⟩

theorem nayaTrace_exactly_licenses_positive_and_negative
    (certificate : TriadCertificate model carrier oldMode newMode
      earlier later) :
    certificate.OldModeTraceAgreement /\
      BuddhistComparativeLogic.Saptabhangi.Dynamics.ExactlyLicenses
        certificate.nayaTrace .B3 := by
  refine ⟨certificate.oldModeTraceAgreement, ?_⟩
  simpa [nayaTrace] using
    (BuddhistComparativeLogic.Saptabhangi.Dynamics.every_mode_has_an_exact_route .B3)

/-- Monotone naya support is projected from exact licensing only after the
same adapter theorem has supplied old-mode trace agreement. -/
theorem toNayaSupport
    (certificate : TriadCertificate model carrier oldMode newMode
      earlier later) :
    BuddhistComparativeLogic.Saptabhangi.Dynamics.Supports certificate.nayaTrace .B3 :=
  BuddhistComparativeLogic.Saptabhangi.Dynamics.exactlyLicenses_implies_supports
    certificate.nayaTrace_exactly_licenses_positive_and_negative.2

/-! ### Boundary against directed momentariness -/

/-- Transfer of carrier existence into an existing causal theory. -/
def TracksCausalExistence
    (_certificate : TriadCertificate model carrier oldMode newMode
      earlier later)
    (causal : BuddhistComparativeLogic.Momentariness.Theory Carrier Effect Time) : Prop :=
  forall time, model.existsAt carrier time ->
    causal.existsAt carrier time

/-- Two-time duration rules out literal momentariness of the same carrier in
any causal theory that tracks the certificate's existence facts. -/
theorem excludes_momentary_carrier
    (certificate : TriadCertificate model carrier oldMode newMode
      earlier later)
    (distinctTimes : earlier ≠ later)
    (causal : BuddhistComparativeLogic.Momentariness.Theory Carrier Effect Time)
    (tracks : certificate.TracksCausalExistence causal) :
    Not (causal.Momentary carrier) := by
  rintro ⟨onlyTime, _existsOnly, unique⟩
  have earlierAt : causal.existsAt carrier earlier :=
    tracks earlier certificate.carrierEarlier
  have laterAt : causal.existsAt carrier later :=
    tracks later certificate.carrierLater
  exact distinctTimes ((unique earlier earlierAt).trans
    (unique later laterAt).symm)

/-- Actual adapter to `DirectedMomentariness`: rooted directed transport would
derive a momentary carrier, contradicting the certified two-time duration.
The theorem pinpoints the incompatible assumptions without declaring either
historical account true by definition. -/
theorem incompatible_with_rooted_directed_momentariness
    (certificate : TriadCertificate model carrier oldMode newMode
      earlier later)
    (distinctTimes : earlier ≠ later)
    (causal : BuddhistComparativeLogic.Momentariness.Theory Carrier Effect Time)
    (criterion :
      BuddhistComparativeLogic.DirectedMomentariness.DirectedCriterion causal)
    (root : Time) (here : causal.existsAt carrier root)
    (rooted : forall {effect time}, causal.produces carrier effect time ->
      BuddhistComparativeLogic.DirectedMomentariness.DirectedChain
        criterion carrier root time)
    (tracks : certificate.TracksCausalExistence causal) : False := by
  have momentary : causal.Momentary carrier :=
    BuddhistComparativeLogic.DirectedMomentariness.momentary_of_rooted_directedChains
      criterion here rooted
  exact certificate.excludes_momentary_carrier distinctTimes causal tracks
    momentary

end TriadCertificate

/-! ## A finite positive instance -/

inductive DemoCarrier where
  | clay
  deriving DecidableEq, Repr

inductive DemoMode where
  | lump
  | pot
  deriving DecidableEq, Repr

inductive DemoTime where
  | earlier
  | later
  deriving DecidableEq, Repr

open DemoCarrier DemoMode DemoTime

/-- The clay persists while the lump mode is lost and the pot mode arises. -/
def clayChange : Model DemoCarrier DemoMode DemoTime where
  existsAt := fun carrier _time => carrier = .clay
  hasMode := fun carrier mode time =>
    carrier = .clay /\
      ((mode = .lump /\ time = .earlier) \/
        (mode = .pot /\ time = .later))
  follows := fun first second => first = .earlier /\ second = .later

theorem clayChangeCertificate :
    TriadCertificate clayChange .clay .lump .pot .earlier .later := by
  refine {
    succession := ⟨rfl, rfl⟩
    carrierEarlier := rfl
    carrierLater := rfl
    oldEarlier := ?_
    oldAbsentLater := ?_
    newAbsentEarlier := ?_
    newLater := ?_
  }
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · simp [clayChange]
  · simp [clayChange]
  · exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩

theorem clay_change_realizes_origination_decay_duration :
    clayChange.TriadicTransition .clay .lump .pot .earlier .later :=
  clayChangeCertificate.sound

theorem positive_model_is_inhabited_and_nontrivial :
    Nonempty DemoCarrier /\ Nonempty DemoMode /\ Nonempty DemoTime /\
      DemoTime.earlier ≠ DemoTime.later :=
  ⟨⟨.clay⟩, ⟨.lump⟩, ⟨.earlier⟩, by decide⟩

/-! ## Adapter from aggregate streams -/

/-- Regard a five-aggregate stream as the modal profile of one conventional
carrier.  The unit carrier exists at every admitted time; individual
aggregates are its Boolean modes. -/
def ofAggregateStream {Time : Type w}
    (stream : BuddhistComparativeLogic.Pudgala.AggregateStream Time) :
    Model Unit BuddhistComparativeLogic.Skandha Time where
  existsAt := fun _carrier _time => True
  hasMode := fun _carrier aggregate time =>
    stream.present time aggregate = true
  follows := stream.follows

/-- A changing aggregate step gives a witnessed acquisition or loss while
the conventional unit carrier endures.  A single changed Boolean coordinate
need not provide both halves of the triad. -/
theorem aggregateChangingStep_gives_modal_change
    {Time : Type w} (stream : BuddhistComparativeLogic.Pudgala.AggregateStream Time)
    {earlier later : Time} (step : stream.ChangingStep earlier later) :
    exists aggregate,
      (ofAggregateStream stream).follows earlier later /\
      (ofAggregateStream stream).Dhrauvya () earlier later /\
      ((ofAggregateStream stream).Utpada () aggregate earlier later \/
        (ofAggregateStream stream).Vyaya () aggregate earlier later) := by
  obtain ⟨succession, aggregate, changed⟩ := step
  refine ⟨aggregate, succession, ⟨trivial, trivial⟩, ?_⟩
  cases before : stream.present earlier aggregate <;>
    cases after : stream.present later aggregate <;>
      simp [ofAggregateStream, Model.Utpada, Model.Vyaya,
        before, after] at changed ⊢

/-- With separate old-loss and new-acquisition witnesses, an aggregate stream
produces the full transition certificate used above. -/
theorem aggregateStream_to_triadCertificate
    {Time : Type w} (stream : BuddhistComparativeLogic.Pudgala.AggregateStream Time)
    {earlier later : Time} {oldMode newMode : BuddhistComparativeLogic.Skandha}
    (succession : stream.follows earlier later)
    (oldEarlier : stream.present earlier oldMode = true)
    (oldLater : stream.present later oldMode = false)
    (newEarlier : stream.present earlier newMode = false)
    (newLater : stream.present later newMode = true) :
    TriadCertificate (ofAggregateStream stream) () oldMode newMode
      earlier later := by
  refine {
    succession := succession
    carrierEarlier := trivial
    carrierLater := trivial
    oldEarlier := ?_
    oldAbsentLater := ?_
    newAbsentEarlier := ?_
    newLater := ?_
  }
  · exact oldEarlier
  · simp [ofAggregateStream, oldLater]
  · simp [ofAggregateStream, newEarlier]
  · exact newLater

/-! ## Finite countermodel: replacement without duration -/

inductive ReplacementCarrier where
  | lumpToken
  | potToken
  deriving DecidableEq, Repr

open ReplacementCarrier

/-- The earlier lump and later pot belong to distinct carrier tokens. -/
def replacement : Model ReplacementCarrier DemoMode DemoTime where
  existsAt := fun carrier time =>
    (carrier = .lumpToken /\ time = .earlier) \/
      (carrier = .potToken /\ time = .later)
  hasMode := fun carrier mode time =>
    (carrier = .lumpToken /\ mode = .lump /\ time = .earlier) \/
      (carrier = .potToken /\ mode = .pot /\ time = .later)
  follows := fun first second => first = .earlier /\ second = .later

/-- Mode succession across two replacement tokens is nonvacuous, but no
carrier occurs at both endpoints. -/
theorem replacement_without_duration :
    replacement.follows .earlier .later /\
      replacement.hasMode .lumpToken .lump .earlier /\
      replacement.hasMode .potToken .pot .later /\
      Not (exists carrier,
        replacement.Dhrauvya carrier .earlier .later) /\
      Not (exists carrier oldMode newMode,
        replacement.TriadicTransition carrier oldMode newMode
          .earlier .later) := by
  have noDuration : Not (exists carrier,
      replacement.Dhrauvya carrier .earlier .later) := by
    rintro ⟨carrier, duration⟩
    cases carrier <;> simp [Model.Dhrauvya, replacement] at duration
  refine ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩,
    Or.inr ⟨rfl, rfl, rfl⟩, noDuration, ?_⟩
  · rintro ⟨carrier, oldMode, newMode, transition⟩
    exact noDuration ⟨carrier, transition.2.1⟩

theorem replacement_model_is_inhabited_and_finite :
    Nonempty ReplacementCarrier /\
      (forall carrier,
        carrier = ReplacementCarrier.lumpToken \/
          carrier = ReplacementCarrier.potToken) := by
  refine ⟨⟨.lumpToken⟩, ?_⟩
  intro carrier
  cases carrier <;> simp

/-! ## Finite countermodel: duration without modal change -/

/-- The unit carrier persists and remains in the lump mode at both times. -/
def stableDuration : Model Unit DemoMode DemoTime where
  existsAt := fun _carrier _time => True
  hasMode := fun _carrier mode _time => mode = .lump
  follows := fun first second => first = .earlier /\ second = .later

theorem duration_without_modal_change :
    stableDuration.Dhrauvya () .earlier .later /\
      stableDuration.hasMode () .lump .earlier /\
      stableDuration.hasMode () .lump .later /\
      Not (exists oldMode newMode,
        stableDuration.TriadicTransition () oldMode newMode
          .earlier .later) := by
  refine ⟨⟨trivial, trivial⟩, rfl, rfl, ?_⟩
  rintro ⟨oldMode, newMode, transition⟩
  cases oldMode <;>
    simp [Model.TriadicTransition, Model.Vyaya, stableDuration] at transition

end BuddhistComparativeLogic.JainaChange
