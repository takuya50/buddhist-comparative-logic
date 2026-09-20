/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.SvatantraPrasanga

/-!
# Semantic proof and procedural result in a small debate audit

This module gives a deliberately small formal interface inspired by
Dharmakirti's *Vadanyaya*.  It is not a complete transcription of that work,
its historical list of defeat conditions, or any later debate manual.  The
model isolates a few auditable distinctions: proponent and opponent have
asymmetric procedural obligations; an allegation may identify a real fault
or merely a pseudo-fault; and thesis truth, semantic proof, public acceptance,
and procedural result remain separate layers.

The outcome checker consumes only a finite record of publicly visible moves.
It does not contain a proof of the thesis, and no certificate stores its own
conclusion or victory as a field.  The positive semantic bridge instead
reuses the existing Nyaya and `PramanaSynthesis` proof interfaces.  Concrete
finite cases show both that a correct inference can lose procedurally and
that procedural loss does not make its thesis false.
-/

namespace BuddhistComparativeLogic.Vadanyaya

open BuddhistComparativeLogic.Hetucakra

/-! ## Asymmetric roles and fault assessment -/

inductive Role where
  | proponent
  | opponent
  deriving DecidableEq, Repr

/-- A small selection of procedural faults.  The first three concern the
presenter's burden; the final two concern the respondent's burden. -/
inductive Fault where
  | omittedReason
  | omittedPervasion
  | unansweredChallenge
  | unsupportedCharge
  | withheldReply
  deriving DecidableEq, Repr

/-- Public facts relevant to one completed or suspended exchange.  These are
independent Boolean observations, so no result is smuggled into the record. -/
structure RoundRecord where
  reasonPresented : Bool
  pervasionPresented : Bool
  challengeIssued : Bool
  challengeAnswered : Bool
  chargeSupported : Bool
  opponentResponded : Bool
  opponentConceded : Bool
  deriving DecidableEq, Repr

/-- Which role can bear which type of fault. -/
def properTarget : Role → Fault → Bool
  | .proponent, .omittedReason => true
  | .proponent, .omittedPervasion => true
  | .proponent, .unansweredChallenge => true
  | .opponent, .unsupportedCharge => true
  | .opponent, .withheldReply => true
  | _, _ => false

/-- Whether the publicly recorded conditions for a fault occurred. -/
def occurred (record : RoundRecord) : Fault → Bool
  | .omittedReason => !record.reasonPresented
  | .omittedPervasion => !record.pervasionPresented
  | .unansweredChallenge => record.challengeIssued && !record.challengeAnswered
  | .unsupportedCharge => record.challengeIssued && !record.chargeSupported
  | .withheldReply =>
      record.challengeAnswered &&
        !record.opponentResponded && !record.opponentConceded

structure Charge where
  target : Role
  alleged : Fault
  deriving DecidableEq, Repr

/-- A charge is real exactly when its kind belongs to the charged role and
the relevant public condition occurred. -/
def isRealFault (record : RoundRecord) (charge : Charge) : Bool :=
  properTarget charge.target charge.alleged && occurred record charge.alleged

inductive FaultStatus where
  | real
  | pseudo
  deriving DecidableEq, Repr

/-- Executable classification of an allegation. -/
def classifyFault (record : RoundRecord) (charge : Charge) : FaultStatus :=
  if isRealFault record charge then .real else .pseudo

theorem classifyFault_real_iff (record : RoundRecord) (charge : Charge) :
    classifyFault record charge = .real ↔
      isRealFault record charge = true := by
  unfold classifyFault
  cases isRealFault record charge <;> simp

theorem classifyFault_pseudo_iff (record : RoundRecord) (charge : Charge) :
    classifyFault record charge = .pseudo ↔
      isRealFault record charge = false := by
  unfold classifyFault
  cases isRealFault record charge <;> simp

theorem fault_status_complete (record : RoundRecord) (charge : Charge) :
    classifyFault record charge = .real ∨
      classifyFault record charge = .pseudo := by
  cases classifyFault record charge <;> simp

theorem fault_status_exclusive (record : RoundRecord) (charge : Charge) :
    ¬ (classifyFault record charge = .real ∧
      classifyFault record charge = .pseudo) := by
  rintro ⟨real, pseudo⟩
  rw [real] at pseudo
  exact FaultStatus.noConfusion pseudo

/-- The modeled burdens are role-asymmetric rather than a single undirected
error predicate. -/
theorem role_obligations_are_asymmetric :
    properTarget .proponent .omittedReason = true ∧
      properTarget .opponent .omittedReason = false ∧
      properTarget .opponent .unsupportedCharge = true ∧
      properTarget .proponent .unsupportedCharge = false := by
  decide

def allFaults : List Fault :=
  [.omittedReason, .omittedPervasion, .unansweredChallenge,
    .unsupportedCharge, .withheldReply]

/-- The finite scan for a real fault attributed to one role. -/
def hasRealFault (record : RoundRecord) (role : Role) : Bool :=
  allFaults.any fun fault =>
    isRealFault record { target := role, alleged := fault }

/-! ## A finite procedural result -/

inductive Outcome where
  | proponentWon
  | proponentLost
  | undecided
  deriving DecidableEq, Repr

/-- If both roles incur a fault in this small simultaneous record, the
proponent's unmet burden has priority.  Otherwise opponent fault or explicit
concession yields proponent victory; a clean unresolved exchange is
undecided. -/
def outcome (record : RoundRecord) : Outcome :=
  if hasRealFault record .proponent then
    .proponentLost
  else if hasRealFault record .opponent || record.opponentConceded then
    .proponentWon
  else
    .undecided

def Won (record : RoundRecord) : Prop :=
  outcome record = .proponentWon

def Lost (record : RoundRecord) : Prop :=
  outcome record = .proponentLost

def Undecided (record : RoundRecord) : Prop :=
  outcome record = .undecided

/-- The executable outcome covers all three modeled procedural results. -/
theorem outcome_complete (record : RoundRecord) :
    Won record ∨ Lost record ∨ Undecided record := by
  cases result : outcome record <;>
    simp [Won, Lost, Undecided, result]

/-- Two readings of the same deterministic checker cannot disagree. -/
theorem outcome_unique (record : RoundRecord) {first second : Outcome}
    (firstResult : outcome record = first)
    (secondResult : outcome record = second) : first = second :=
  firstResult.symm.trans secondResult

theorem outcomes_pairwise_exclusive (record : RoundRecord) :
    ¬ (Won record ∧ Lost record) ∧
      ¬ (Won record ∧ Undecided record) ∧
      ¬ (Lost record ∧ Undecided record) := by
  constructor
  · rintro ⟨won, lost⟩
    unfold Won at won
    unfold Lost at lost
    rw [won] at lost
    exact Outcome.noConfusion lost
  constructor
  · rintro ⟨won, undecided⟩
    unfold Won at won
    unfold Undecided at undecided
    rw [won] at undecided
    exact Outcome.noConfusion undecided
  · rintro ⟨lost, undecided⟩
    unfold Lost at lost
    unfold Undecided at undecided
    rw [lost] at undecided
    exact Outcome.noConfusion undecided

/-- `outcome` is a total decision procedure, expressed as uniqueness of the
returned constructor. -/
theorem outcome_determined (record : RoundRecord) :
    ∃ result : Outcome, outcome record = result ∧
      ∀ other, outcome record = other → result = other := by
  exact ⟨outcome record, rfl, fun _ equality => equality⟩

instance outcomeDecidable (record : RoundRecord) (result : Outcome) :
    Decidable (outcome record = result) := inferInstance

instance wonDecidable (record : RoundRecord) : Decidable (Won record) := by
  unfold Won
  infer_instance

instance lostDecidable (record : RoundRecord) : Decidable (Lost record) := by
  unfold Lost
  infer_instance

instance undecidedDecidable (record : RoundRecord) :
    Decidable (Undecided record) := by
  unfold Undecided
  infer_instance

/-! ## Truth, proof, public acceptance, and result remain distinct -/

def ThesisTrue {L : Type u} (argument : Anumana L) : Prop :=
  argument.sadhya argument.paksa

/-- Semantic correctness uses the existing Nyaya certificate, whose fields
are the reason at the subject and a separately supplied pervasion. -/
abbrev SemanticProof {L : Type u} (argument : Anumana L) :=
  BuddhistComparativeLogic.Nyaya.SemanticProof argument

theorem semantic_proof_is_truth {L : Type u} {argument : Anumana L}
    (proof : SemanticProof argument) : ThesisTrue argument :=
  proof.sound

/-- The common pramana certificate reaches the same truth layer without
mentioning a procedural result. -/
theorem synthesized_certificate_is_truth {L : Type u}
    {model : BuddhistComparativeLogic.Dharmakirti.Model L}
    (certificate : BuddhistComparativeLogic.PramanaSynthesis.DeductiveCertificate model) :
    ThesisTrue model.toAnumana :=
  BuddhistComparativeLogic.PramanaSynthesis.deductive_sound certificate

/-- Public acceptance is read from the existing asymmetric Tibetan debate
ledger.  It is a commitment condition, not semantic truth. -/
def PubliclyAcceptable {L : Type u} (argument : Anumana L)
    (state : BuddhistComparativeLogic.TibetanDebate.State
      (BuddhistComparativeLogic.SvatantraPrasanga.InferenceClaim argument)) : Prop :=
  BuddhistComparativeLogic.TibetanDebate.LegalReply state
    (BuddhistComparativeLogic.SvatantraPrasanga.challenge argument) .accept

/-- Reuse the existing finite smoke/fire state to exhibit a sound argument
whose pervasion is not publicly accepted. -/
theorem semantic_proof_does_not_force_public_acceptance :
    SemanticProof BuddhistComparativeLogic.Nyaya.smokeFire ∧
      ThesisTrue BuddhistComparativeLogic.Nyaya.smokeFire ∧
      ¬ PubliclyAcceptable BuddhistComparativeLogic.Nyaya.smokeFire
        BuddhistComparativeLogic.SvatantraPrasanga.reasonOnlySmokeState := by
  exact ⟨BuddhistComparativeLogic.SvatantraPrasanga.smokeFireCertificate.semantic,
    BuddhistComparativeLogic.Nyaya.smokeFireFive.sound,
    BuddhistComparativeLogic.SvatantraPrasanga.semantic_soundness_does_not_force_dialectical_acceptance.2.2.2⟩

/-! ## Concrete finite outcomes and independence countermodels -/

/-- The proponent omits the public reason although the other recorded duties
are met. -/
def omittedReasonRound : RoundRecord where
  reasonPresented := false
  pervasionPresented := true
  challengeIssued := true
  challengeAnswered := true
  chargeSupported := true
  opponentResponded := true
  opponentConceded := false

def concededRound : RoundRecord where
  reasonPresented := true
  pervasionPresented := true
  challengeIssued := true
  challengeAnswered := true
  chargeSupported := true
  opponentResponded := true
  opponentConceded := true

def unresolvedRound : RoundRecord where
  reasonPresented := true
  pervasionPresented := true
  challengeIssued := true
  challengeAnswered := true
  chargeSupported := true
  opponentResponded := true
  opponentConceded := false

theorem real_and_pseudo_faults_nonvacuous :
    classifyFault omittedReasonRound
        { target := .proponent, alleged := .omittedReason } = .real ∧
      classifyFault omittedReasonRound
        { target := .opponent, alleged := .omittedReason } = .pseudo := by
  decide

theorem all_three_outcomes_are_inhabited :
    Lost omittedReasonRound ∧ Won concededRound ∧ Undecided unresolvedRound := by
  decide

/-- `Place` has three constructors and the argument has positive and negative
instances.  Its semantic proof is correct, yet omission in the independent
procedural record makes the proponent lose rather than win. -/
theorem correct_argument_need_not_win_procedurally :
    SemanticProof BuddhistComparativeLogic.Nyaya.smokeFire ∧
      ThesisTrue BuddhistComparativeLogic.Nyaya.smokeFire ∧
      (∃ place, BuddhistComparativeLogic.Nyaya.smokeFire.reason place ∧
        BuddhistComparativeLogic.Nyaya.smokeFire.sadhya place) ∧
      (∃ place, ¬ BuddhistComparativeLogic.Nyaya.smokeFire.reason place ∧
        ¬ BuddhistComparativeLogic.Nyaya.smokeFire.sadhya place) ∧
      Lost omittedReasonRound ∧ ¬ Won omittedReasonRound := by
  exact ⟨BuddhistComparativeLogic.SvatantraPrasanga.smokeFireCertificate.semantic,
    BuddhistComparativeLogic.Nyaya.smokeFireFive.sound,
    BuddhistComparativeLogic.Nyaya.smokeFire_nonvacuous.2.1,
    BuddhistComparativeLogic.Nyaya.smokeFire_nonvacuous.2.2, by decide, by decide⟩

/-- The same true finite smoke/fire thesis refutes the invalid transfer from
procedural defeat to semantic falsity. -/
theorem procedural_loss_does_not_entail_false_thesis :
    Lost omittedReasonRound ∧
      ThesisTrue BuddhistComparativeLogic.Nyaya.smokeFire ∧
      ¬ (Lost omittedReasonRound →
        ¬ ThesisTrue BuddhistComparativeLogic.Nyaya.smokeFire) := by
  have lost : Lost omittedReasonRound := by decide
  have trueThesis : ThesisTrue BuddhistComparativeLogic.Nyaya.smokeFire :=
    BuddhistComparativeLogic.Nyaya.smokeFireFive.sound
  refine ⟨lost, trueThesis, ?_⟩
  intro transfer
  exact transfer lost trueThesis

/-- Conversely, explicit concession can produce procedural victory even for
the existing `nofire` inference whose subject thesis is false. -/
theorem procedural_victory_does_not_entail_true_thesis :
    Won concededRound ∧
      ¬ ThesisTrue BuddhistComparativeLogic.Hetucakra.nofire := by
  exact ⟨by decide,
    BuddhistComparativeLogic.Hetucakra.no_deductive_soundness.2.2⟩

end BuddhistComparativeLogic.Vadanyaya
