/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.InferenceScope
import BuddhistComparativeLogic.Comparative.Nyaya.Nyaya
import BuddhistComparativeLogic.Buddhist.Madhyamaka.Prasanga
import BuddhistComparativeLogic.Buddhist.Pramana.Tibetan.Debate

/-!
# Autonomous inference and consequence refutation

This module supplies two small interfaces for comparing an autonomous
inference with a consequence-style refutation.  It is not a definition of
the historically contested labels *Svatantrika* and *Prasangika*, nor does it
attribute one fixed proof theory to Bhaviveka, Candrakirti, or later Tibetan
authors.  The interfaces isolate claims that can be checked in the present
repository: a deductively sound argument may also require the opponent's
commitment to its subject reason and pervasion, whereas a covered refutation
of an opponent's claim does not by itself prove an independent thesis.

The semantic premises reuse `InferenceScope` and `Nyaya`.  Opponent-relative
availability reuses the commitment ledger of `TibetanDebate`, and the
consequence refutation delegates to the generic exhaustive eliminator in
`Prasanga`.  Finite examples keep semantic truth, public acceptability, and
the transfer from refutation to an independent thesis visibly separate.
-/

namespace BuddhistComparativeLogic.SvatantraPrasanga

open BuddhistComparativeLogic.Hetucakra

/-! ## One argument retained across semantic and dialectical layers -/

/-- Labels for the two premises and conclusion of one particular inference.
Indexing the claim type by the complete `Anumana`, rather than merely carrying
its subject, prevents tokens belonging to distinct arguments from sharing a
ledger even when those arguments happen to have the same subject. -/
inductive InferenceClaim {L : Type u} (argument : Anumana L) where
  | subjectReason
  | pervasion
  | conclusion
  deriving DecidableEq, Repr

/-- The public consequence associated with an `Anumana`. -/
def challenge (argument : Anumana L) :
    TibetanDebate.Consequence (InferenceClaim argument) where
  subjectReason := .subjectReason
  pervasion := .pervasion
  conclusion := .conclusion

/-- A semantic interpretation of the dialogue labels.  The pervasion label
uses the globally scoped predicate audited by `InferenceScope`. -/
def meaning (argument : Anumana L) : InferenceClaim argument -> Prop
  | .subjectReason => argument.reason argument.paksa
  | .pervasion => InferenceScope.Pervasion argument
  | .conclusion => argument.sadhya argument.paksa

/-- The generated consequence is semantically sound.  This theorem says
nothing yet about whether either dialogue participant accepts its premises. -/
theorem challenge_sound (argument : Anumana L) :
    TibetanDebate.SoundUnder (meaning argument) (challenge argument) := by
  intro subjectReason pervasion
  exact pervasion argument.paksa subjectReason

/-- A project-level proxy for an autonomous argument that is both
deductively certified and available against the defender's current ledger.
The two ledger fields are explicit because semantic truth does not create a
dialectical commitment. -/
structure SvatantraCertificate (argument : Anumana L) where
  semantic : Nyaya.SemanticProof argument
  state : TibetanDebate.State (InferenceClaim argument)
  pending : state.pending = some (challenge argument)
  opponentAcceptsReason :
    state.ledger.Committed .defender .subjectReason
  opponentAcceptsPervasion :
    state.ledger.Committed .defender .pervasion

namespace SvatantraCertificate

variable {L : Type u} {argument : Anumana L}

/-- A certified argument establishes the subject thesis semantically and
makes acceptance a legal move in the explicit dialogue state. -/
theorem sound_and_acceptable (certificate : SvatantraCertificate argument) :
    argument.sadhya argument.paksa /\
      TibetanDebate.LegalReply certificate.state (challenge argument)
        .accept /\
      (TibetanDebate.resolve certificate.state (challenge argument) .accept).ledger.Committed
        .defender .conclusion := by
  have accepted :=
    TibetanDebate.reason_and_pervasion_acceptance_commits
      certificate.state (challenge argument)
      certificate.opponentAcceptsReason certificate.opponentAcceptsPervasion
  exact ⟨certificate.semantic.sound, accepted⟩

/-- The pending field turns the legal acceptance into an actual one-step
response of the existing debate calculus. -/
theorem accepting_response (certificate : SvatantraCertificate argument) :
    TibetanDebate.Responds certificate.state (challenge argument) .accept
      (TibetanDebate.resolve certificate.state (challenge argument) .accept) where
  pending := certificate.pending
  legal := certificate.sound_and_acceptable.2.1
  result := rfl

end SvatantraCertificate

/-! ## A covered consequence refutation -/

/-- A consequence certificate exposes both the coverage premise and the
rejection of every covered case.  It is intentionally weaker than an
autonomous proof of some separately chosen proposition. -/
structure PrasangaCertificate (opponentClaim : Prop) where
  caseOf : Origin -> Prop
  coverage : opponentClaim -> exists origin, caseOf origin
  rejects : forall origin, ¬ caseOf origin

namespace PrasangaCertificate

/-- Reuse the repository's exhaustive reductio rather than baking negation
of the opponent's claim into the certificate. -/
theorem refutes {opponentClaim : Prop}
    (certificate : PrasangaCertificate opponentClaim) : ¬ opponentClaim :=
  Prasanga.exhaustive_reductio opponentClaim certificate.caseOf
    certificate.coverage certificate.rejects

end PrasangaCertificate

/-! ## Finite witnesses and boundary cases -/

/-- Both obligations are on the defender's finite ledger for the existing
three-place smoke/fire inference. -/
def smokeFireState :
    TibetanDebate.State (InferenceClaim Nyaya.smokeFire) where
  ledger :=
    { challenger := []
      defender := [.subjectReason, .pervasion] }
  pending := some (challenge Nyaya.smokeFire)

def smokeFireCertificate : SvatantraCertificate Nyaya.smokeFire where
  semantic := Nyaya.smokeFireFive.toSemanticProof
  state := smokeFireState
  pending := rfl
  opponentAcceptsReason := by
    change (.subjectReason : InferenceClaim Nyaya.smokeFire) ∈
      [.subjectReason, .pervasion]
    decide
  opponentAcceptsPervasion := by
    change (.pervasion : InferenceClaim Nyaya.smokeFire) ∈
      [.subjectReason, .pervasion]
    decide

/-- Nonvacuity: the certificate is inhabited, the subject has the reason,
there is a positive comparison witness, and there is a genuinely negative
comparison place. -/
theorem autonomous_inference_nonvacuous :
    Nonempty (SvatantraCertificate Nyaya.smokeFire) /\
      Nyaya.smokeFire.reason Nyaya.smokeFire.paksa /\
      (exists place,
        Nyaya.smokeFire.reason place /\ Nyaya.smokeFire.sadhya place) /\
      (exists place,
        ¬ Nyaya.smokeFire.reason place /\
          ¬ Nyaya.smokeFire.sadhya place) := by
  exact ⟨⟨smokeFireCertificate⟩, by simp [Nyaya.smokeFire],
    Nyaya.smokeFire_nonvacuous.2⟩

/-- The same sound inference placed in a ledger that contains only its
subject reason. -/
def reasonOnlySmokeState :
    TibetanDebate.State (InferenceClaim Nyaya.smokeFire) where
  ledger :=
    { challenger := []
      defender := [.subjectReason] }
  pending := some (challenge Nyaya.smokeFire)

/-- Semantic soundness does not force an opponent to accept the pervasion.
This finite state therefore licenses the targeted noncommitment reply and
forbids acceptance even though the subject thesis is true. -/
theorem semantic_soundness_does_not_force_dialectical_acceptance :
    Nyaya.SemanticProof Nyaya.smokeFire /\
      Nyaya.smokeFire.sadhya Nyaya.smokeFire.paksa /\
      TibetanDebate.LegalReply reasonOnlySmokeState
        (challenge Nyaya.smokeFire) .pervasionNotCommitted /\
      ¬ TibetanDebate.LegalReply reasonOnlySmokeState
        (challenge Nyaya.smokeFire) .accept := by
  refine ⟨Nyaya.smokeFireFive.toSemanticProof, Nyaya.smokeFireFive.sound,
    ?_, ?_⟩
  · change
      ((.subjectReason : InferenceClaim Nyaya.smokeFire) ∈ [.subjectReason]) /\
        ¬ ((.pervasion : InferenceClaim Nyaya.smokeFire) ∈ [.subjectReason])
    decide
  · change ¬
      (((.subjectReason : InferenceClaim Nyaya.smokeFire) ∈ [.subjectReason]) /\
        ((.pervasion : InferenceClaim Nyaya.smokeFire) ∈ [.subjectReason]))
    decide

/-- A state containing the pervasion label but not the subject reason for
Nyaya's existing missing-application countermodel. -/
def pervasionOnlyState :
    TibetanDebate.State (InferenceClaim Nyaya.missingApplication) where
  ledger :=
    { challenger := []
      defender := [.pervasion] }
  pending := some (challenge Nyaya.missingApplication)

/-- A nonvacuous example plus pervasion does not repair the missing subject
reason.  The semantic certificate would imply the already refuted thesis,
while the dialogue calculus identifies exactly the missing commitment. -/
theorem missing_subject_reason_blocks_both_layers :
    Nonempty (Nyaya.Udaharana Nyaya.missingApplication) /\
      TibetanDebate.LegalReply pervasionOnlyState
        (challenge Nyaya.missingApplication) .reasonNotCommitted /\
      ¬ Nyaya.SemanticProof Nyaya.missingApplication /\
      ¬ Nyaya.missingApplication.sadhya
        Nyaya.missingApplication.paksa := by
  refine ⟨⟨Nyaya.missingApplicationUdaharana⟩, ?_, ?_,
    Nyaya.missing_reason_and_application_does_not_establish_thesis.2.2⟩
  · change ¬
      ((.subjectReason : InferenceClaim Nyaya.missingApplication) ∈ [.pervasion])
    decide
  · intro semantic
    exact Nyaya.missing_reason_and_application_does_not_establish_thesis.2.2
      semantic.sound

/-- Two independent positions are enough to audit the invalid reverse step
from refuting one position to establishing the other. -/
inductive MiniPosition where
  | opponent
  | proponent
  deriving DecidableEq, Repr

/-- Four concrete, separately decidable contradictions indexed by the four
origins.  No branch is definitionally the constant `False` predicate. -/
def miniCase : Origin -> Prop
  | .self => false = true
  | .other => true = false
  | .both => (0 : Nat) = 1
  | .neither => (some true : Option Bool) = none

/-- The opponent's position is exactly the assertion that one of the four
concrete origin cases holds. -/
def miniOpponentClaim : Prop := exists origin, miniCase origin

def miniMeaning : MiniPosition -> Prop
  | .opponent => miniOpponentClaim
  | .proponent => False

/-- Each branch is rejected on its own finite equality computation. -/
theorem mini_cases_individually_refuted :
    (¬ miniCase .self) /\ (¬ miniCase .other) /\
      (¬ miniCase .both) /\ (¬ miniCase .neither) := by
  simp [miniCase]

def miniPrasanga : PrasangaCertificate miniOpponentClaim where
  caseOf := miniCase
  coverage := fun covered => covered
  rejects := by
    intro origin
    cases origin <;> simp [miniCase]

/-- Refutation has no general reverse implication to an independent thesis.
The model is finite and the refutation certificate is explicitly inhabited. -/
theorem refutation_does_not_establish_an_independent_thesis :
    Nonempty (PrasangaCertificate (miniMeaning .opponent)) /\
      ¬ miniMeaning .opponent /\
      ¬ miniMeaning .proponent /\
      ¬ (¬ miniMeaning .opponent -> miniMeaning .proponent) := by
  refine ⟨⟨miniPrasanga⟩, miniPrasanga.refutes, fun h => h, ?_⟩
  intro transfer
  exact transfer miniPrasanga.refutes

end BuddhistComparativeLogic.SvatantraPrasanga
