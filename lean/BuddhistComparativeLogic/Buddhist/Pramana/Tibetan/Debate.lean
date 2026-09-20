/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.PramanaSynthesis
import Lean.Elab.Tactic.Omega

/-!
# A small consequence-debate calculus

This module gives a deliberately small calculus inspired by Tibetan
`bsdus grwa` consequence debate.  It is not a transcription of any one
monastic manual, and its three replies are not claimed to exhaust the
historical vocabulary.  They isolate one proof-theoretic core: a challenger
presents a consequence, while a defender may accept it, report no commitment
to its subject-reason, or report no commitment to its pervasion.

The latter two constructors implement a closed-world ledger dispatcher:
absence from the defender's ledger means only “not committed here.”  It is not
semantic falsity, a refutation, or the richer historical claim that a reason
has been shown not to be established.  Such evidence would require a separate
challenge or refutation layer.

Claims are syntactic labels.  A ledger records dialectical commitments, not
truth.  Acceptance adds a conclusion only when the defender is already
committed to the subject-reason and pervasion obligations.  A separate
semantic bridge below shows that these are exactly the two obligations used
by the project's Dharmakirti inference interface.

The final termination result is intentionally strategy-relative.  On a
finite language, a strategy that accepts only fresh conclusions has at most
as many rounds as there are claim labels.  The unrestricted legal transition
system can instead repeat an unresolved reason-noncommitment response forever; finite
language alone does not imply termination.
-/

namespace BuddhistComparativeLogic.TibetanDebate

/-! ## Roles, commitments, and consequence obligations -/

inductive Role where
  | challenger
  | defender
  deriving DecidableEq, Repr

/-- A consequence has two separately challengeable premises.  The
`subjectReason` field names possession of the reason at the disputed subject;
`pervasion` names the rule carrying that reason to the conclusion. -/
structure Consequence (Claim : Type u) where
  subjectReason : Claim
  pervasion : Claim
  conclusion : Claim
  deriving Repr

inductive Obligation where
  | subjectReason
  | pervasion
  deriving DecidableEq, Repr

namespace Consequence

variable {Claim : Type u}

def obligation (c : Consequence Claim) : Obligation → Claim
  | .subjectReason => c.subjectReason
  | .pervasion => c.pervasion

end Consequence

/-- The calculus keeps only the three replies relevant to the two explicit
inference obligations. -/
inductive Reply where
  | accept
  | reasonNotCommitted
  | pervasionNotCommitted
  deriving DecidableEq, Repr

namespace Reply

/-- An acceptance closes the consequence.  Each noncommitment response points
to exactly one of its two proof obligations. -/
def target : Reply → Option Obligation
  | .accept => none
  | .reasonNotCommitted => some .subjectReason
  | .pervasionNotCommitted => some .pervasion

@[simp] theorem reason_noncommitment_target :
    target .reasonNotCommitted = some .subjectReason := rfl

@[simp] theorem pervasion_noncommitment_target :
    target .pervasionNotCommitted = some .pervasion := rfl

@[simp] theorem acceptance_has_no_noncommitment_target :
    target .accept = none := rfl

end Reply

/-- Each role has its own ordered ledger.  Repetition is permitted by the
unrestricted calculus; the terminating strategy below explicitly forbids it
for newly accepted conclusions. -/
structure Ledger (Claim : Type u) where
  challenger : List Claim
  defender : List Claim

namespace Ledger

variable {Claim : Type u}

def claims (ledger : Ledger Claim) : Role → List Claim
  | .challenger => ledger.challenger
  | .defender => ledger.defender

abbrev Committed (ledger : Ledger Claim) (role : Role) (claim : Claim) : Prop :=
  claim ∈ ledger.claims role

def add (ledger : Ledger Claim) (role : Role) (claim : Claim) : Ledger Claim :=
  match role with
  | .challenger =>
      { challenger := claim :: ledger.challenger
        defender := ledger.defender }
  | .defender =>
      { challenger := ledger.challenger
        defender := claim :: ledger.defender }

/-- `newer.Extends older` means that no earlier role commitment was lost. -/
def Extends (newer older : Ledger Claim) : Prop :=
  ∀ role claim, older.Committed role claim → newer.Committed role claim

theorem add_commits (ledger : Ledger Claim) (role : Role) (claim : Claim) :
    (ledger.add role claim).Committed role claim := by
  cases role <;> simp [add, Committed, claims]

theorem add_extends (ledger : Ledger Claim) (role : Role) (claim : Claim) :
    (ledger.add role claim).Extends ledger := by
  intro other statement committed
  cases role <;> cases other <;> simp_all [add, Committed, claims]

theorem Extends.refl (ledger : Ledger Claim) : ledger.Extends ledger :=
  fun _ _ committed => committed

theorem Extends.trans {first second third : Ledger Claim}
    (h₁ : first.Extends second) (h₂ : second.Extends third) :
    first.Extends third :=
  fun role claim committed => h₁ role claim (h₂ role claim committed)

end Ledger

/-- `pending` records an issued consequence.  Merely issuing it changes no
commitment: the challenger may be testing consequences of the defender's
ledger without asserting the conclusion. -/
structure State (Claim : Type u) where
  ledger : Ledger Claim
  pending : Option (Consequence Claim)

namespace State

variable {Claim : Type u}

def issue (state : State Claim) (challenge : Consequence Claim) : State Claim :=
  { state with pending := some challenge }

@[simp] theorem issue_ledger (state : State Claim)
    (challenge : Consequence Claim) :
    (state.issue challenge).ledger = state.ledger := rfl

end State

/-! ## Legal replies and state transitions -/

/-- A defender may accept exactly when both displayed obligations are already
in its ledger.  If the reason is absent it reports reason noncommitment; if the
reason is present but pervasion is absent it reports pervasion noncommitment.
This is an explicit closed-world protocol over ledger membership.  The
priority makes its three legal cases disjoint as well as exhaustive. -/
def LegalReply {Claim : Type u} (state : State Claim)
    (challenge : Consequence Claim) : Reply → Prop
  | .accept =>
      state.ledger.Committed .defender challenge.subjectReason ∧
        state.ledger.Committed .defender challenge.pervasion
  | .reasonNotCommitted =>
      ¬ state.ledger.Committed .defender challenge.subjectReason
  | .pervasionNotCommitted =>
      state.ledger.Committed .defender challenge.subjectReason ∧
        ¬ state.ledger.Committed .defender challenge.pervasion

/-- Resolve the current challenge.  Acceptance adds its conclusion to the
defender's ledger; noncommitment replies close the pending exchange without
changing either ledger.  Legality is imposed by `Responds` or `Move.LegalAt`,
rather than by this total update function. -/
def resolve {Claim : Type u} (state : State Claim)
    (challenge : Consequence Claim) : Reply → State Claim
  | .accept =>
      { ledger := state.ledger.add .defender challenge.conclusion
        pending := none }
  | .reasonNotCommitted => { state with pending := none }
  | .pervasionNotCommitted => { state with pending := none }

/-- A one-step response relation records that the named consequence was
actually pending, that the response was legal, and that `resolve` produced the
next state. -/
structure Responds {Claim : Type u} (state : State Claim)
    (challenge : Consequence Claim) (reply : Reply)
    (next : State Claim) : Prop where
  pending : state.pending = some challenge
  legal : LegalReply state challenge reply
  result : next = resolve state challenge reply

theorem accept_legal_iff {Claim : Type u} (state : State Claim)
    (challenge : Consequence Claim) :
    LegalReply state challenge .accept ↔
      state.ledger.Committed .defender challenge.subjectReason ∧
        state.ledger.Committed .defender challenge.pervasion :=
  Iff.rfl

/-- This is a rule about dialectical commitment.  It does not by itself say
that the accepted conclusion is semantically true. -/
theorem reason_and_pervasion_acceptance_commits {Claim : Type u}
    (state : State Claim) (challenge : Consequence Claim)
    (reason : state.ledger.Committed .defender challenge.subjectReason)
    (pervasion : state.ledger.Committed .defender challenge.pervasion) :
    LegalReply state challenge .accept ∧
      (resolve state challenge .accept).ledger.Committed
        .defender challenge.conclusion := by
  refine ⟨⟨reason, pervasion⟩, ?_⟩
  simpa [resolve] using
    state.ledger.add_commits .defender challenge.conclusion

theorem accepted_response_commits_conclusion {Claim : Type u}
    {state next : State Claim} {challenge : Consequence Claim}
    (response : Responds state challenge .accept next) :
    next.ledger.Committed .defender challenge.conclusion := by
  rw [response.result]
  simpa [resolve] using
    state.ledger.add_commits .defender challenge.conclusion

theorem reason_noncommitment_targets_missing_commitment {Claim : Type u}
    {state : State Claim} {challenge : Consequence Claim}
    (legal : LegalReply state challenge .reasonNotCommitted) :
    Reply.target .reasonNotCommitted = some .subjectReason ∧
      ¬ state.ledger.Committed .defender
        (challenge.obligation .subjectReason) :=
  ⟨rfl, legal⟩

theorem pervasion_noncommitment_targets_missing_commitment {Claim : Type u}
    {state : State Claim} {challenge : Consequence Claim}
    (legal : LegalReply state challenge .pervasionNotCommitted) :
    Reply.target .pervasionNotCommitted = some .pervasion ∧
      state.ledger.Committed .defender
        (challenge.obligation .subjectReason) ∧
      ¬ state.ledger.Committed .defender
        (challenge.obligation .pervasion) :=
  ⟨rfl, legal⟩

theorem resolve_extends {Claim : Type u} (state : State Claim)
    (challenge : Consequence Claim) (reply : Reply) :
    (resolve state challenge reply).ledger.Extends state.ledger := by
  cases reply
  · exact state.ledger.add_extends .defender challenge.conclusion
  · exact Ledger.Extends.refl state.ledger
  · exact Ledger.Extends.refl state.ledger

@[simp] theorem reason_noncommitment_preserves_ledger {Claim : Type u}
    (state : State Claim) (challenge : Consequence Claim) :
    (resolve state challenge .reasonNotCommitted).ledger = state.ledger :=
  rfl

@[simp] theorem pervasion_noncommitment_preserves_ledger {Claim : Type u}
    (state : State Claim) (challenge : Consequence Claim) :
    (resolve state challenge .pervasionNotCommitted).ledger = state.ledger :=
  rfl

/-! ## A decidable finite language and exhaustive reply selection -/

/-- An explicit enumeration witnesses finiteness.  `complete` makes every
claim available to the bound below; `nodup` makes the enumeration a canonical
count rather than a padded upper bound. -/
structure FiniteLanguage (Claim : Type u) where
  enumeration : List Claim
  complete : ∀ claim, claim ∈ enumeration
  nodup : enumeration.Nodup

def chooseReply {Claim : Type u} [DecidableEq Claim]
    (state : State Claim) (challenge : Consequence Claim) : Reply :=
  if state.ledger.Committed .defender challenge.subjectReason then
    if state.ledger.Committed .defender challenge.pervasion then
      .accept
    else
      .pervasionNotCommitted
  else
    .reasonNotCommitted

theorem chooseReply_legal {Claim : Type u} [DecidableEq Claim]
    (state : State Claim) (challenge : Consequence Claim) :
    LegalReply state challenge (chooseReply state challenge) := by
  unfold chooseReply
  by_cases reason :
      state.ledger.Committed .defender challenge.subjectReason
  · simp only [reason, ↓reduceIte]
    by_cases pervasion :
        state.ledger.Committed .defender challenge.pervasion
    · simp [pervasion, LegalReply, reason]
    · simp [pervasion, LegalReply, reason]
  · simp [reason, LegalReply]

/-- The priority built into `LegalReply` makes the three modeled replies
pairwise exclusive as well as exhaustive. -/
theorem legal_reply_unique {Claim : Type u} {state : State Claim}
    {challenge : Consequence Claim} {first second : Reply}
    (firstLegal : LegalReply state challenge first)
    (secondLegal : LegalReply state challenge second) : first = second := by
  cases first <;> cases second <;> simp_all [LegalReply]

/-- In a decidable finite claim language one of the three replies is always
legal.  The local case split needs only decidable equality; the explicit
finite witness is retained because the same language supplies the global
termination bound below. -/
theorem legal_reply_exhaustive {Claim : Type u} [DecidableEq Claim]
    (_language : FiniteLanguage Claim) (state : State Claim)
    (challenge : Consequence Claim) :
    ∃ reply, LegalReply state challenge reply :=
  ⟨chooseReply state challenge, chooseReply_legal state challenge⟩

/-! ## Runs and the fresh-conclusion strategy -/

structure Move (Claim : Type u) where
  challenge : Consequence Claim
  reply : Reply
  deriving Repr

namespace Move

variable {Claim : Type u}

/-- An atomic move may start only from an idle state.  This prevents its
implicit `issue` step from overwriting an older unresolved consequence. -/
def LegalAt (move : Move Claim) (state : State Claim) : Prop :=
  state.pending = none ∧ LegalReply state move.challenge move.reply

def execute (move : Move Claim) (state : State Claim) : State Claim :=
  resolve (state.issue move.challenge) move.challenge move.reply

def FreshAccepting (move : Move Claim) (state : State Claim) : Prop :=
  move.reply = .accept ∧
    ¬ state.ledger.Committed .defender move.challenge.conclusion

theorem legal_starts_without_pending (move : Move Claim)
    (state : State Claim) (legal : move.LegalAt state) :
    state.pending = none :=
  legal.1

/-- An unresolved consequence blocks every new atomic move, so `execute`
cannot silently replace it. -/
theorem pending_blocks_atomic_move (move : Move Claim)
    (state : State Claim) (busy : state.pending ≠ none) :
    ¬ move.LegalAt state := by
  intro legal
  exact busy (move.legal_starts_without_pending state legal)

theorem execute_extends (move : Move Claim) (state : State Claim) :
    (move.execute state).ledger.Extends state.ledger := by
  exact resolve_extends (state.issue move.challenge) move.challenge move.reply

theorem execute_accept_commits (move : Move Claim) (state : State Claim)
    (accepts : move.reply = .accept) :
    (move.execute state).ledger.Committed
      .defender move.challenge.conclusion := by
  unfold execute
  rw [accepts]
  simpa [resolve] using
    state.ledger.add_commits .defender move.challenge.conclusion

end Move

def run {Claim : Type u} : State Claim → List (Move Claim) → State Claim
  | state, [] => state
  | state, move :: moves => run (move.execute state) moves

def LegalTrace {Claim : Type u} : State Claim → List (Move Claim) → Prop
  | _, [] => True
  | state, move :: moves =>
      move.LegalAt state ∧ LegalTrace (move.execute state) moves

/-- This strategy accepts every round and requires its conclusion to be new
at the state where that round begins.  Thus each round consumes one available
claim label. -/
def NewCommitmentTrace {Claim : Type u} :
    State Claim → List (Move Claim) → Prop
  | _, [] => True
  | state, move :: moves =>
      move.LegalAt state ∧ move.FreshAccepting state ∧
        NewCommitmentTrace (move.execute state) moves

def conclusionTrace {Claim : Type u} (moves : List (Move Claim)) : List Claim :=
  moves.map fun move => move.challenge.conclusion

theorem run_extends {Claim : Type u} (state : State Claim)
    (moves : List (Move Claim)) :
    (run state moves).ledger.Extends state.ledger := by
  induction moves generalizing state with
  | nil => exact Ledger.Extends.refl state.ledger
  | cons move moves ih =>
      exact (ih (move.execute state)).trans (move.execute_extends state)

private theorem committed_not_in_new_conclusions {Claim : Type u}
    {state : State Claim} {moves : List (Move Claim)} {claim : Claim}
    (trace : NewCommitmentTrace state moves)
    (committed : state.ledger.Committed .defender claim) :
    claim ∉ conclusionTrace moves := by
  induction moves generalizing state with
  | nil => simp [conclusionTrace]
  | cons move moves ih =>
      simp only [NewCommitmentTrace] at trace
      rcases trace with ⟨_legal, fresh, tail⟩
      simp only [conclusionTrace, List.map_cons, List.mem_cons]
      intro occurs
      rcases occurs with atHead | inTail
      · apply fresh.2
        simpa [atHead] using committed
      · apply ih tail
          (move.execute_extends state .defender claim committed)
        exact inTail

theorem conclusionTrace_nodup {Claim : Type u} {state : State Claim}
    {moves : List (Move Claim)} (trace : NewCommitmentTrace state moves) :
    (conclusionTrace moves).Nodup := by
  induction moves generalizing state with
  | nil => simp [conclusionTrace]
  | cons move moves ih =>
      simp only [NewCommitmentTrace] at trace
      rcases trace with ⟨_legal, fresh, tail⟩
      rw [conclusionTrace]
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · exact committed_not_in_new_conclusions tail
          (move.execute_accept_commits state fresh.1)
      · exact ih tail

private theorem nodup_length_le_of_subset {Claim : Type u}
    [DecidableEq Claim] :
    ∀ (xs ys : List Claim), xs.Nodup → xs ⊆ ys → xs.length ≤ ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _
      simp
  | cons claim claims ih =>
      intro ys nodup subset
      have parts := List.nodup_cons.mp nodup
      have present : claim ∈ ys := subset (by simp)
      have tailSubset : claims ⊆ ys.erase claim := by
        intro other inClaims
        have distinct : other ≠ claim := by
          intro equal
          subst other
          exact parts.1 inClaims
        exact (List.mem_erase_of_ne distinct).2
          (subset (by simp [inClaims]))
      have bound := ih (ys.erase claim) parts.2 tailSubset
      rw [List.length_erase_of_mem present] at bound
      have positive := List.length_pos_of_mem present
      change claims.length + 1 ≤ ys.length
      omega

/-- Finite termination for the stated strategy: no legal trace that accepts a
fresh conclusion at every round can exceed the number of claim labels.  This
is a bound on rounds, not a claim that unrestricted monastic debate must
terminate. -/
theorem finite_termination_bound {Claim : Type u} [DecidableEq Claim]
    (language : FiniteLanguage Claim) (state : State Claim)
    (moves : List (Move Claim))
    (trace : NewCommitmentTrace state moves) :
    moves.length ≤ language.enumeration.length := by
  have distinct := conclusionTrace_nodup trace
  have within : conclusionTrace moves ⊆ language.enumeration :=
    fun claim _ => language.complete claim
  have bound := nodup_length_le_of_subset
    (conclusionTrace moves) language.enumeration distinct within
  simpa [conclusionTrace] using bound

theorem no_overlong_new_commitment_trace {Claim : Type u}
    [DecidableEq Claim] (language : FiniteLanguage Claim)
    (state : State Claim) (moves : List (Move Claim))
    (overlong : language.enumeration.length < moves.length) :
    ¬ NewCommitmentTrace state moves := by
  intro trace
  exact (Nat.not_lt_of_ge
    (finite_termination_bound language state moves trace)) overlong

/-! ## Semantic bridge to the existing inference API -/

/-- `SoundUnder` interprets a consequence without identifying semantic truth
with ledger membership. -/
def SoundUnder {Claim : Type u} (meaning : Claim → Prop)
    (challenge : Consequence Claim) : Prop :=
  meaning challenge.subjectReason →
    meaning challenge.pervasion →
      meaning challenge.conclusion

namespace PramanaBridge

inductive Claim where
  | subjectReason
  | pervasion
  | conclusion
  deriving DecidableEq, Repr

def challenge : Consequence Claim where
  subjectReason := .subjectReason
  pervasion := .pervasion
  conclusion := .conclusion

/-- The labels receive their meaning from a particular Dharmakirti model;
the pervasion label denotes the model's own explicit `vyapti` proposition. -/
def meaning {L : Type u} (model : BuddhistComparativeLogic.Dharmakirti.Model L) :
    Claim → Prop
  | .subjectReason => model.toAnumana.paksadharmata
  | .pervasion => model.vyapti
  | .conclusion => model.sadhya model.paksa

/-- The semantic reading of the dialogue challenge is exactly the project's
two-premise subject-level inference rule. -/
theorem challenge_sound {L : Type u}
    (model : BuddhistComparativeLogic.Dharmakirti.Model L) :
    SoundUnder (meaning model) challenge := by
  intro subjectReason pervasion
  exact model.vyapti_sound pervasion subjectReason

theorem challenge_is_global_pervasion {L : Type u}
    (model : BuddhistComparativeLogic.Dharmakirti.Model L) :
    meaning model .pervasion ↔
      BuddhistComparativeLogic.InferenceScope.Pervasion model.toAnumana :=
  BuddhistComparativeLogic.PramanaSynthesis.vyapti_iff_global_pervasion model

end PramanaBridge

/-! ## Concrete nonvacuity and the unrestricted loop -/

inductive DemoClaim where
  | reason
  | pervasion
  | conclusion
  deriving DecidableEq, Repr

def demoLanguage : FiniteLanguage DemoClaim where
  enumeration := [.reason, .pervasion, .conclusion]
  complete := by intro claim; cases claim <;> simp
  nodup := by decide

def demoChallenge : Consequence DemoClaim where
  subjectReason := .reason
  pervasion := .pervasion
  conclusion := .conclusion

def demoState : State DemoClaim where
  ledger :=
    { challenger := []
      defender := [.reason, .pervasion] }
  pending := some demoChallenge

/-- The acceptance rule has a finite model in which both obligations are
present, the conclusion is initially absent, and the response adds it. -/
theorem acceptance_nonvacuous :
    LegalReply demoState demoChallenge .accept ∧
      ¬ demoState.ledger.Committed .defender .conclusion ∧
      (resolve demoState demoChallenge .accept).ledger.Committed
        .defender .conclusion := by
  simp [LegalReply, demoState, demoChallenge, Ledger.Committed,
    Ledger.claims, resolve, Ledger.add]

inductive LoopClaim where
  | disputedReason
  deriving DecidableEq, Repr

def loopLanguage : FiniteLanguage LoopClaim where
  enumeration := [.disputedReason]
  complete := by intro claim; cases claim; simp
  nodup := by decide

def loopState : State LoopClaim where
  ledger :=
    { challenger := []
      defender := [] }
  pending := none

def loopChallenge : Consequence LoopClaim where
  subjectReason := .disputedReason
  pervasion := .disputedReason
  conclusion := .disputedReason

def loopMove : Move LoopClaim where
  challenge := loopChallenge
  reply := .reasonNotCommitted

theorem loop_move_legal : loopMove.LegalAt loopState := by
  simp [Move.LegalAt, LegalReply, loopMove, loopChallenge, loopState,
    Ledger.Committed, Ledger.claims]

theorem loop_move_stutters : loopMove.execute loopState = loopState := by
  rfl

/-- Even over a one-claim finite language, the same legal noncommitment reply can be
repeated for an arbitrary requested number of rounds.  This is the explicit
boundary showing why the freshness strategy is needed. -/
theorem arbitrarily_long_legal_loop (rounds : Nat) :
    LegalTrace loopState (List.replicate rounds loopMove) ∧
      run loopState (List.replicate rounds loopMove) = loopState ∧
      (List.replicate rounds loopMove).length = rounds := by
  induction rounds with
  | zero => simp [LegalTrace, run]
  | succ rounds ih =>
      simpa [List.replicate_succ, LegalTrace, run, loop_move_legal,
        loop_move_stutters] using ih

end BuddhistComparativeLogic.TibetanDebate
