/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.InferenceScope

/-!
# A five-member public inference protocol

This module gives a deliberately small, text-bounded model of the five
members conventionally named `pratijna`, `hetu`, `udaharana`, `upanaya`, and
`nigamana` in discussions of classical Nyaya inference.  It formalizes one
inferential reading of those members; it is not an edition of the
*Nyayasutra* or *Nyayabhasya*, and it does not claim that every historical
Nyaya author assigned them exactly these proof-theoretic roles.

The public script is kept separate from its semantic certificate.  In this
model the reason and application both assert possession of the reason at the
subject, while the example member contains a universal pervasion premise and
a distinct positive illustration.  The illustration does not generate the
universal premise.  This choice lets Lean expose both the sound argument and
two familiar gaps: one positive example does not prove pervasion, and
pervasion plus an example proves nothing about the subject when subject
application is absent.
-/

namespace BuddhistComparativeLogic.Nyaya

open BuddhistComparativeLogic.Hetucakra

/-- Universal reason-to-thesis inclusion, reusing the scope audited in
`BuddhistComparativeLogic.Buddhist.Pramana.InferenceScope`.  This is an extensional proxy; it does not encode
how Nyāya establishes pervasion or excludes an `upadhi` condition. -/
abbrev Pervasion {L : Type u} (argument : Anumana L) : Prop :=
  BuddhistComparativeLogic.InferenceScope.Pervasion argument

/-- A positive illustration separate from the disputed subject.  This is
only instance-level evidence and contains no universal rule. -/
structure PositiveExample {L : Type u} (argument : Anumana L) where
  witness : L
  distinct : witness ≠ argument.paksa
  hasReason : argument.reason witness
  hasThesis : argument.sadhya witness

/-- The semantic payload assigned here to `udaharana`: a pervasion rule
together with one positive illustration.  The rule is an explicit field, not
a consequence of `example`. -/
structure Udaharana {L : Type u} (argument : Anumana L) where
  pervasion : Pervasion argument
  illustration : PositiveExample argument

/-- The five public member names. -/
inductive Member where
  | pratijna
  | hetu
  | udaharana
  | upanaya
  | nigamana
  deriving DecidableEq, Repr

/-- The semantic claim associated with each public member in this module.
`pratijna` and `nigamana` have the same propositional content; likewise
`hetu` and `upanaya`.  Their different tags retain their public positions. -/
def Member.claim {L : Type u} (argument : Anumana L) : Member -> Prop
  | .pratijna => argument.sadhya argument.paksa
  | .hetu => argument.reason argument.paksa
  | .udaharana => Nonempty (Udaharana argument)
  | .upanaya => argument.reason argument.paksa
  | .nigamana => argument.sadhya argument.paksa

/-- An ordered public script carries no proofs of the claims it displays. -/
structure PublicPresentation where
  members : List Member
  deriving Repr

def fiveMemberOrder : List Member :=
  [.pratijna, .hetu, .udaharana, .upanaya, .nigamana]

def threeMemberOrder : List Member :=
  [.pratijna, .hetu, .udaharana]

def twoMemberOrder : List Member :=
  [.pratijna, .hetu]

def fiveMemberScript : PublicPresentation :=
  { members := fiveMemberOrder }

def threeMemberScript : PublicPresentation :=
  { members := threeMemberOrder }

def twoMemberScript : PublicPresentation :=
  { members := twoMemberOrder }

theorem member_counts :
    fiveMemberScript.members.length = 5 /\
      threeMemberScript.members.length = 3 /\
      twoMemberScript.members.length = 2 := by
  decide

/-! ## Semantic proof and certified public presentation -/

/-- The two semantic premises needed for deduction.  This proof object is
independent of how many public members are uttered. -/
structure SemanticProof {L : Type u} (argument : Anumana L) : Prop where
  subjectReason : argument.reason argument.paksa
  pervasion : Pervasion argument

namespace SemanticProof

variable {L : Type u} {argument : Anumana L}

theorem sound (proof : SemanticProof argument) :
    argument.sadhya argument.paksa :=
  proof.pervasion argument.paksa proof.subjectReason

end SemanticProof

/-- A certified five-member presentation.  `scriptOrder` certifies only the
displayed order.  The other fields certify the inferential premises assigned
to the reason, example, and application members.  Truth of the opening thesis
and closing conclusion is derived below rather than assumed in this record. -/
structure CompletePresentation {L : Type u} (argument : Anumana L) where
  script : PublicPresentation
  scriptOrder : script.members = fiveMemberOrder
  hetu : argument.reason argument.paksa
  udaharana : Udaharana argument
  upanaya : argument.reason argument.paksa

namespace CompletePresentation

variable {L : Type u} {argument : Anumana L}

/-- Extract a semantic deduction from the public application and pervasion
premise.  Neither the opening thesis nor the closing conclusion is used. -/
theorem toSemanticProof (presentation : CompletePresentation argument) :
    SemanticProof argument where
  subjectReason := presentation.upanaya
  pervasion := presentation.udaharana.pervasion

/-- Soundness of the complete presentation. -/
theorem sound (presentation : CompletePresentation argument) :
    argument.sadhya argument.paksa :=
  presentation.toSemanticProof.sound

/-- Every displayed member is semantically licensed once the premise fields
of a complete presentation have been checked. -/
theorem member_sound (presentation : CompletePresentation argument)
    (member : Member) : member.claim argument := by
  cases member with
  | pratijna => exact presentation.sound
  | hetu => exact presentation.hetu
  | udaharana => exact Nonempty.intro presentation.udaharana
  | upanaya => exact presentation.upanaya
  | nigamana => exact presentation.sound

end CompletePresentation

theorem complete_presentation_sound {L : Type u} {argument : Anumana L}
    (presentation : CompletePresentation argument) :
    argument.sadhya argument.paksa :=
  presentation.sound

/-! ## Three- and two-member informational compressions -/

/-- The three-member compression retains the thesis tag, one subject-reason
statement, and the rule-plus-example member.  The repeated application and
conclusion tags are omitted because their claim contents duplicate `hetu`
and the derived `pratijna` in this explicitly stated model. -/
structure ThreeMemberPresentation {L : Type u} (argument : Anumana L) where
  script : PublicPresentation
  scriptOrder : script.members = threeMemberOrder
  hetu : argument.reason argument.paksa
  udaharana : Udaharana argument

namespace ThreeMemberPresentation

variable {L : Type u} {argument : Anumana L}

theorem sound (presentation : ThreeMemberPresentation argument) :
    argument.sadhya argument.paksa :=
  presentation.udaharana.pervasion argument.paksa presentation.hetu

end ThreeMemberPresentation

/-- Erasing the two repeated public members preserves the premises required
for semantic soundness. -/
def CompletePresentation.compressToThree {L : Type u}
    {argument : Anumana L} (presentation : CompletePresentation argument) :
    ThreeMemberPresentation argument where
  script := threeMemberScript
  scriptOrder := rfl
  hetu := presentation.hetu
  udaharana := presentation.udaharana

/-- Background which an audience must already accept before the example
member may be left unuttered.  Keeping both fields explicit prevents the
single illustration from being mistaken for its universal pervasion. -/
structure SharedBackground {L : Type u} (argument : Anumana L) : Prop where
  pervasion : Pervasion argument
  positiveExample : Nonempty (PositiveExample argument)

theorem Udaharana.toSharedBackground {L : Type u} {argument : Anumana L}
    (support : Udaharana argument) : SharedBackground argument where
  pervasion := support.pervasion
  positiveExample := Nonempty.intro support.illustration

/-- A two-member compression utters only the thesis and subject reason.  Its
soundness is conditional on a separately supplied shared background. -/
structure TwoMemberPresentation {L : Type u} (argument : Anumana L) where
  script : PublicPresentation
  scriptOrder : script.members = twoMemberOrder
  hetu : argument.reason argument.paksa

def ThreeMemberPresentation.compressToTwo {L : Type u}
    {argument : Anumana L} (presentation : ThreeMemberPresentation argument)
    (_shared : SharedBackground argument) : TwoMemberPresentation argument where
  script := twoMemberScript
  scriptOrder := rfl
  hetu := presentation.hetu

theorem TwoMemberPresentation.sound_under_shared_background {L : Type u}
    {argument : Anumana L} (presentation : TwoMemberPresentation argument)
    (shared : SharedBackground argument) :
    argument.sadhya argument.paksa :=
  shared.pervasion argument.paksa presentation.hetu

/-- Five, three, and two public members reach the same subject thesis.  The
last compression visibly takes the audience's shared pervasion and example
as an extra argument. -/
theorem compressed_presentations_are_sound {L : Type u}
    {argument : Anumana L} (five : CompletePresentation argument)
    (shared : SharedBackground argument) :
    argument.sadhya argument.paksa /\
      argument.sadhya argument.paksa /\
      argument.sadhya argument.paksa :=
  ⟨five.sound, five.compressToThree.sound,
    TwoMemberPresentation.sound_under_shared_background
      (five.compressToThree.compressToTwo shared) shared⟩

/-! ## Finite audits -/

inductive Place where
  | hill
  | kitchen
  | lake
  deriving DecidableEq, Repr

open Place

/-- A nonvacuous smoke/fire model: smoke occurs at the hill and kitchen,
fire occurs there as well, and neither occurs at the lake. -/
def smokeFire : Anumana Place where
  paksa := .hill
  reason := fun place => place = .hill \/ place = .kitchen
  sadhya := fun place => place ≠ .lake

theorem smokeFire_pervasion : Pervasion smokeFire := by
  intro place smoke
  rcases smoke with rfl | rfl <;> simp [smokeFire]

def smokeFireExample : PositiveExample smokeFire where
  witness := .kitchen
  distinct := by decide
  hasReason := Or.inr rfl
  hasThesis := by simp [smokeFire]

def smokeFireUdaharana : Udaharana smokeFire where
  pervasion := smokeFire_pervasion
  illustration := smokeFireExample

def smokeFireFive : CompletePresentation smokeFire where
  script := fiveMemberScript
  scriptOrder := rfl
  hetu := Or.inl rfl
  udaharana := smokeFireUdaharana
  upanaya := Or.inl rfl

/-- The executable witness has positive subject and example cases and a
negative comparison case, so its soundness is not obtained from empty
predicates or a vacuous pervasion. -/
theorem smokeFire_nonvacuous :
    smokeFire.sadhya smokeFire.paksa /\
      (∃ place, smokeFire.reason place /\ smokeFire.sadhya place) /\
      (∃ place, (¬ smokeFire.reason place) /\
        ¬ smokeFire.sadhya place) := by
  refine ⟨smokeFireFive.sound, ?_, ?_⟩
  · exact ⟨.kitchen, Or.inr rfl, by simp [smokeFire]⟩
  · refine ⟨.lake, ?_, ?_⟩
    · simp [smokeFire]
    · simp [smokeFire]

/-- The kitchen illustrates the reason and thesis together, but the hill is
a counterinstance to the universal rule. -/
def oneExampleOnly : Anumana Place where
  paksa := .hill
  reason := fun place => place = .hill \/ place = .kitchen
  sadhya := fun place => place = .kitchen

def onePositiveExample : PositiveExample oneExampleOnly where
  witness := .kitchen
  distinct := by decide
  hasReason := Or.inr rfl
  hasThesis := rfl

/-- A single positive example does not entail universal `vyapti`. -/
theorem one_example_does_not_entail_pervasion :
    Nonempty (PositiveExample oneExampleOnly) /\
      ¬ Pervasion oneExampleOnly := by
  refine ⟨⟨onePositiveExample⟩, ?_⟩
  intro universal
  have falseThesis : oneExampleOnly.sadhya .hill :=
    universal .hill (Or.inl rfl)
  cases falseThesis

/-- Pervasion and a genuine positive example are present, but the subject has
neither the reason nor the thesis. -/
def missingApplication : Anumana Place where
  paksa := .hill
  reason := fun place => place = .kitchen
  sadhya := fun place => place = .kitchen

def missingApplicationExample : PositiveExample missingApplication where
  witness := .kitchen
  distinct := by decide
  hasReason := rfl
  hasThesis := rfl

def missingApplicationUdaharana : Udaharana missingApplication where
  pervasion := by
    intro place reason
    exact reason
  illustration := missingApplicationExample

/-- Even a nonvacuous, universally valid example member cannot establish the
subject thesis when all evidence for the reason's subject application is
missing.  Since `hetu` and `upanaya` share that content in this model, this is
the countermodel to omitting both informational occurrences. -/
theorem missing_reason_and_application_does_not_establish_thesis :
    Nonempty (Udaharana missingApplication) /\
      ¬ missingApplication.reason missingApplication.paksa /\
      ¬ missingApplication.sadhya missingApplication.paksa := by
  refine ⟨⟨missingApplicationUdaharana⟩, ?_, ?_⟩ <;>
    simp [missingApplication]

/-- Merely displaying the canonical five public tags supplies no semantic
proof: the same script can accompany the false thesis in the preceding
finite countermodel. -/
theorem public_script_is_not_a_semantic_proof :
    fiveMemberScript.members = fiveMemberOrder /\
      ¬ missingApplication.sadhya missingApplication.paksa := by
  exact ⟨rfl, by simp [missingApplication]⟩

end BuddhistComparativeLogic.Nyaya
