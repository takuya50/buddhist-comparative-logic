/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Grammar.PaniniDerivation
import BuddhistComparativeLogic.Buddhist.HeartSutra.PremiseCertificates

/-!
# Ranked grounds for Mīmāṃsā viniyoga

This module formalizes a finite resolver for the six interpretive grounds
often ordered as `śruti`, `liṅga`, `vākya`, `prakaraṇa`, `sthāna`, and
`samākhyā`.  Evidence records both whether it applies in the present case and
which decision it supports.  The resolver first finds the strongest rank
among applicable items and returns a decision only when every item at that
rank supports the same result.

The textual anchor is Jaimini's *Mīmāṃsāsūtra* 3.3.14.  The Sanskrit text in
the TextGrid Repository enumerates these six grounds and says that, when they
concur, the later members are progressively weaker because they are more
remote from the meaning:
<https://www.textgridrep.org/browse/49nrf.0>.  This module paraphrases only
that ordering claim; it does not reproduce or translate the surrounding
ritual examples or Śabara's commentary.

The numerical ranks are a modern implementation of relative priority among
applicable grounds.  They are not a truth procedure and do not claim that the
six grounds settle every historical Mīmāṃsā dispute.  Equal-rank disagreement
remains unresolved, while a stronger but inapplicable item has no force.  An
additional semantic warrant is required before a resolved decision may be
treated as true.
-/

namespace BuddhistComparativeLogic.MimamsaViniyoga

universe u

/-! ## The six grounds and finite evidence -/

inductive Ground where
  | sruti
  | linga
  | vakya
  | prakarana
  | sthana
  | samakhya
  deriving DecidableEq, Repr

namespace Ground

/-- Higher numbers represent stronger relative priority. -/
def rank : Ground -> Nat
  | .sruti => 6
  | .linga => 5
  | .vakya => 4
  | .prakarana => 3
  | .sthana => 2
  | .samakhya => 1

theorem strict_priority_chain :
    rank .samakhya < rank .sthana /\
      rank .sthana < rank .prakarana /\
      rank .prakarana < rank .vakya /\
      rank .vakya < rank .linga /\
      rank .linga < rank .sruti := by
  decide

end Ground

/-- One finite item of interpretive evidence.  `supports` is a decision label,
not a proof that the decision is true. -/
structure Evidence (Decision : Type u) where
  ground : Ground
  applicable : Bool
  supports : Decision
  deriving DecidableEq, Repr

namespace Evidence

variable {Decision : Type u}

def Supports (evidence : Evidence Decision) (decision : Decision) : Prop :=
  evidence.supports = decision

end Evidence

def applicableInventory {Decision : Type u}
    (inventory : List (Evidence Decision)) : List (Evidence Decision) :=
  inventory.filter (fun evidence => evidence.applicable)

/-- The greatest rank represented by applicable evidence, if any. -/
def topRank {Decision : Type u}
    (inventory : List (Evidence Decision)) : Option Nat :=
  ((applicableInventory inventory).map
    (fun evidence => evidence.ground.rank)).max?

/-- All applicable evidence at the greatest applicable rank. -/
def strongest {Decision : Type u}
    (inventory : List (Evidence Decision)) : List (Evidence Decision) :=
  inventory.filter fun evidence =>
    evidence.applicable &&
      decide (topRank inventory = some evidence.ground.rank)

/-- Return a decision exactly when the highest applicable layer is nonempty
and unanimous.  All operations are executable on a finite list. -/
def resolve {Decision : Type u} [DecidableEq Decision]
    (inventory : List (Evidence Decision)) : Option Decision :=
  match strongest inventory with
  | [] => none
  | first :: rest =>
      if rest.all (fun other => decide (other.supports = first.supports))
      then some first.supports
      else none

/-! ## Soundness and uniqueness of resolution -/

theorem mem_strongest_iff {Decision : Type u}
    {inventory : List (Evidence Decision)} {evidence : Evidence Decision} :
    evidence ∈ strongest inventory <->
      evidence ∈ inventory /\
      evidence.applicable = true /\
      topRank inventory = some evidence.ground.rank := by
  simp [strongest]

theorem strongest_is_applicable_and_maximal {Decision : Type u}
    {inventory : List (Evidence Decision)} {evidence : Evidence Decision}
    (member : evidence ∈ strongest inventory) :
    evidence ∈ inventory /\
      evidence.applicable = true /\
      forall other, other ∈ inventory -> other.applicable = true ->
        other.ground.rank <= evidence.ground.rank := by
  have properties := mem_strongest_iff.mp member
  refine ⟨properties.1, properties.2.1, ?_⟩
  intro other otherMember otherApplicable
  have maximum :=
    (List.max?_eq_some_iff.mp properties.2.2).2
  apply maximum other.ground.rank
  apply List.mem_map.mpr
  exact ⟨other, List.mem_filter.mpr ⟨otherMember, otherApplicable⟩, rfl⟩

/-- Every executable success is backed by applicable evidence at the maximal
applicable rank. -/
theorem resolve_some_sound {Decision : Type u} [DecidableEq Decision]
    {inventory : List (Evidence Decision)} {decision : Decision}
    (resolved : resolve inventory = some decision) :
    exists evidence,
      evidence ∈ inventory /\
      evidence.applicable = true /\
      evidence.Supports decision /\
      forall other, other ∈ inventory -> other.applicable = true ->
        other.ground.rank <= evidence.ground.rank := by
  unfold resolve at resolved
  cases selected : strongest inventory with
  | nil => simp [selected] at resolved
  | cons first rest =>
      by_cases unanimous :
          rest.all (fun other => decide (other.supports = first.supports)) = true
      · simp [selected, unanimous] at resolved
        subst decision
        have member : first ∈ strongest inventory := by
          rw [selected]
          simp
        have properties := strongest_is_applicable_and_maximal member
        exact ⟨first, properties.1, properties.2.1, rfl, properties.2.2⟩
      · simp [selected, unanimous] at resolved

/-- A certificate says that the executable strongest layer contains exactly
one evidence item.  Its witness can be inspected and consumed by adapters. -/
structure UniqueStrongestCertificate {Decision : Type u}
    (inventory : List (Evidence Decision)) : Type u where
  evidence : Evidence Decision
  strongest_eq : strongest inventory = [evidence]

theorem unique_strongest_is_applicable_and_maximal
    {Decision : Type u} {inventory : List (Evidence Decision)}
    (certificate : UniqueStrongestCertificate inventory) :
    certificate.evidence ∈ inventory /\
      certificate.evidence.applicable = true /\
      forall other, other ∈ inventory -> other.applicable = true ->
        other.ground.rank <= certificate.evidence.ground.rank := by
  apply strongest_is_applicable_and_maximal
  rw [certificate.strongest_eq]
  simp

theorem unique_strongest_evidence_unique
    {Decision : Type u} {inventory : List (Evidence Decision)}
    (certificate : UniqueStrongestCertificate inventory)
    {other : Evidence Decision} (member : other ∈ strongest inventory) :
    other = certificate.evidence := by
  rw [certificate.strongest_eq] at member
  simpa using member

theorem unique_strongest_resolves
    {Decision : Type u} [DecidableEq Decision]
    {inventory : List (Evidence Decision)}
    (certificate : UniqueStrongestCertificate inventory) :
    resolve inventory = some certificate.evidence.supports := by
  simp [resolve, certificate.strongest_eq]

theorem resolved_decision_unique
    {Decision : Type u} [DecidableEq Decision]
    {inventory : List (Evidence Decision)} {left right : Decision}
    (leftResult : resolve inventory = some left)
    (rightResult : resolve inventory = some right) : left = right := by
  rw [leftResult] at rightResult
  exact Option.some.inj rightResult

private theorem maxNat_perm {left right : List Nat}
    (permutation : left.Perm right) : left.max? = right.max? := by
  cases leftMax : left.max? with
  | none =>
      have leftEmpty : left = [] := List.max?_eq_none_iff.mp leftMax
      subst left
      have rightEmpty : right = [] := permutation.symm.eq_nil
      subst right
      rfl
  | some greatest =>
      have leftSpec := List.max?_eq_some_iff.mp leftMax
      have rightSpec :
          greatest ∈ right /\
            forall value, value ∈ right -> value <= greatest := by
        constructor
        · exact permutation.mem_iff.mp leftSpec.1
        · intro value member
          exact leftSpec.2 value (permutation.mem_iff.mpr member)
      have rightMax : right.max? = some greatest :=
        List.max?_eq_some_iff.mpr rightSpec
      exact rightMax.symm

theorem topRank_perm {Decision : Type u}
    {left right : List (Evidence Decision)}
    (permutation : left.Perm right) : topRank left = topRank right := by
  apply maxNat_perm
  exact (permutation.filter (fun evidence => evidence.applicable)).map
    (fun evidence => evidence.ground.rank)

theorem strongest_perm {Decision : Type u}
    {left right : List (Evidence Decision)}
    (permutation : left.Perm right) :
    (strongest left).Perm (strongest right) := by
  unfold strongest
  rw [topRank_perm permutation]
  exact permutation.filter _

private theorem perm_singleton_eq {alpha : Type u} {item : alpha}
    {items : List alpha} (permutation : [item].Perm items) :
    items = [item] := by
  have lengthOne : items.length = 1 := by
    simpa using permutation.length_eq.symm
  cases items with
  | nil => simp at lengthOne
  | cons head tail =>
      cases tail with
      | nil =>
          have headMember : head ∈ [item] :=
            permutation.mem_iff.mpr (by simp)
          have headEq : head = item := by simpa using headMember
          simp [headEq]
      | cons next rest => simp at lengthOne

/-- A permutation transports a unique-strongest certificate and leaves the
resolved decision unchanged. -/
theorem unique_strongest_order_invariant
    {Decision : Type u} [DecidableEq Decision]
    {left right : List (Evidence Decision)}
    (permutation : left.Perm right)
    (certificate : UniqueStrongestCertificate left) :
    exists transported : UniqueStrongestCertificate right,
      transported.evidence = certificate.evidence /\
        resolve left = resolve right := by
  have selectedPerm := strongest_perm permutation
  rw [certificate.strongest_eq] at selectedPerm
  have rightStrongest : strongest right = [certificate.evidence] :=
    perm_singleton_eq selectedPerm
  let transported : UniqueStrongestCertificate right :=
    { evidence := certificate.evidence
      strongest_eq := rightStrongest }
  refine ⟨transported, rfl, ?_⟩
  rw [unique_strongest_resolves certificate,
    unique_strongest_resolves transported]

/-! ## Adapters to existing proof-bearing interfaces -/

/-- Package successful resolution in the repository's provenance-aware
premise type.  The external locator remains metadata; the `fact` field is the
Lean proof furnished by the unique-strongest certificate. -/
def toPremiseCertificate
    {Decision : Type u} [DecidableEq Decision]
    {inventory : List (Evidence Decision)}
    (certificate : UniqueStrongestCertificate inventory) :
    BuddhistComparativeLogic.PremiseCertificates.Certified
      (resolve inventory = some certificate.evidence.supports) where
  evidence :=
    { kind := .philosophical
      source := "Mimamsa viniyoga priority model"
      locator := .external "six ranked grounds with applicability" }
  fact := unique_strongest_resolves certificate

inductive ResolutionRule where
  | applyStrongest
  deriving DecidableEq, Repr

inductive ResolutionTerm (Decision : Type u) where
  | pending
  | settled (decision : Decision)
  deriving DecidableEq, Repr

/-- A certified one-step resolution induces an actual Pāṇinian
`PrioritySystem`: its single rule rewrites the pending problem to the decision
selected by the strongest applicable evidence. -/
def toPaniniPrioritySystem
    {Decision : Type u} {inventory : List (Evidence Decision)}
    (certificate : UniqueStrongestCertificate inventory) :
    BuddhistComparativeLogic.PaniniDerivation.PrioritySystem
      (ResolutionTerm Decision) ResolutionRule where
  applies
    | .applyStrongest, .pending => true
    | _, _ => false
  result
    | .applyStrongest, .pending => .settled certificate.evidence.supports
    | _, term => term
  priority := fun _ => certificate.evidence.ground.rank
  rank
    | .pending => 1
    | .settled _ => 0
  rules := [.applyStrongest]
  rulesComplete := by intro rule; cases rule; simp
  rulesNodup := by simp
  decreases := by
    intro rule term applicable
    cases rule
    cases term <;> simp_all
  choose
    | .pending => some .applyStrongest
    | .settled _ => none
  chooseSound := by
    intro term rule selected
    cases term <;> cases rule <;> simp_all
  chooseComplete := by
    intro term selected rule
    cases term <;> cases rule <;> simp_all
  chooseMaximal := by
    intro term rule selected alternative applicable
    cases term <;> cases rule <;> cases alternative <;> simp_all

theorem panini_adapter_agrees_with_resolver
    {Decision : Type u} [DecidableEq Decision]
    {inventory : List (Evidence Decision)}
    (certificate : UniqueStrongestCertificate inventory) :
    (toPaniniPrioritySystem certificate).next? (.pending) =
        some (.settled certificate.evidence.supports) /\
      resolve inventory = some certificate.evidence.supports :=
  ⟨rfl, unique_strongest_resolves certificate⟩

/-! ## Finite countermodels and a positive certificate -/

inductive DemoDecision where
  | perform
  | omit
  deriving DecidableEq, Repr

open DemoDecision

def srutiPerform : Evidence DemoDecision :=
  { ground := .sruti, applicable := true, supports := .perform }

def srutiOmit : Evidence DemoDecision :=
  { ground := .sruti, applicable := true, supports := .omit }

def lingaPerform : Evidence DemoDecision :=
  { ground := .linga, applicable := true, supports := .perform }

def inapplicableSrutiOmit : Evidence DemoDecision :=
  { ground := .sruti, applicable := false, supports := .omit }

def equalRankConflict : List (Evidence DemoDecision) :=
  [srutiPerform, srutiOmit]

/-- Equal-rank evidence for opposite decisions is unresolved by hierarchy
alone. -/
theorem equal_rank_conflict_is_unresolved :
    Nonempty (Evidence DemoDecision) /\
      topRank equalRankConflict = some Ground.sruti.rank /\
      (strongest equalRankConflict).length = 2 /\
      resolve equalRankConflict = none := by
  exact ⟨⟨srutiPerform⟩, by decide⟩

def inapplicableStrongerInventory : List (Evidence DemoDecision) :=
  [inapplicableSrutiOmit, lingaPerform]

/-- An inapplicable `śruti` item does not defeat applicable `liṅga` evidence. -/
theorem inapplicable_stronger_does_not_defeat_applicable_weaker :
    topRank inapplicableStrongerInventory = some Ground.linga.rank /\
      strongest inapplicableStrongerInventory = [lingaPerform] /\
      resolve inapplicableStrongerInventory = some .perform := by
  decide

def lingaPerformCertificate :
    UniqueStrongestCertificate inapplicableStrongerInventory where
  evidence := lingaPerform
  strongest_eq := by decide

theorem finite_positive_certificate_is_sound :
    resolve inapplicableStrongerInventory = some .perform /\
      lingaPerform ∈ inapplicableStrongerInventory /\
      lingaPerform.applicable = true := by
  have properties :=
    unique_strongest_is_applicable_and_maximal lingaPerformCertificate
  exact ⟨unique_strongest_resolves lingaPerformCertificate,
    properties.1, properties.2.1⟩

def falseHighInventory : List (Evidence DemoDecision) :=
  [srutiOmit]

def intendedMeaning : DemoDecision -> Prop
  | .perform => True
  | .omit => False

/-- Priority can select a decision which an independent valuation rejects;
relative evidential strength is not semantic truth. -/
theorem hierarchy_alone_is_not_a_truth_decider :
    resolve falseHighInventory = some .omit /\
      ¬ intendedMeaning .omit := by
  simp [resolve, strongest, topRank, applicableInventory,
    falseHighInventory, srutiOmit, intendedMeaning, Ground.rank]

end BuddhistComparativeLogic.MimamsaViniyoga
