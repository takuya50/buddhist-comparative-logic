/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Momentariness

/-!
# Directed causal transport and momentariness

`BuddhistComparativeLogic.Buddhist.Pramana.Momentariness` derives punctual production from a rooted chain whose
links preserve every causal power in both directions.  Literal momentariness
does not need that much.  For a production observed at the end of a rooted
chain, it is enough to transport that same effect backwards, one link at a
time, to the root.  Uniqueness of an effect's production time then identifies
the observed time with the root.

This module isolates that directed criterion, proves the corresponding
momentariness theorem, embeds the earlier two-way criterion into it, and gives
a finite model in which backward transport holds while forward transport
fails.  Thus the weaker theorem does not silently assume persistence of causal
power away from the root.  The declarations reuse `Momentariness.Theory`, whose
interface also carries a `twoTimes` witness for older nonuniformity results;
the directed proofs below do not consume that field.
-/

namespace BuddhistComparativeLogic.DirectedMomentariness

open Momentariness

universe u v w

variable {D : Type u} {E : Type v} {T : Type w}

/-- A directed continuity link transports an effect from the later endpoint
back to the earlier endpoint.  No forward transport law is included. -/
structure DirectedCriterion (M : Theory D E T) where
  continues : D → T → T → Prop
  transportsToEarlier : ∀ {d e t t'}, continues d t t' →
    M.produces d e t' → M.produces d e t

/-- A finite path of directed links from a selected root to a production
time. -/
inductive DirectedChain {M : Theory D E T}
    (C : DirectedCriterion M) (d : D) : T → T → Prop
  | refl (t : T) : DirectedChain C d t t
  | tail {t u v : T} : DirectedChain C d t u → C.continues d u v →
      DirectedChain C d t v

/-- Production of one effect at the end of a directed chain can be transported
to its root.  The proof uses only the backward field of `DirectedCriterion`. -/
theorem production_at_root_of_directedChain
    {M : Theory D E T} (C : DirectedCriterion M)
    {d : D} {e : E} {root t : T}
    (chain : DirectedChain C d root t) (produced : M.produces d e t) :
    M.produces d e root := by
  induction chain with
  | refl => exact produced
  | tail prior link ih =>
      exact ih (C.transportsToEarlier link produced)

/-- If each actual production time has a directed path from the chosen root,
effect-time uniqueness makes all production punctual at that root. -/
theorem punctual_of_rooted_directedChains
    {M : Theory D E T} (C : DirectedCriterion M) {d : D} {root : T}
    (rooted : ∀ {e t}, M.produces d e t → DirectedChain C d root t) :
    M.PunctualAt d root := by
  intro e t produced
  have atRoot : M.produces d e root :=
    production_at_root_of_directedChain C (rooted produced) produced
  exact M.once produced atRoot

/-- The weaker directed-root criterion suffices for literal momentariness.
The surrounding `Theory` type includes a `twoTimes` field, but this proof uses
only efficacy, unique effect time, existence at the root, and rooted backward
transport. -/
theorem momentary_of_rooted_directedChains
    {M : Theory D E T} (C : DirectedCriterion M) {d : D} {root : T}
    (here : M.existsAt d root)
    (rooted : ∀ {e t}, M.produces d e t → DirectedChain C d root t) :
    M.Momentary d := by
  exact M.momentary_if_production_is_punctual
    (punctual_of_rooted_directedChains C rooted) here

/-! ## Relation to the earlier two-way criterion -/

/-- Forgetting forward transport turns every earlier continuity criterion into
a directed one. -/
def ofContinuityCriterion (M : Theory D E T)
    (C : M.ContinuityCriterion) : DirectedCriterion M where
  continues := C.continues
  transportsToEarlier := C.transportsBackward

theorem causalChain_to_directedChain
    (M : Theory D E T) (C : M.ContinuityCriterion) {d : D} {t t' : T}
    (chain : M.CausalChain C d t t') :
    DirectedChain (ofContinuityCriterion M C) d t t' := by
  induction chain with
  | refl => exact .refl _
  | tail prior link ih => exact .tail ih link

/-- The old rooted-chain theorem is an instance of the directed theorem. -/
theorem momentary_of_twoWay_rootedChains
    (M : Theory D E T) (C : M.ContinuityCriterion) {d : D} {root : T}
    (here : M.existsAt d root)
    (rooted : ∀ {e t}, M.produces d e t → M.CausalChain C d root t) :
    M.Momentary d := by
  apply momentary_of_rooted_directedChains (ofContinuityCriterion M C) here
  intro e t produced
  exact causalChain_to_directedChain M C (rooted produced)

/-! ## Finite strictness witness

The sole object exists only at `false` and produces one effect there.  A link
from `false` to `true` satisfies backward transport vacuously at its later
endpoint, but it cannot transport the actual root production forward. -/

def rootOnly : Theory Unit Unit Bool where
  existsAt _ t := t = false
  produces _ _ t := t = false
  efficacy _ t := by
    constructor
    · intro ht
      exact ⟨(), ht⟩
    · rintro ⟨_, ht⟩
      exact ht
  once := by
    intro d e t t' ht ht'
    exact ht.trans ht'.symm
  twoTimes := ⟨false, true, by decide⟩

/-- Directed links start at the only productive time. -/
def rootDirection : DirectedCriterion rootOnly where
  continues _ t _ := t = false
  transportsToEarlier := by
    intro d e t t' ht ht'
    exact ht

theorem rootDirection_rooted :
    ∀ {e t}, rootOnly.produces () e t →
      DirectedChain rootDirection () false t := by
  intro e t produced
  cases produced
  exact .refl false

theorem rootOnly_is_momentary : rootOnly.Momentary () := by
  exact momentary_of_rooted_directedChains rootDirection rfl
    rootDirection_rooted

/-- Forward preservation fails on a declared directed link.  Consequently the
directed criterion is strictly weaker than a two-way continuity criterion with
the same link relation.  The productive rooted chain in this separation model
is reflexive; the witness separates the assumptions and does not claim an
observed effect traverses a nontrivial link. -/
theorem directed_transport_does_not_imply_forward_transport :
    rootDirection.continues () false true ∧
      (∀ {e t}, rootOnly.produces () e t →
        DirectedChain rootDirection () false t) ∧
      ¬ (∀ {d e t t'}, rootDirection.continues d t t' →
        rootOnly.produces d e t → rootOnly.produces d e t') ∧
      rootOnly.Momentary () := by
  refine ⟨rfl, rootDirection_rooted, ?_, rootOnly_is_momentary⟩
  intro forward
  have impossible := forward (d := ()) (e := ()) (t := false) (t' := true)
    rfl rfl
  exact Bool.noConfusion impossible

end BuddhistComparativeLogic.DirectedMomentariness
