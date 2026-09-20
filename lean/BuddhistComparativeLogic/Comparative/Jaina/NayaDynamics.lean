/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Comparative.Jaina.Saptabhangi

/-!
# Ordered observation traces for the seven naya

`BuddhistComparativeLogic.Comparative.Jaina.Saptabhangi` separates the seven modes by quantifying over three
respects.  This module adds an ordered observation layer.  A trace records the
respects actually entered; observation is accumulated monotonically, and a
mode is exactly licensed when the trace has acquired its primitive profile.

The construction is deliberately small.  It proves what an ordered route
through respects contributes without postulating a transition relation or a
historically privileged order.
-/

namespace BuddhistComparativeLogic.Saptabhangi.Dynamics

open BuddhistComparativeLogic
open BuddhistComparativeLogic.Saptabhangi
open Respect3 Bhanga

abbrev Profile := Bool × Bool × Bool

def mark : Respect3 → Profile
  | .positive => (true, false, false)
  | .negative => (false, true, false)
  | .ineffable => (false, false, true)

def join (x y : Profile) : Profile :=
  (x.1 || y.1, x.2.1 || y.2.1, x.2.2 || y.2.2)

def observed : List Respect3 → Profile
  | [] => (false, false, false)
  | r :: rs => join (mark r) (observed rs)

/-- Exact licensing records that the accumulated profile has precisely the
three primitive coordinates of the mode, with no additional respect seen. -/
def ExactlyLicenses (trace : List Respect3) (b : Bhanga) : Prop :=
  observed trace = prims b

/-- Compatibility name for the original exact-profile predicate. -/
abbrev Licenses := ExactlyLicenses

def route : Bhanga → List Respect3
  | .B1 => [.positive]
  | .B2 => [.negative]
  | .B3 => [.positive, .negative]
  | .B4 => [.ineffable]
  | .B5 => [.positive, .ineffable]
  | .B6 => [.negative, .ineffable]
  | .B7 => [.positive, .negative, .ineffable]

theorem observed_append (xs ys : List Respect3) :
    observed (xs ++ ys) = join (observed xs) (observed ys) := by
  induction xs with
  | nil =>
      rcases h : observed ys with ⟨a, n, e⟩
      simp [observed, join, h]
  | cons r rs ih =>
      cases r <;>
        simp [observed, join, ih, Bool.or_assoc]

theorem observation_idempotent (trace : List Respect3) (r : Respect3) :
    observed (r :: r :: trace) = observed (r :: trace) := by
  cases r <;> simp [observed, join]

theorem route_profile (b : Bhanga) : observed (route b) = prims b := by
  cases b <;> decide

theorem every_mode_has_an_exact_route (b : Bhanga) : Licenses (route b) b :=
  route_profile b

def accumulatedValuation (trace : List Respect3) : Respect3 → TV5 :=
  naya3 (observed trace).1 (observed trace).2.1 (observed trace).2.2

theorem route_realizes_mode (b : Bhanga) :
    nayaHolds (accumulatedValuation (route b)) b := by
  cases b <;>
    simp [accumulatedValuation, route, observed, join, mark, nayaHolds,
      astiSome, nastiSome, avakSome, exists_respect3_iff, naya3,
      kotiOf, des5, neg5, neg4, BuddhistComparativeLogic.mk, tr, fa]

def Seen (r : Respect3) (trace : List Respect3) : Prop := r ∈ trace

theorem observed_positive_iff (trace : List Respect3) :
    (observed trace).1 = true ↔ Seen .positive trace := by
  induction trace with
  | nil => simp [observed, Seen]
  | cons r rs ih =>
      cases r <;> simp [observed, join, mark, Seen, ih]

theorem observed_negative_iff (trace : List Respect3) :
    (observed trace).2.1 = true ↔ Seen .negative trace := by
  induction trace with
  | nil => simp [observed, Seen]
  | cons r rs ih =>
      cases r <;> simp [observed, join, mark, Seen, ih]

theorem observed_ineffable_iff (trace : List Respect3) :
    (observed trace).2.2 = true ↔ Seen .ineffable trace := by
  induction trace with
  | nil => simp [observed, Seen]
  | cons r rs ih =>
      cases r <;> simp [observed, join, mark, Seen, ih]

theorem licenses_iff_exact_respects (trace : List Respect3) (b : Bhanga) :
    Licenses trace b ↔
      (Seen .positive trace ↔ (prims b).1 = true) ∧
      (Seen .negative trace ↔ (prims b).2.1 = true) ∧
      (Seen .ineffable trace ↔ (prims b).2.2 = true) := by
  rw [Licenses]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun x : Profile => x.2.1) h
    have h3 := congrArg (fun x : Profile => x.2.2) h
    exact ⟨(observed_positive_iff trace).symm.trans (eq_iff_iff.mp
      (congrArg (fun q : Bool => q = true) h1)),
      (observed_negative_iff trace).symm.trans (eq_iff_iff.mp
        (congrArg (fun q : Bool => q = true) h2)),
      (observed_ineffable_iff trace).symm.trans (eq_iff_iff.mp
        (congrArg (fun q : Bool => q = true) h3))⟩
  · rintro ⟨hp, hn, he⟩
    apply Prod.ext
    · apply Bool.eq_iff_iff.mpr
      exact (observed_positive_iff trace).trans hp
    · apply Prod.ext
      · apply Bool.eq_iff_iff.mpr
        exact (observed_negative_iff trace).trans hn
      · apply Bool.eq_iff_iff.mpr
        exact (observed_ineffable_iff trace).trans he

theorem seventh_mode_requires_all_respects {trace : List Respect3}
    (h : Licenses trace .B7) :
    Seen .positive trace ∧ Seen .negative trace ∧ Seen .ineffable trace := by
  have exactness := (licenses_iff_exact_respects trace .B7).mp h
  simpa [prims] using exactness

theorem no_single_respect_trace_licenses_a_mixed_mode (r : Respect3) :
    ¬ Licenses [r] .B5 ∧ ¬ Licenses [r] .B6 ∧ ¬ Licenses [r] .B7 := by
  cases r <;> simp [ExactlyLicenses, observed, join, mark, prims]

theorem two_distinct_respects_need_two_steps {trace : List Respect3}
    {r s : Respect3} (hr : Seen r trace) (hs : Seen s trace) (hne : r ≠ s) :
    2 ≤ trace.length := by
  cases trace with
  | nil => simp [Seen] at hr
  | cons x xs =>
      cases xs with
      | nil =>
          simp [Seen] at hr hs
          exact False.elim (hne (hr.trans hs.symm))
      | cons y ys => simp

theorem three_respects_need_three_steps {trace : List Respect3}
    (hp : Seen .positive trace) (hn : Seen .negative trace)
    (he : Seen .ineffable trace) : 3 ≤ trace.length := by
  cases trace with
  | nil => simp [Seen] at hp
  | cons x xs =>
      cases xs with
      | nil =>
          cases x <;> simp [Seen] at hp hn he
      | cons y ys =>
          cases ys with
          | nil =>
              cases x <;> cases y <;> simp [Seen] at hp hn he
          | cons z zs => simp

theorem route_is_length_minimal {trace : List Respect3} {b : Bhanga}
    (h : Licenses trace b) : (route b).length ≤ trace.length := by
  have exactness := (licenses_iff_exact_respects trace b).mp h
  cases b
  · have hpos := List.length_pos_of_mem (exactness.1.mpr rfl)
    simpa [route] using (Nat.succ_le_iff.mpr hpos)
  · have hpos := List.length_pos_of_mem (exactness.2.1.mpr rfl)
    simpa [route] using (Nat.succ_le_iff.mpr hpos)
  · exact two_distinct_respects_need_two_steps
      (exactness.1.mpr rfl) (exactness.2.1.mpr rfl) (by decide)
  · have hpos := List.length_pos_of_mem (exactness.2.2.mpr rfl)
    simpa [route] using (Nat.succ_le_iff.mpr hpos)
  · exact two_distinct_respects_need_two_steps
      (exactness.1.mpr rfl) (exactness.2.2.mpr rfl) (by decide)
  · exact two_distinct_respects_need_two_steps
      (exactness.2.1.mpr rfl) (exactness.2.2.mpr rfl) (by decide)
  · have hp := exactness.1.mpr rfl
    have hn := exactness.2.1.mpr rfl
    have he := exactness.2.2.mpr rfl
    exact three_respects_need_three_steps hp hn he

/-! ## Monotone support

Exact licensing is intentionally not monotone: entering an additional respect
changes the exact profile.  `Supports` records the weaker, monotone claim that
every primitive coordinate required by a mode has already been observed.
-/

def profileIncluded (required observed : Profile) : Prop :=
  (required.1 = true → observed.1 = true) ∧
  (required.2.1 = true → observed.2.1 = true) ∧
  (required.2.2 = true → observed.2.2 = true)

def Supports (trace : List Respect3) (b : Bhanga) : Prop :=
  profileIncluded (prims b) (observed trace)

theorem supports_iff_required_respects (trace : List Respect3) (b : Bhanga) :
    Supports trace b ↔
      ((prims b).1 = true → Seen .positive trace) ∧
      ((prims b).2.1 = true → Seen .negative trace) ∧
      ((prims b).2.2 = true → Seen .ineffable trace) := by
  unfold Supports profileIncluded
  rw [observed_positive_iff, observed_negative_iff,
    observed_ineffable_iff]

theorem exactlyLicenses_implies_supports {trace : List Respect3} {b : Bhanga}
    (h : ExactlyLicenses trace b) : Supports trace b := by
  unfold ExactlyLicenses Supports profileIncluded at *
  rw [h]
  exact ⟨fun hp => hp, fun hn => hn, fun he => he⟩

/-- Once supported, a mode remains supported when observations are appended. -/
theorem supports_append_left {trace : List Respect3} {b : Bhanga}
    (h : Supports trace b) (later : List Respect3) :
    Supports (trace ++ later) b := by
  rw [supports_iff_required_respects] at h ⊢
  rcases h with ⟨hp, hn, he⟩
  refine ⟨?_, ?_, ?_⟩
  · intro required
    have seen := hp required
    change .positive ∈ trace ++ later
    exact List.mem_append.mpr (Or.inl seen)
  · intro required
    have seen := hn required
    change .negative ∈ trace ++ later
    exact List.mem_append.mpr (Or.inl seen)
  · intro required
    have seen := he required
    change .ineffable ∈ trace ++ later
    exact List.mem_append.mpr (Or.inl seen)

/-- A supported suffix also remains supported when earlier observations are
prefixed. -/
theorem supports_append_right (earlier : List Respect3)
    {trace : List Respect3} {b : Bhanga} (h : Supports trace b) :
    Supports (earlier ++ trace) b := by
  rw [supports_iff_required_respects] at h ⊢
  rcases h with ⟨hp, hn, he⟩
  refine ⟨?_, ?_, ?_⟩
  · intro required
    have seen := hp required
    change .positive ∈ earlier ++ trace
    exact List.mem_append.mpr (Or.inr seen)
  · intro required
    have seen := hn required
    change .negative ∈ earlier ++ trace
    exact List.mem_append.mpr (Or.inr seen)
  · intro required
    have seen := he required
    change .ineffable ∈ earlier ++ trace
    exact List.mem_append.mpr (Or.inr seen)

theorem route_supports_mode (b : Bhanga) : Supports (route b) b :=
  exactlyLicenses_implies_supports (route_profile b)

/-- The original predicate remains exact: adding a new respect may preserve
support while ending exact licensing. -/
theorem exact_license_need_not_persist :
    ExactlyLicenses [.positive] .B1 ∧
      Supports [.positive, .negative] .B1 ∧
      ¬ ExactlyLicenses [.positive, .negative] .B1 := by
  simp [ExactlyLicenses, Supports, profileIncluded, observed, join, mark, prims]

end BuddhistComparativeLogic.Saptabhangi.Dynamics
