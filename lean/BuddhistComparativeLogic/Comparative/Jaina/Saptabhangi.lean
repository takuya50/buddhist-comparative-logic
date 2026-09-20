/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation

/-!
# The Jaina sevenfold predication

This follows `isabelle/Comparative/Jaina/Jaina_Saptabhangi.thy` through its three readings: truth
functional, classificatory, and indexical over respects (`naya`).
-/

namespace BuddhistComparativeLogic.Saptabhangi

open BuddhistComparativeLogic
open TV4 TV5 Koti

inductive Bhanga where
  | B1 | B2 | B3 | B4 | B5 | B6 | B7
  deriving DecidableEq, Repr

open Bhanga

/-! ## Truth-functional reading -/

def bhVal (x : TV5) : Bhanga → TV5
  | .B1 => x
  | .B2 => neg5 x
  | .B3 => conj5 x (neg5 x)
  | .B4 => .E
  | .B5 => conj5 x .E
  | .B6 => conj5 (neg5 x) .E
  | .B7 => conj5 (conj5 x (neg5 x)) .E

theorem avaktavya_absorbs (x : TV5) :
    bhVal x .B4 = .E ∧ bhVal x .B5 = .E ∧
      bhVal x .B6 = .E ∧ bhVal x .B7 = .E := by
  cases x <;> simp [bhVal, conj5]

theorem bh_val_range (x : TV5) (b : Bhanga) :
    bhVal x b = x ∨ bhVal x b = neg5 x ∨
      bhVal x b = conj5 x (neg5 x) ∨ bhVal x b = .E := by
  cases b <;> simp [bhVal, conj5_E_right]

theorem saptabhangi_not_truth_functional (x : TV5) :
    B4 ≠ B5 ∧ B5 ≠ B6 ∧ B6 ≠ B7 ∧
      bhVal x B4 = bhVal x B5 ∧ bhVal x B5 = bhVal x B6 ∧
      bhVal x B6 = bhVal x B7 := by
  cases x <;> simp [bhVal, conj5]

/-- The executable form of Isabelle's cardinality bound: every one of the
seven outputs is one of four listed values. -/
theorem seven_modes_four_values (x : TV5) :
    ∀ b, bhVal x b = x ∨ bhVal x b = neg5 x ∨
      bhVal x b = conj5 x (neg5 x) ∨ bhVal x b = .E :=
  bh_val_range x

/-! ## Classificatory reading -/

def bhHolds (corner : V → Koti) (x : V) : Bhanga → Prop
  | .B1 => corner x = .K1
  | .B2 => corner x = .K2
  | .B3 => corner x = .K3
  | .B4 => corner x = .K4
  | .B5 => corner x = .K1 ∧ corner x = .K4
  | .B6 => corner x = .K2 ∧ corner x = .K4
  | .B7 => corner x = .K3 ∧ corner x = .K4

theorem mixed_modes_unsatisfiable (corner : V → Koti) (x : V) :
    ¬ bhHolds corner x B5 ∧ ¬ bhHolds corner x B6 ∧
      ¬ bhHolds corner x B7 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact (by decide : K1 ≠ K4) (h.1.symm.trans h.2)
  · intro h
    exact (by decide : K2 ≠ K4) (h.1.symm.trans h.2)
  · intro h
    exact (by decide : K3 ≠ K4) (h.1.symm.trans h.2)

theorem fde5_koti_values :
    kotiOf des5 neg5 (.fin T) = K1 ∧
      kotiOf des5 neg5 (.fin F) = K2 ∧
      kotiOf des5 neg5 (.fin B) = K3 ∧
      kotiOf des5 neg5 (.fin N) = K4 := by
  decide

theorem fde5_saptabhangi_realizable_is_catuskoti (b : Bhanga) :
    (∃ x : TV5, bhHolds (kotiOf des5 neg5) x b) ↔
      b = B1 ∨ b = B2 ∨ b = B3 ∨ b = B4 := by
  constructor
  · rintro ⟨x, hx⟩
    cases b
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact False.elim ((mixed_modes_unsatisfiable _ x).1 hx)
    · exact False.elim ((mixed_modes_unsatisfiable _ x).2.1 hx)
    · exact False.elim ((mixed_modes_unsatisfiable _ x).2.2 hx)
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨.fin T, fde5_koti_values.1⟩
    · exact ⟨.fin F, fde5_koti_values.2.1⟩
    · exact ⟨.fin B, fde5_koti_values.2.2.1⟩
    · exact ⟨.E, fifth_corner_collapses.1⟩

theorem avaktavya_is_the_fourth_corner :
    bhHolds (kotiOf des5 neg5) TV5.E B4 :=
  fifth_corner_collapses.1

theorem avaktavya_designated_is_a_glut :
    kotiOf des5D neg5 TV5.E = K3 := by
  decide

/-! ## Indexical reading -/

def astiSome (V : R → TV5) : Prop :=
  ∃ r, kotiOf des5 neg5 (V r) = K1

def nastiSome (V : R → TV5) : Prop :=
  ∃ r, kotiOf des5 neg5 (V r) = K2

def avakSome (V : R → TV5) : Prop := ∃ r, V r = .E

def nayaHolds (V : R → TV5) : Bhanga → Prop
  | .B1 => astiSome V
  | .B2 => nastiSome V
  | .B3 => astiSome V ∧ nastiSome V
  | .B4 => avakSome V
  | .B5 => astiSome V ∧ avakSome V
  | .B6 => nastiSome V ∧ avakSome V
  | .B7 => astiSome V ∧ nastiSome V ∧ avakSome V

/-- The indexical reading is cumulative: support for the seventh mode also
supports every lower mode. The seven predicates are distinguishable but are
not mutually exclusive classifications. -/
theorem seventh_mode_supports_every_mode {R : Type u} {V : R → TV5}
    (h : nayaHolds V B7) : ∀ b, nayaHolds V b := by
  intro b
  cases b <;> simp_all [nayaHolds]

theorem single_naya_mixed_unsatisfiable (x : TV5) :
    ¬ nayaHolds (fun _ : Nat => x) B5 ∧
      ¬ nayaHolds (fun _ : Nat => x) B6 ∧
      ¬ nayaHolds (fun _ : Nat => x) B7 := by
  constructor
  · rintro ⟨⟨_, hk⟩, ⟨_, he⟩⟩
    change x = E at he
    rw [he] at hk
    exact (by decide : kotiOf des5 neg5 TV5.E ≠ K1) hk
  constructor
  · rintro ⟨⟨_, hk⟩, ⟨_, he⟩⟩
    change x = E at he
    rw [he] at hk
    exact (by decide : kotiOf des5 neg5 TV5.E ≠ K2) hk
  · rintro ⟨⟨_, hk⟩, _, ⟨_, he⟩⟩
    change x = E at he
    rw [he] at hk
    exact (by decide : kotiOf des5 neg5 TV5.E ≠ K1) hk

def prims : Bhanga → Bool × Bool × Bool
  | .B1 => (true, false, false)
  | .B2 => (false, true, false)
  | .B3 => (true, true, false)
  | .B4 => (false, false, true)
  | .B5 => (true, false, true)
  | .B6 => (false, true, true)
  | .B7 => (true, true, true)

theorem prims_injective : Function.Injective prims := by
  intro b b' h
  cases b <;> cases b' <;> simp_all [prims]

theorem three_primitives_generate (t : Bool × Bool × Bool)
    (hne : t ≠ (false, false, false)) : ∃ b, prims b = t := by
  rcases t with ⟨a, n, e⟩
  cases a <;> cases n <;> cases e
  · exact False.elim (hne rfl)
  · exact ⟨B4, rfl⟩
  · exact ⟨B2, rfl⟩
  · exact ⟨B6, rfl⟩
  · exact ⟨B1, rfl⟩
  · exact ⟨B5, rfl⟩
  · exact ⟨B3, rfl⟩
  · exact ⟨B7, rfl⟩

inductive Respect3 where
  | positive | negative | ineffable
  deriving DecidableEq, Repr

open Respect3

theorem exists_respect3_iff (P : Respect3 → Prop) :
    (∃ r, P r) ↔ P .positive ∨ P .negative ∨ P .ineffable := by
  constructor
  · rintro ⟨r, hr⟩
    cases r
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hr)
  · rintro (h | h | h)
    · exact ⟨.positive, h⟩
    · exact ⟨.negative, h⟩
    · exact ⟨.ineffable, h⟩

def naya3 (a n e : Bool) : Respect3 → TV5
  | .positive => if a then .fin T else .fin B
  | .negative => if n then .fin F else .fin B
  | .ineffable => if e then .E else .fin B

theorem naya_primitives_independent (a n e : Bool) :
    (astiSome (naya3 a n e) ↔ a = true) ∧
      (nastiSome (naya3 a n e) ↔ n = true) ∧
      (avakSome (naya3 a n e) ↔ e = true) := by
  cases a <;> cases n <;> cases e <;>
    simp [astiSome, nastiSome, avakSome, exists_respect3_iff, naya3,
      kotiOf, des5, neg5, neg4, mk, tr, fa]

def wit (b : Bhanga) : Respect3 → TV5 :=
  naya3 (prims b).1 (prims b).2.1 (prims b).2.2

theorem all_seven_satisfiable (b : Bhanga) : nayaHolds (wit b) b := by
  cases b
  · exact ⟨.positive, rfl⟩
  · exact ⟨.negative, rfl⟩
  · exact ⟨⟨.positive, rfl⟩, ⟨.negative, rfl⟩⟩
  · exact ⟨.ineffable, rfl⟩
  · exact ⟨⟨.positive, rfl⟩, ⟨.ineffable, rfl⟩⟩
  · exact ⟨⟨.negative, rfl⟩, ⟨.ineffable, rfl⟩⟩
  · exact ⟨⟨.positive, rfl⟩, ⟨.negative, rfl⟩, ⟨.ineffable, rfl⟩⟩

theorem saptabhangi_separated_by_naya {b b' : Bhanga} (hne : b ≠ b') :
    nayaHolds (wit b) b ≠ nayaHolds (wit b) b' ∨
      nayaHolds (wit b') b ≠ nayaHolds (wit b') b' := by
  cases b <;> cases b' <;>
    simp_all [nayaHolds, wit, prims, astiSome, nastiSome, avakSome,
      exists_respect3_iff, naya3, kotiOf, des5, neg5, neg4, mk, tr, fa]

theorem mixed_modes_need_two_nayas {R : Type u} {V : R → TV5}
    (h : nayaHolds V B5) : ∃ r r', V r ≠ V r' := by
  rcases h with ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
  refine ⟨r, r', ?_⟩
  intro heq
  rw [heq, hr'] at hr
  exact (by decide : kotiOf des5 neg5 TV5.E ≠ K1) hr

theorem seventh_mode_needs_three_nayas {R : Type u} {V : R → TV5}
    (h : nayaHolds V B7) :
    ∃ r1 r2 r3, V r1 ≠ V r2 ∧ V r1 ≠ V r3 ∧ V r2 ≠ V r3 := by
  rcases h with ⟨⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩
  refine ⟨r1, r2, r3, ?_, ?_, ?_⟩
  · intro heq
    rw [heq] at h1
    exact (by decide : Koti.K1 ≠ Koti.K2) (h1.symm.trans h2)
  · intro heq
    rw [heq, h3] at h1
    exact (by decide : kotiOf des5 neg5 TV5.E ≠ K1) h1
  · intro heq
    rw [heq, h3] at h2
    exact (by decide : kotiOf des5 neg5 TV5.E ≠ K2) h2

/-! ## Representative subfamilies

Only the three existential supports are retained by this model. Selecting
one witness for each support therefore preserves all seven predicates,
even for an infinite family. The selection is noncomputable in general;
it preserves neither order, multiplicity, nor relations between respects.
In particular the model does not recover successive versus simultaneous
predication: its `E` support is independent of its positive/negative supports.
-/

/-- A singleton witness, or the empty list if the predicate has no witness. -/
noncomputable def supportRepresentative {R : Type u} (P : R → Prop) : List R := by
  classical
  exact if h : ∃ r, P r then [Classical.choose h] else []

theorem supportRepresentative_length {R : Type u} (P : R → Prop) :
    (supportRepresentative P).length ≤ 1 := by
  classical
  unfold supportRepresentative
  split <;> simp

theorem supportRepresentative_exists {R : Type u} (P : R → Prop) :
    (∃ r, r ∈ supportRepresentative P ∧ P r) ↔ ∃ r, P r := by
  classical
  constructor
  · rintro ⟨r, _, hr⟩
    exact ⟨r, hr⟩
  · intro h
    exact ⟨Classical.choose h, by simp [supportRepresentative, h],
      Classical.choose_spec h⟩

/-- At most one original respect is chosen for each primitive support.
No inhabitance or finiteness assumption on `R` is required. -/
noncomputable def representativeNayas {R : Type u} (V : R → TV5) : List R :=
  supportRepresentative (fun r => kotiOf des5 neg5 (V r) = K1) ++
  supportRepresentative (fun r => kotiOf des5 neg5 (V r) = K2) ++
  supportRepresentative (fun r => V r = .E)

theorem representativeNayas_length {R : Type u} (V : R → TV5) :
    (representativeNayas V).length ≤ 3 := by
  have h1 := supportRepresentative_length (fun r => kotiOf des5 neg5 (V r) = K1)
  have h2 := supportRepresentative_length (fun r => kotiOf des5 neg5 (V r) = K2)
  have h3 := supportRepresentative_length (fun r => V r = .E)
  simp only [representativeNayas, List.length_append]
  omega

theorem representativeNayas_preserve_primitives {R : Type u} (V : R → TV5) :
    let W := fun r : {r // r ∈ representativeNayas V} => V r.val
    (astiSome W ↔ astiSome V) ∧ (nastiSome W ↔ nastiSome V) ∧
      (avakSome W ↔ avakSome V) := by
  dsimp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨r, hr⟩
    exact ⟨r.val, hr⟩
  · intro h
    obtain ⟨r, hr, hp⟩ := (supportRepresentative_exists _).mpr h
    exact ⟨⟨r, by simp [representativeNayas, hr]⟩, hp⟩
  · rintro ⟨r, hr⟩
    exact ⟨r.val, hr⟩
  · intro h
    obtain ⟨r, hr, hp⟩ := (supportRepresentative_exists _).mpr h
    exact ⟨⟨r, by simp [representativeNayas, hr]⟩, hp⟩
  · rintro ⟨r, hr⟩
    exact ⟨r.val, hr⟩
  · intro h
    obtain ⟨r, hr, hp⟩ := (supportRepresentative_exists _).mpr h
    exact ⟨⟨r, by simp [representativeNayas, hr]⟩, hp⟩

/-- All seven predicates are simultaneously preserved by an actual subfamily
of at most three original respects. -/
theorem representativeNayas_preserve_all {R : Type u} (V : R → TV5) (b : Bhanga) :
    nayaHolds (fun r : {r // r ∈ representativeNayas V} => V r.val) b ↔
      nayaHolds V b := by
  obtain ⟨ha, hn, he⟩ := representativeNayas_preserve_primitives V
  cases b <;> simp only [nayaHolds, ha, hn, he]

theorem naya_small_model {R : Type u} (V : R → TV5) :
    ∃ rs : List R, rs.length ≤ 3 ∧
      ∀ b, nayaHolds (fun r : {r // r ∈ rs} => V r.val) b ↔ nayaHolds V b :=
  ⟨representativeNayas V, representativeNayas_length V, representativeNayas_preserve_all V⟩

theorem representativeNayas_eq_nil_of_no_support {R : Type u} (V : R → TV5)
    (ha : ¬ astiSome V) (hn : ¬ nastiSome V) (he : ¬ avakSome V) :
    representativeNayas V = [] := by
  simp only [astiSome] at ha
  simp only [nastiSome] at hn
  simp only [avakSome] at he
  simp [representativeNayas, supportRepresentative, ha, hn, he]

/-- Empty families are included, not padded by an artificial respect. -/
theorem representativeNayas_empty (V : Empty → TV5) : representativeNayas V = [] := by
  apply representativeNayas_eq_nil_of_no_support <;>
    rintro ⟨r, _⟩ <;> exact Empty.elim r

private theorem three_distinct_members_length {R : Type u} {rs : List R}
    {a b c : R} (ha : a ∈ rs) (hb : b ∈ rs) (hc : c ∈ rs)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ rs.length := by
  cases rs with
  | nil => simp at ha
  | cons x xs =>
    cases xs with
    | nil => simp_all
    | cons y ys =>
      cases ys with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          rcases hc with rfl | rfl <;> simp_all
      | cons z zs => simp

/-- Any representative list retaining the seventh mode needs three entries.
The argument reuses the existing separation theorem, rather than a new
interpretation of the seventh mode. -/
theorem seventh_mode_subfamily_lower_bound {R : Type u} (V : R → TV5) (rs : List R)
    (h : nayaHolds (fun r : {r // r ∈ rs} => V r.val) B7) : 3 ≤ rs.length := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := seventh_mode_needs_three_nayas h
  apply three_distinct_members_length a.property b.property c.property
  · intro heq
    exact hab (congrArg V heq)
  · intro heq
    exact hac (congrArg V heq)
  · intro heq
    exact hbc (congrArg V heq)

/-- The uniform upper bound is attained and cannot be lowered: the existing
seventh-mode witness requires exactly three representatives. -/
theorem naya_small_model_bound_sharp :
    (representativeNayas (wit B7)).length = 3 ∧
      ∀ rs : List Respect3,
        (∀ b, nayaHolds (fun r : {r // r ∈ rs} => wit B7 r.val) b ↔
          nayaHolds (wit B7) b) → 3 ≤ rs.length := by
  have h7 := all_seven_satisfiable B7
  have hlo := seventh_mode_subfamily_lower_bound (wit B7) (representativeNayas (wit B7))
    ((representativeNayas_preserve_all (wit B7) B7).mpr h7)
  have hhi := representativeNayas_length (wit B7)
  refine ⟨by omega, ?_⟩
  intro rs h
  exact seventh_mode_subfamily_lower_bound (wit B7) rs ((h B7).mpr h7)

/-! ## An explicit information-loss witness

This is a minimal modern enrichment by an observation relation, not a
formalization of historical succession or simultaneity. Forgetting that
extra relation can identify relationally different structures, even when
their valuation families themselves (not just the seven predicates) agree.
-/

structure NayaObservation (R : Type u) where
  valuation : R → TV5
  relation : R → R → Prop

def observationVariant (marked : Bool) : NayaObservation Respect3 where
  valuation := wit B7
  relation := fun r s => marked = true ∧ r = positive ∧ s = negative

theorem observation_variants_same_profile :
    ∀ b, nayaHolds (observationVariant false).valuation b ↔
      nayaHolds (observationVariant true).valuation b := by
  intro b
  rfl

theorem observation_variants_different_relation :
    ¬ (observationVariant false).relation positive negative ∧
      (observationVariant true).relation positive negative := by
  simp [observationVariant]

/-- No function of the seven-predicate profile recovers even this single
observation-relation bit on every enriched family. -/
theorem naya_profile_cannot_recover_relation :
    ¬ ∃ recover : (Bhanga → Prop) → Prop,
      ∀ O : NayaObservation Respect3,
        recover (nayaHolds O.valuation) ↔ O.relation positive negative := by
  rintro ⟨recover, h⟩
  have absent := (h (observationVariant false)).mp
  have present := (h (observationVariant true)).mpr
    observation_variants_different_relation.2
  exact observation_variants_different_relation.1 (absent present)

theorem syat_is_indexical (x : TV5) :
    ¬ bhHolds (kotiOf des5 neg5) x B5 ∧ nayaHolds (wit B5) B5 :=
  ⟨(mixed_modes_unsatisfiable _ _).1, all_seven_satisfiable B5⟩

end BuddhistComparativeLogic.Saptabhangi
