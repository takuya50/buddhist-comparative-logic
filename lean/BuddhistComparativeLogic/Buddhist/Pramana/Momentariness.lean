/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Abhidharma.Sarvastivada

/-!
# Causal efficacy and the limit of the argument for momentariness

The argument usually summarized as `whatever exists is momentary` first
establishes a weaker conclusion under efficacy, uniqueness of an effect's
production time, and the existence of two distinct times: an existent cannot
have exactly the same causal powers at every time.  This module keeps that
conclusion separate from the further continuity and punctuality bridge needed
for literal momentariness.
-/

namespace BuddhistComparativeLogic.Momentariness

structure Theory (D : Type u) (E : Type v) (T : Type w) where
  existsAt : D → T → Prop
  produces : D → E → T → Prop
  efficacy : ∀ d t, existsAt d t ↔ ∃ e, produces d e t
  once : ∀ {d e t t'}, produces d e t → produces d e t' → t = t'
  twoTimes : ∃ t t' : T, t ≠ t'

namespace Theory

variable (M : Theory D E T)

def Efficacious (d : D) (t : T) : Prop := ∃ e, M.produces d e t

def Permanent (d : D) : Prop := ∀ t, M.existsAt d t

def IntrinsicPower (d : D) : Prop :=
  ∀ e t t', M.produces d e t ↔ M.produces d e t'

def SamePower (d : D) (t t' : T) : Prop :=
  ∀ e, M.produces d e t ↔ M.produces d e t'

def Momentary (d : D) : Prop :=
  ∃ t, M.existsAt d t ∧ ∀ t', M.existsAt d t' → t' = t

def PunctualAt (d : D) (t₀ : T) : Prop :=
  ∀ e t, M.produces d e t → t = t₀

theorem efficacious_iff_exists (d : D) (t : T) :
    M.Efficacious d t ↔ M.existsAt d t :=
  (M.efficacy d t).symm

theorem intrinsic_uniform {d : D} (h : M.IntrinsicPower d) (t t' : T) :
    M.Efficacious d t ↔ M.Efficacious d t' := by
  constructor <;> rintro ⟨e, he⟩
  · exact ⟨e, (h e t t').mp he⟩
  · exact ⟨e, (h e t' t).mp he⟩

theorem intrinsic_efficacy_all_or_none {d : D} (h : M.IntrinsicPower d) :
    (∀ t, M.Efficacious d t) ∨ (∀ t, ¬ M.Efficacious d t) := by
  obtain ⟨t₀, _⟩ := M.twoTimes
  by_cases h₀ : M.Efficacious d t₀
  · left
    intro t
    exact (M.intrinsic_uniform h t₀ t).mp h₀
  · right
    intro t ht
    exact h₀ ((M.intrinsic_uniform h t t₀).mp ht)

theorem intrinsic_produces_nothing {d : D} (h : M.IntrinsicPower d)
    (e : E) (t : T) : ¬ M.produces d e t := by
  intro hp
  obtain ⟨t₁, t₂, hne⟩ := M.twoTimes
  have hp₁ : M.produces d e t₁ := (h e t t₁).mp hp
  have hp₂ : M.produces d e t₂ := (h e t t₂).mp hp
  exact hne (M.once hp₁ hp₂)

theorem intrinsic_does_not_exist {d : D} (h : M.IntrinsicPower d) (t : T) :
    ¬ M.existsAt d t := by
  intro hex
  obtain ⟨e, he⟩ := (M.efficacy d t).mp hex
  exact M.intrinsic_produces_nothing h e t he

theorem no_permanent_uniform_thing {d : D} (h : M.IntrinsicPower d) :
    ¬ M.Permanent d := by
  intro hp
  obtain ⟨t, _⟩ := M.twoTimes
  exact M.intrinsic_does_not_exist h t (hp t)

theorem causal_nonuniformity {d : D} {t : T} (h : M.existsAt d t) :
    ¬ M.IntrinsicPower d := by
  intro hi
  exact M.intrinsic_does_not_exist hi t h

theorem power_changes {d : D} {t : T} (h : M.existsAt d t) :
    ∃ e t₁ t₂, ¬ (M.produces d e t₁ ↔ M.produces d e t₂) := by
  apply Classical.byContradiction
  intro hn
  apply M.causal_nonuniformity h
  intro e t₁ t₂
  apply Classical.byContradiction
  intro hiff
  exact hn ⟨e, t₁, t₂, hiff⟩

theorem never_same_power_throughout {d : D} {t : T}
    (h : M.existsAt d t) : ¬ ∀ t₁ t₂, M.SamePower d t₁ t₂ := by
  intro hs
  apply M.causal_nonuniformity h
  exact fun e t₁ t₂ => hs t₁ t₂ e

theorem momentary_if_production_is_punctual {d : D} {t₀ : T}
    (punctual : M.PunctualAt d t₀) (here : M.existsAt d t₀) :
    M.Momentary d := by
  refine ⟨t₀, here, ?_⟩
  intro t ht
  obtain ⟨e, he⟩ := (M.efficacy d t).mp ht
  exact punctual e t he

/-! ## Identity through causal continuity -/

structure ContinuityCriterion where
  continues : D → T → T → Prop
  transportsForward : ∀ {d e t t'}, continues d t t' →
    M.produces d e t → M.produces d e t'
  transportsBackward : ∀ {d e t t'}, continues d t t' →
    M.produces d e t' → M.produces d e t

theorem samePower_of_continuity (C : M.ContinuityCriterion)
    {d : D} {t t' : T} (h : C.continues d t t') :
    M.SamePower d t t' := by
  intro e
  exact ⟨C.transportsForward h, C.transportsBackward h⟩

/-- A finite causal chain is the reflexive-transitive closure of explicitly
declared cross-time continuity links.  No endpoint power equality is stored
in the chain. -/
inductive CausalChain (C : M.ContinuityCriterion) (d : D) : T → T → Prop
  | refl (t : T) : CausalChain C d t t
  | tail {t u v : T} : CausalChain C d t u → C.continues d u v →
      CausalChain C d t v

theorem samePower_of_causalChain (C : M.ContinuityCriterion) {d : D}
    {t t' : T} (chain : M.CausalChain C d t t') :
    M.SamePower d t t' := by
  induction chain with
  | refl =>
      intro e
      exact Iff.rfl
  | tail prior link ih =>
      intro e
      exact (ih e).trans (M.samePower_of_continuity C link e)

def NontrivialCausalChain (C : M.ContinuityCriterion)
    (d : D) (t t' : T) : Prop :=
  M.CausalChain C d t t' ∧ t ≠ t'

theorem nontrivial_causalChain_gives_samePower
    (C : M.ContinuityCriterion) {d : D} {t t' : T}
    (h : M.NontrivialCausalChain C d t t') :
    M.SamePower d t t' :=
  M.samePower_of_causalChain C h.1

/-- If every production time is connected to a chosen root time by a causal
chain, local two-way effect transport and uniqueness of an effect's time
derive punctuality at the root. -/
theorem punctual_of_rooted_causalChains
    (C : M.ContinuityCriterion) {d : D} {t₀ : T}
    (rooted : ∀ {e t}, M.produces d e t → M.CausalChain C d t₀ t) :
    M.PunctualAt d t₀ := by
  intro e t hp
  have same : M.SamePower d t₀ t :=
    M.samePower_of_causalChain C (rooted hp)
  have atRoot : M.produces d e t₀ := (same e).mpr hp
  exact M.once hp atRoot

theorem momentary_of_rooted_causalChains
    (C : M.ContinuityCriterion) {d : D} {t₀ : T}
    (here : M.existsAt d t₀)
    (rooted : ∀ {e t}, M.produces d e t → M.CausalChain C d t₀ t) :
    M.Momentary d := by
  exact M.momentary_if_production_is_punctual
    (M.punctual_of_rooted_causalChains C rooted) here

theorem no_nontrivial_causalChain_from_productive_time
    (C : M.ContinuityCriterion) {d : D} {e : E} {t t' : T}
    (hp : M.produces d e t) :
    ¬ M.NontrivialCausalChain C d t t' := by
  rintro ⟨chain, hne⟩
  have hp' : M.produces d e t' :=
    (M.samePower_of_causalChain C chain e).mp hp
  exact hne (M.once hp hp')

theorem some_continuity_breaks (C : M.ContinuityCriterion) {d : D} {t : T}
    (h : M.existsAt d t) : ∃ t₁ t₂, ¬ C.continues d t₁ t₂ := by
  apply Classical.byContradiction
  intro hn
  apply M.never_same_power_throughout h
  intro t₁ t₂
  apply M.samePower_of_continuity C
  apply Classical.byContradiction
  intro hc
  exact hn ⟨t₁, t₂, hc⟩

theorem total_causal_continuity_excludes_existence
    (C : M.ContinuityCriterion)
    (total : ∀ d t t', C.continues d t t') (d : D) (t : T) :
    ¬ M.existsAt d t := by
  intro h
  obtain ⟨t₁, t₂, hbreak⟩ := M.some_continuity_breaks C h
  exact hbreak (total d t₁ t₂)

end Theory

/-! ## Finite and infinite countermodels expose the extra premises -/

def eachMoment : Theory Unit Nat Nat where
  existsAt _ _ := True
  produces _ e t := e = t
  efficacy _ t := ⟨fun _ => ⟨t, rfl⟩, fun _ => trivial⟩
  once := fun h h' => h.symm.trans h'
  twoTimes := ⟨0, 1, by decide⟩

theorem each_moment_nonvacuous : eachMoment.Efficacious () 3 := ⟨3, rfl⟩

theorem causal_nonuniformity_is_not_yet_momentariness :
    (∀ t, eachMoment.existsAt () t) ∧
      ¬ eachMoment.IntrinsicPower () ∧
      ¬ eachMoment.Momentary () := by
  refine ⟨fun _ => trivial, ?_, ?_⟩
  · exact eachMoment.causal_nonuniformity (t := 0) trivial
  · rintro ⟨t, _, unique⟩
    have h := unique (t + 1) trivial
    omega

def temporalIdentity : eachMoment.ContinuityCriterion where
  continues _ t t' := t = t'
  transportsForward := by
    intro d e t t' h hp
    cases h
    exact hp
  transportsBackward := by
    intro d e t t' h hp
    cases h
    exact hp

theorem causal_continuity_alone_does_not_yield_momentariness :
    (∀ d t, temporalIdentity.continues d t t) ∧
      (∀ {d t t'}, temporalIdentity.continues d t t' →
        eachMoment.SamePower d t t') ∧
      ¬ eachMoment.Momentary () := by
  exact ⟨fun _ _ => rfl, eachMoment.samePower_of_continuity temporalIdentity,
    causal_nonuniformity_is_not_yet_momentariness.2.2⟩

def alwaysProduces (_ : Unit) (_ : Unit) (_ : Nat) : Prop := True

theorem without_unique_effect_time_uniform_power_is_possible :
    (∀ d t, True ↔ ∃ e, alwaysProduces d e t) ∧
      (∃ t t' : Nat, t ≠ t') ∧
      (¬ ∀ d e t t', alwaysProduces d e t → alwaysProduces d e t' → t = t') ∧
      (∀ d e t t', alwaysProduces d e t ↔ alwaysProduces d e t') := by
  refine ⟨?_, ⟨0, 1, by decide⟩, ?_, ?_⟩
  · intro d t
    exact ⟨fun _ => ⟨(), trivial⟩, fun _ => trivial⟩
  · intro h
    have := h () () 0 1 trivial trivial
    contradiction
  · intros
    exact Iff.rfl

def twoExistenceTimes : Theory Unit Bool Bool where
  existsAt _ _ := True
  produces _ e t := e = t
  efficacy _ t := ⟨fun _ => ⟨t, rfl⟩, fun _ => trivial⟩
  once := fun h h' => h.symm.trans h'
  twoTimes := ⟨false, true, by decide⟩

theorem punctuality_is_needed_for_the_last_step :
    twoExistenceTimes.existsAt () false ∧
      ¬ twoExistenceTimes.IntrinsicPower () ∧
      ¬ twoExistenceTimes.PunctualAt () false ∧
      ¬ twoExistenceTimes.Momentary () := by
  refine ⟨trivial,
    twoExistenceTimes.causal_nonuniformity (t := false) trivial, ?_, ?_⟩
  · intro hp
    have := hp true true rfl
    contradiction
  · rintro ⟨t, _, unique⟩
    cases t
    · have := unique true trivial
      contradiction
    · have := unique false trivial
      contradiction

end BuddhistComparativeLogic.Momentariness
