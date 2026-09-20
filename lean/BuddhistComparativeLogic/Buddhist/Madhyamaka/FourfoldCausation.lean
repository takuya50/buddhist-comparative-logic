/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.Prasanga

/-!
# Event-level reconstruction of fourfold non-arising

This file separates an event token from its kind and time.  In particular,
a prior event of the same kind is not the very event that it produces.  The
distinction prevents the rejection of self-arising from accidentally ruling
out ordinary recurrence or conditional production.

The four exact origin profiles are exhaustive by propositional case analysis.
Their rejection is not analytic: it uses temporal priority, strictness of
priority, an occurrence condition, and the proposed meaning of intrinsic
production as independence from a numerically distinct source.  Countermodels
below show that each premise has independent work to do.
-/

namespace BuddhistComparativeLogic.FourfoldCausation

/-- Events carry a kind and a time.  `causes c e` relates event tokens, while
`intrinsic e` is kept primitive so that its proposed explication can be audited
as a separate law. -/
structure Model (E : Type u) (K : Type v) (T : Type w) where
  kind : E → K
  time : E → T
  occurs : E → Prop
  causes : E → E → Prop
  earlier : T → T → Prop
  intrinsic : E → Prop

namespace Model

variable (M : Model E K T)

def CausalPriority : Prop :=
  ∀ {c e}, M.causes c e → M.earlier (M.time c) (M.time e)

def StrictEarlier : Prop :=
  ∀ t, ¬ M.earlier t t

def IntrinsicOccurs : Prop :=
  ∀ {e}, M.intrinsic e → M.occurs e

/-- The substantive reading of own-being used in the other-origin reductio:
an intrinsically produced event cannot depend on a numerically distinct event.
This does not follow from the word `intrinsic`; it is an explicit premise. -/
def IntrinsicIndependence : Prop :=
  ∀ {e}, M.intrinsic e → ∀ {c}, c ≠ e → ¬ M.causes c e

/-- The admitted domain contains produced occurrences rather than unexplained
appearances: every occurrence has at least one causal condition. -/
def OccurrenceConditioned : Prop :=
  ∀ {e}, M.occurs e → ∃ c, M.causes c e

structure Laws : Prop where
  causalPriority : M.CausalPriority
  strictEarlier : M.StrictEarlier
  intrinsicOccurs : M.IntrinsicOccurs
  intrinsicIndependence : M.IntrinsicIndependence
  occurrenceConditioned : M.OccurrenceConditioned

def TokenSelfSource (e : E) : Prop := M.causes e e

def OtherSource (e : E) : Prop :=
  ∃ c, c ≠ e ∧ M.causes c e

def AnySource (e : E) : Prop :=
  ∃ c, M.causes c e

def NoSource (e : E) : Prop :=
  ¬ M.AnySource e

/-- Ordinary conditional production requires an occurrence and a source.  It
does not assert independence or own-being. -/
def OrdinaryConditional (e : E) : Prop :=
  M.occurs e ∧ M.AnySource e

/-- A same-kind predecessor remains a distinct event token. -/
def SameKindConditional (e : E) : Prop :=
  M.occurs e ∧ ∃ c, c ≠ e ∧ M.kind c = M.kind e ∧ M.causes c e

/-- Mutually exclusive profiles of the availability of a token-self source and
a numerically other source. -/
def ExactOrigin (e : E) : Origin → Prop
  | .self => M.TokenSelfSource e ∧ ¬ M.OtherSource e
  | .other => ¬ M.TokenSelfSource e ∧ M.OtherSource e
  | .both => M.TokenSelfSource e ∧ M.OtherSource e
  | .neither => ¬ M.TokenSelfSource e ∧ ¬ M.OtherSource e

theorem source_is_self_or_other {e : E} :
    M.AnySource e → M.TokenSelfSource e ∨ M.OtherSource e := by
  rintro ⟨c, hc⟩
  by_cases hce : c = e
  · left
    simpa [TokenSelfSource, hce] using hc
  · exact Or.inr ⟨c, hce, hc⟩

theorem exact_origin_exhaustive (e : E) : ∃ o, M.ExactOrigin e o := by
  classical
  by_cases hs : M.TokenSelfSource e
  · by_cases ho : M.OtherSource e
    · exact ⟨.both, hs, ho⟩
    · exact ⟨.self, hs, ho⟩
  · by_cases ho : M.OtherSource e
    · exact ⟨.other, hs, ho⟩
    · exact ⟨.neither, hs, ho⟩

theorem exact_origin_unique {e : E} {o p : Origin}
    (ho : M.ExactOrigin e o) (hp : M.ExactOrigin e p) : o = p := by
  cases o <;> cases p <;> simp_all [ExactOrigin]

theorem no_token_self_source (priority : M.CausalPriority)
    (strict : M.StrictEarlier) (e : E) : ¬ M.TokenSelfSource e := by
  intro hself
  exact strict (M.time e) (priority hself)

theorem intrinsic_excludes_other_source
    (independent : M.IntrinsicIndependence) {e : E}
    (hi : M.intrinsic e) : ¬ M.OtherSource e := by
  rintro ⟨c, hne, hc⟩
  exact independent hi hne hc

theorem intrinsic_has_source (occurs : M.IntrinsicOccurs)
    (conditioned : M.OccurrenceConditioned) {e : E}
    (hi : M.intrinsic e) : M.AnySource e :=
  conditioned (occurs hi)

theorem not_exact_self (priority : M.CausalPriority)
    (strict : M.StrictEarlier) (e : E) : ¬ M.ExactOrigin e .self := by
  intro h
  exact M.no_token_self_source priority strict e h.1

theorem not_exact_other (independent : M.IntrinsicIndependence)
    {e : E} (hi : M.intrinsic e) : ¬ M.ExactOrigin e .other := by
  intro h
  exact M.intrinsic_excludes_other_source independent hi h.2

/-- The both case needs no new causal principle: its self component already
conflicts with strict temporal priority. -/
theorem not_exact_both (priority : M.CausalPriority)
    (strict : M.StrictEarlier) (e : E) : ¬ M.ExactOrigin e .both := by
  intro h
  exact M.no_token_self_source priority strict e h.1

theorem not_exact_neither (occurs : M.IntrinsicOccurs)
    (conditioned : M.OccurrenceConditioned) {e : E}
    (hi : M.intrinsic e) : ¬ M.ExactOrigin e .neither := by
  intro h
  obtain ⟨c, hc⟩ := M.intrinsic_has_source occurs conditioned hi
  by_cases hce : c = e
  · subst c
    exact h.1 hc
  · exact h.2 ⟨c, hce, hc⟩

/-- Fourfold elimination using the exact, mutually exclusive profiles. -/
theorem no_intrinsic_by_four_cases (laws : M.Laws) (e : E) :
    ¬ M.intrinsic e := by
  intro hi
  obtain ⟨o, ho⟩ := M.exact_origin_exhaustive e
  cases o with
  | self => exact M.not_exact_self laws.causalPriority laws.strictEarlier e ho
  | other => exact M.not_exact_other laws.intrinsicIndependence hi ho
  | both => exact M.not_exact_both laws.causalPriority laws.strictEarlier e ho
  | neither =>
      exact M.not_exact_neither laws.intrinsicOccurs
        laws.occurrenceConditioned hi ho

/-- The same premises also expose the shorter source argument hidden inside the
fourfold presentation. -/
theorem no_intrinsic_direct (laws : M.Laws) (e : E) : ¬ M.intrinsic e := by
  intro hi
  obtain ⟨c, hc⟩ := laws.occurrenceConditioned (laws.intrinsicOccurs hi)
  by_cases hce : c = e
  · subst c
    exact laws.strictEarlier (M.time e) (laws.causalPriority hc)
  · exact laws.intrinsicIndependence hi hce hc

theorem ordinary_does_not_assert_intrinsic (laws : M.Laws) (e : E) :
    M.OrdinaryConditional e → ¬ M.intrinsic e := by
  intro _
  exact M.no_intrinsic_direct laws e

/-! An adapter derives every premise used by the earlier `Prasanga.Production`
reconstruction.  Its origin predicates record evidence and may overlap; the
`ExactOrigin` predicates above are the disjoint four-way classification. -/

def OriginEvidence (e : E) : Origin → Prop
  | .self => M.TokenSelfSource e
  | .other => M.OtherSource e
  | .both => M.TokenSelfSource e ∧ M.OtherSource e
  | .neither => M.NoSource e

def asProduction : Prasanga.Production E where
  intrinsic := M.intrinsic
  fromOrigin e o := M.intrinsic e ∧ M.OriginEvidence e o
  prior a b := M.earlier (M.time a) (M.time b)
  depends := M.causes

theorem derived_prasanga_laws (laws : M.Laws) : M.asProduction.Laws := by
  constructor
  · intro e hi
    obtain ⟨c, hc⟩ := laws.occurrenceConditioned (laws.intrinsicOccurs hi)
    by_cases hce : c = e
    · subst c
      exact ⟨.self, hi, hc⟩
    · exact ⟨.other, hi, ⟨c, hce, hc⟩⟩
  · intro e h
    exact laws.causalPriority h.2
  · intro e h
    exact laws.strictEarlier (M.time e) h
  · intro e h y
    by_cases hye : y = e
    · subst y
      exact M.no_token_self_source laws.causalPriority laws.strictEarlier e
    · exact laws.intrinsicIndependence h.1 hye
  · intro _ h
    change M.intrinsic _ ∧ M.OtherSource _ at h
    obtain ⟨c, _, hc⟩ := h.2
    exact ⟨c, hc⟩
  · intro _ h
    exact ⟨h.1, h.2.1⟩
  · intro _ h y hy
    exact h.2 ⟨y, hy⟩
  · intro e h
    exact laws.occurrenceConditioned (laws.intrinsicOccurs h.1)

theorem derived_prasanga_conclusion (laws : M.Laws) (e : E) :
    ¬ M.asProduction.intrinsic e :=
  M.asProduction.no_intrinsic_production (M.derived_prasanga_laws laws) e

end Model

/-! ## A nonvacuous ordinary causal history -/

/-- `false` is a prior event token and `true` is the produced event token.
They have the same kind, but are numerically and temporally distinct. -/
def chain : Model Bool Unit Bool where
  kind _ := ()
  time e := e
  occurs e := e = true
  causes c e := c = false ∧ e = true
  earlier s t := s = false ∧ t = true
  intrinsic _ := False

theorem chain_laws : chain.Laws := by
  constructor
  · intro _ _ h
    exact h
  · intro t h
    cases t with
    | false => cases h.2
    | true => cases h.1
  · intro _ h
    exact False.elim h
  · intro _ h
    exact False.elim h
  · intro e he
    cases e with
    | false => cases he
    | true => exact ⟨false, rfl, rfl⟩

theorem ordinary_conditional_nonvacuous : chain.OrdinaryConditional true := by
  exact ⟨rfl, ⟨false, rfl, rfl⟩⟩

theorem same_kind_conditional_nonvacuous : chain.SameKindConditional true := by
  exact ⟨rfl, false, by decide, rfl, rfl, rfl⟩

theorem same_kind_is_not_token_self :
    chain.SameKindConditional true ∧ ¬ chain.TokenSelfSource true := by
  exact ⟨same_kind_conditional_nonvacuous, by simp [Model.TokenSelfSource, chain]⟩

theorem nonarising_preserves_ordinary_production :
    (¬ chain.intrinsic true) ∧ chain.OrdinaryConditional true :=
  ⟨chain.no_intrinsic_by_four_cases chain_laws true,
    ordinary_conditional_nonvacuous⟩

/-! ## Independence audits

Each finite model below satisfies every law except the named one and contains
an intrinsic event.  Thus none of the five premises can be deleted from the
general non-intrinsic-production theorem while keeping its present vocabulary.
-/

def withoutPriority : Model Unit Unit Unit where
  kind _ := ()
  time _ := ()
  occurs _ := True
  causes _ _ := True
  earlier _ _ := False
  intrinsic _ := True

theorem causal_priority_needed :
    withoutPriority.StrictEarlier ∧
    withoutPriority.IntrinsicOccurs ∧
    withoutPriority.IntrinsicIndependence ∧
    withoutPriority.OccurrenceConditioned ∧
    withoutPriority.intrinsic () ∧
    withoutPriority.ExactOrigin () .self ∧
    ¬ withoutPriority.CausalPriority := by
  simp [Model.StrictEarlier, Model.IntrinsicOccurs,
    Model.IntrinsicIndependence, Model.OccurrenceConditioned,
    Model.ExactOrigin, Model.TokenSelfSource, Model.OtherSource,
    Model.CausalPriority, withoutPriority]

def withoutStrictness : Model Unit Unit Unit where
  kind _ := ()
  time _ := ()
  occurs _ := True
  causes _ _ := True
  earlier _ _ := True
  intrinsic _ := True

theorem strict_priority_needed :
    withoutStrictness.CausalPriority ∧
    withoutStrictness.IntrinsicOccurs ∧
    withoutStrictness.IntrinsicIndependence ∧
    withoutStrictness.OccurrenceConditioned ∧
    withoutStrictness.intrinsic () ∧
    withoutStrictness.ExactOrigin () .self ∧
    ¬ withoutStrictness.StrictEarlier := by
  simp [Model.CausalPriority, Model.IntrinsicOccurs,
    Model.IntrinsicIndependence, Model.OccurrenceConditioned,
    Model.ExactOrigin, Model.TokenSelfSource, Model.OtherSource,
    Model.StrictEarlier, withoutStrictness]

def withoutIntrinsicOccurrence : Model Unit Unit Unit where
  kind _ := ()
  time _ := ()
  occurs _ := False
  causes _ _ := False
  earlier _ _ := False
  intrinsic _ := True

theorem intrinsic_occurrence_needed :
    withoutIntrinsicOccurrence.CausalPriority ∧
    withoutIntrinsicOccurrence.StrictEarlier ∧
    withoutIntrinsicOccurrence.IntrinsicIndependence ∧
    withoutIntrinsicOccurrence.OccurrenceConditioned ∧
    withoutIntrinsicOccurrence.intrinsic () ∧
    withoutIntrinsicOccurrence.ExactOrigin () .neither ∧
    ¬ withoutIntrinsicOccurrence.IntrinsicOccurs := by
  simp [Model.CausalPriority, Model.StrictEarlier,
    Model.IntrinsicIndependence, Model.OccurrenceConditioned,
    Model.ExactOrigin, Model.TokenSelfSource, Model.OtherSource,
    Model.IntrinsicOccurs, withoutIntrinsicOccurrence]

def withoutIndependence : Model Bool Unit Bool :=
  { chain with intrinsic := fun e => e = true }

theorem intrinsic_independence_needed :
    withoutIndependence.CausalPriority ∧
    withoutIndependence.StrictEarlier ∧
    withoutIndependence.IntrinsicOccurs ∧
    withoutIndependence.OccurrenceConditioned ∧
    withoutIndependence.intrinsic true ∧
    withoutIndependence.ExactOrigin true .other ∧
    ¬ withoutIndependence.IntrinsicIndependence := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro _ _ h
    exact h
  · intro t h
    cases t <;> simp_all [withoutIndependence, chain]
  · intro e he
    exact he
  · intro e he
    cases e with
    | false => cases he
    | true => exact ⟨false, rfl, rfl⟩
  · constructor
    · simp [Model.TokenSelfSource, withoutIndependence, chain]
    · exact ⟨false, by decide, rfl, rfl⟩
  · intro h
    exact h rfl (by decide : false ≠ true) ⟨rfl, rfl⟩

def withoutCondition : Model Unit Unit Unit where
  kind _ := ()
  time _ := ()
  occurs _ := True
  causes _ _ := False
  earlier _ _ := False
  intrinsic _ := True

theorem occurrence_condition_needed :
    withoutCondition.CausalPriority ∧
    withoutCondition.StrictEarlier ∧
    withoutCondition.IntrinsicOccurs ∧
    withoutCondition.IntrinsicIndependence ∧
    withoutCondition.intrinsic () ∧
    withoutCondition.ExactOrigin () .neither ∧
    ¬ withoutCondition.OccurrenceConditioned := by
  simp [Model.CausalPriority, Model.StrictEarlier,
    Model.IntrinsicOccurs, Model.IntrinsicIndependence,
    Model.ExactOrigin, Model.TokenSelfSource, Model.OtherSource,
    Model.OccurrenceConditioned, withoutCondition]

end BuddhistComparativeLogic.FourfoldCausation
