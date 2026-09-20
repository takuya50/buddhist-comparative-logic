/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.MMK1
import BuddhistComparativeLogic.Core.MVLogic
import BuddhistComparativeLogic.Buddhist.Madhyamaka.DependentOrigination

/-!
# Explicit reductio obligations behind fourfold non-arising

MMK 1.1 motivates the four cases. We expose exhaustiveness and each case's
consequence as premises, not four negations presented as already proved.
The target is intrinsic production; ordinary conditional occurrence is a
different predicate and is not refuted by these rules.

The second part separates metalevel rejection from FDE formula negation
and identifies a local condition that recovers material modus tollens.
-/

namespace BuddhistComparativeLogic.Prasanga

structure Production (D : Type u) where
  intrinsic : D → Prop
  fromOrigin : D → Origin → Prop
  prior : D → D → Prop
  depends : D → D → Prop

namespace Production

variable (M : Production D)

def Exhaustive : Prop := ∀ x, M.intrinsic x → ∃ o, M.fromOrigin x o
def SelfPriority : Prop := ∀ x, M.fromOrigin x .self → M.prior x x
def StrictPriority : Prop := ∀ x, ¬ M.prior x x
def OtherIndependent : Prop :=
  ∀ x, M.fromOrigin x .other → ∀ y, ¬ M.depends y x
def OtherDependent : Prop :=
  ∀ x, M.fromOrigin x .other → ∃ y, M.depends y x
def BothIncludesSelf : Prop :=
  ∀ x, M.fromOrigin x .both → M.fromOrigin x .self
def Causeless : Prop :=
  ∀ x, M.fromOrigin x .neither → ∀ y, ¬ M.depends y x
def ProductionHasCondition : Prop :=
  ∀ x, M.fromOrigin x .neither → ∃ y, M.depends y x

/-- The case principles are a reconstruction, not an assertion that each
one follows from the bare names self, other, both and neither. -/
structure Laws : Prop where
  exhaustive : M.Exhaustive
  self_priority : M.SelfPriority
  strict_priority : M.StrictPriority
  other_independent : M.OtherIndependent
  other_dependent : M.OtherDependent
  both_self : M.BothIncludesSelf
  causeless : M.Causeless
  has_condition : M.ProductionHasCondition

theorem not_from_self (hs : M.SelfPriority) (hi : M.StrictPriority) (x : D) :
    ¬ M.fromOrigin x .self := fun h => hi x (hs x h)

theorem not_from_other (hi : M.OtherIndependent) (hd : M.OtherDependent) (x : D) :
    ¬ M.fromOrigin x .other := by
  intro h
  obtain ⟨y, hy⟩ := hd x h
  exact hi x h y hy

theorem not_from_both (hb : M.BothIncludesSelf) (hs : M.SelfPriority)
    (hi : M.StrictPriority) (x : D) : ¬ M.fromOrigin x .both :=
  fun h => M.not_from_self hs hi x (hb x h)

theorem not_from_neither (hn : M.Causeless) (hc : M.ProductionHasCondition) (x : D) :
    ¬ M.fromOrigin x .neither := by
  intro h
  obtain ⟨y, hy⟩ := hc x h
  exact hn x h y hy

theorem no_intrinsic_production (h : M.Laws) (x : D) : ¬ M.intrinsic x := by
  intro hx
  obtain ⟨o, ho⟩ := h.exhaustive x hx
  cases o with
  | self => exact M.not_from_self h.self_priority h.strict_priority x ho
  | other => exact M.not_from_other h.other_independent h.other_dependent x ho
  | both => exact M.not_from_both h.both_self h.self_priority h.strict_priority x ho
  | neither => exact M.not_from_neither h.causeless h.has_condition x ho

end Production

/-- The eliminator itself uses only exhaustiveness and rejection of each
case. It is independent of the particular reconstruction above. -/
theorem exhaustive_reductio (claim : Prop) (caseOf : Origin → Prop)
    (cover : claim → ∃ o, caseOf o) (reject : ∀ o, ¬ caseOf o) : ¬ claim := by
  intro h
  obtain ⟨o, ho⟩ := cover h
  exact reject o ho

/-- Omitting any one case leaves a model of the other three refutations. -/
theorem every_case_matters (omitted : Origin) :
    ∃ caseOf : Origin → Prop,
      (∃ o, caseOf o) ∧ (∀ o, o ≠ omitted → ¬ caseOf o) := by
  exact ⟨fun o => o = omitted, ⟨omitted, rfl⟩, fun _ h => h⟩

theorem coverage_matters :
    ∃ claim : Prop, ∃ caseOf : Origin → Prop,
      claim ∧ (∀ o, ¬ caseOf o) ∧ ¬ (claim → ∃ o, caseOf o) := by
  refine ⟨True, fun _ => False, trivial, fun _ h => h, ?_⟩
  intro h
  obtain ⟨_, bad⟩ := h trivial
  exact bad

/-- Without intrinsic independence, dependent production from another
condition survives the other seven case obligations. -/
def ordinaryOther : Production Bool where
  intrinsic _ := True
  fromOrigin _ o := o = .other
  prior _ _ := False
  depends y x := y ≠ x

theorem other_independence_is_substantive :
    ordinaryOther.Exhaustive ∧ ordinaryOther.SelfPriority ∧
    ordinaryOther.StrictPriority ∧ ordinaryOther.OtherDependent ∧
    ordinaryOther.BothIncludesSelf ∧ ordinaryOther.Causeless ∧
    ordinaryOther.ProductionHasCondition ∧ ordinaryOther.intrinsic false ∧
    ¬ ordinaryOther.OtherIndependent := by
  refine ⟨fun _ _ => ⟨.other, rfl⟩, ?_, fun _ h => h, ?_, ?_, ?_, ?_, trivial, ?_⟩
  · intro _ h; cases h
  · intro x _
    exact ⟨!x, by change (!x) ≠ x; cases x <;> decide⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h
  · intro h
    exact h false rfl true (by change true ≠ false; decide)

def conditionalWorld : Production Bool where
  intrinsic _ := False
  fromOrigin _ _ := False
  prior _ _ := False
  depends y x := y ≠ x

theorem fourfold_laws_nonvacuous : conditionalWorld.Laws := by
  constructor
  · exact fun _ h => False.elim h
  · exact fun _ h => False.elim h
  · exact fun _ h => h
  · exact fun _ h => False.elim h
  · exact fun _ h => False.elim h
  · exact fun _ h => False.elim h
  · exact fun _ h => False.elim h
  · exact fun _ h => False.elim h

theorem nonarising_preserves_conditional_edges :
    ¬ conditionalWorld.intrinsic false ∧ conditionalWorld.depends true false :=
  ⟨conditionalWorld.no_intrinsic_production fourfold_laws_nonvacuous false,
    by change true ≠ false; decide⟩

/-- Derive the disputed independence obligation from the contextual
criterion, if the other-origin claim really asserts own-being. The last
premise must not be silently added to ordinary causal production. -/
theorem other_independence_from_context (M : Production D)
    (C : DependentOrigination.ContextModel W D)
    (sameDependency : M.depends = C.depends) (invariant : C.InvariantOwn)
    (assertsOwn : ∀ x, M.fromOrigin x .other → C.own x) : M.OtherIndependent := by
  intro x hx y edge
  rw [sameDependency] at edge
  exact C.empty_of_dependency invariant edge (assertsOwn x hx)

/-! Local FDE proof rules. -/

theorem rejection_via_preservation (D : V → Prop) (p q : V)
    (rule : D p → D q) (reject : ¬ D q) : ¬ D p := fun hp => reject (rule hp)

theorem fde_material_mt_with_consistent_consequent (p q : TV4)
    (consistent : q ≠ .B)
    (imp : mvFDE.designated (disj4 (neg4 p) q))
    (nq : mvFDE.designated (neg4 q)) : mvFDE.designated (neg4 p) := by
  cases p <;> cases q <;> simp_all [mvFDE, disj4, neg4, mk, tr, fa]

/-- Exactly the glut value allows material MT to fail for a fixed
consequent. For T and N, the negated-consequent premise is unavailable. -/
theorem fde_mt_for_all_antecedents_iff (q : TV4) :
    (∀ p, mvFDE.designated (disj4 (neg4 p) q) →
      mvFDE.designated (neg4 q) → mvFDE.designated (neg4 p)) ↔ q ≠ .B := by
  constructor
  · intro h heq
    subst q
    have bad : false = true := h .T rfl rfl
    cases bad
  · exact fun h p => fde_material_mt_with_consistent_consequent p q h

/-- Discharge the four negations required by the existing MMK1 theorem
using explicit material conditionals and locally consistent consequences.
The conclusion is designated formula negation, not metalevel rejection. -/
theorem fde_fourfold_from_local_reductios (v : UtpadaAtom → TV4)
    (consequence : Origin → TV4)
    (steps : ∀ o, mvFDE.designated (disj4 (neg4 (v (.fromOrigin o))) (consequence o)))
    (denied : ∀ o, mvFDE.designated (neg4 (consequence o)))
    (consistent : ∀ o, consequence o ≠ .B) : sat4 v (.neg arises) = true := by
  apply anutpada_fde_formula v
  intro o
  exact fde_material_mt_with_consistent_consequent _ _ (consistent o) (steps o) (denied o)

/-- Undesignatedness does not entail designated negation in a gap. -/
theorem fde_rejection_without_negation :
    ¬ mvFDE.designated TV4.N ∧ ¬ mvFDE.designated (neg4 TV4.N) := by
  exact ⟨Bool.noConfusion, Bool.noConfusion⟩

theorem fde_rejection_to_negation (p : TV4) (noGap : p ≠ .N)
    (rejected : ¬ mvFDE.designated p) : mvFDE.designated (neg4 p) := by
  cases p <;> simp_all [mvFDE, neg4, mk, tr, fa]

end BuddhistComparativeLogic.Prasanga
