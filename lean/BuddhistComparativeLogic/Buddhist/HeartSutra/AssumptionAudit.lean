/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.TwoTruths
import BuddhistComparativeLogic.Buddhist.HeartSutra.PathModel

/-!
# What the emptiness and two-truths conclusions depend on

Lean-only audit, not an additional translation of a sutra clause. Independent
predicates expose the bridge from dependence to absence of own-being. The
FDE results isolate the local consistency conditions from the number of
evaluation points. None of these results selects a philological reading.
-/

namespace BuddhistComparativeLogic.AssumptionAudit

/-- Dependence and own-being are separate data, with no hidden bridge. -/
structure Dependence (D : Type u) where
  dep : D → D → Prop
  own : D → Prop

namespace Dependence

variable (M : Dependence D)

def arisen (x : D) : Prop := ∃ y, M.dep y x
def emptyOf (x : D) : Prop := ¬ M.own x
def UniversalArising : Prop := ∀ x, M.arisen x
def Exclusion : Prop := ∀ x y, M.dep y x → ¬ M.own x

/-- Only a one-way exclusion law is needed; own-being is not defined as
the complement of arising. -/
theorem empty_of_arisen (bridge : M.Exclusion) {x : D}
    (hx : M.arisen x) : M.emptyOf x := by
  obtain ⟨y, hy⟩ := hx
  exact bridge x y hy

theorem all_empty (bridge : M.Exclusion) (arising : M.UniversalArising) :
    ∀ x, M.emptyOf x := fun x => M.empty_of_arisen bridge (arising x)

/-- With universal arising fixed, the exclusion law already has the
strength of universal emptiness. This is an assumption audit, not an
independent justification of the bridge. -/
theorem all_empty_iff_exclusion (arising : M.UniversalArising) :
    (∀ x, M.emptyOf x) ↔ M.Exclusion := by
  exact ⟨fun h x _ _ => h x, fun h => M.all_empty h arising⟩

end Dependence

/-- A genuine non-self dependence edge does not on its own exclude own-being. -/
def dependentOwn : Dependence Bool where
  dep y x := y ≠ x
  own _ := True

theorem universal_arising_without_exclusion :
    dependentOwn.UniversalArising ∧ ¬ dependentOwn.emptyOf false := by
  constructor
  · intro x
    exact ⟨!x, by change (!x) ≠ x; cases x <;> decide⟩
  · exact fun h => h trivial

def independentOwn : Dependence Unit where
  dep _ _ := False
  own _ := True

theorem exclusion_without_universal_arising :
    independentOwn.Exclusion ∧ ¬ independentOwn.emptyOf () := by
  exact ⟨fun _ _ h => False.elim h, fun h => h trivial⟩

/-- A nonempty model where the law and universal arising both hold. -/
def dependentEmpty : Dependence Bool where
  dep y x := y ≠ x
  own _ := False

theorem dependence_model_nonvacuous :
    dependentEmpty.Exclusion ∧ dependentEmpty.UniversalArising := by
  constructor
  · exact fun _ _ _ h => h
  · intro x
    exact ⟨!x, by change (!x) ≠ x; cases x <;> decide⟩

def independentEmpty : Dependence Unit where
  dep _ _ := False
  own _ := False

/-- The one-way bridge permits neither arising nor own-being. Thus it does
not silently restore the old definition own = not arisen. -/
theorem exclusion_does_not_define_own :
    independentEmpty.Exclusion ∧ ¬ independentEmpty.arisen () ∧
    ¬ independentEmpty.own () := by
  refine ⟨fun _ _ h => False.elim h, ?_, fun h => h⟩
  rintro ⟨_, h⟩
  exact h

/-- Under FDE, saying the negation is designated does not say that the
original is undesignated. This distinguishes the Prop-valued audit above
from the existing many-valued notion of emptiness. -/
theorem fde_negation_is_not_exclusion :
    mvFDE.designated (neg4 TV4.B) ∧ mvFDE.designated TV4.B := ⟨rfl, rfl⟩

def notsep (appearance own : TV4) : Prop :=
  ¬ mvFDE.designated (conj4 appearance own) ∧
    ¬ mvFDE.designated (conj4 (neg4 own) (neg4 appearance))

/-- Exact pointwise dependence: given conventional appearance and ultimate
emptiness, HS06's chosen reading holds iff both relevant values are locally
consistent. No distinctness of evaluation points occurs in the statement. -/
theorem notsep_iff_local_consistency (a s : TV4)
    (ha : mvFDE.designated a) (hs : mvFDE.designated (neg4 s)) :
    notsep a s ↔
      (¬ mvFDE.designated (neg4 a) ∧ ¬ mvFDE.designated s) := by
  cases a <;> cases s <;>
    simp_all [notsep, mvFDE, neg4, conj4, mk, tr, fa]

theorem two_truths_notsep_iff (T : TwoTruths TV4) (hL : T.logic = mvFDE)
    (x : Dharma) :
    T.XNotsep x ↔
      (¬ mvFDE.designated (neg4 (T.val .samvrti x)) ∧
        ¬ mvFDE.designated (T.svAt .paramartha x)) := by
  have ha := T.conv_appears x
  have hs := T.ult_empty x
  rw [hL] at ha hs
  unfold TwoTruths.XNotsep TwoTruths.sunyaAt
  rw [hL]
  exact notsep_iff_local_consistency _ _ ha hs

/-- Retain exactly the two predicates queried by the HS06/07 readings,
while making their evaluations independent of standpoint. This projection
does not preserve arbitrary formulas querying the other coordinates. -/
def flattenQueries (T : TwoTruths V) : TwoTruths V where
  logic := T.logic
  val _ := T.val .samvrti
  svAt _ := T.svAt .paramartha
  conv_appears := T.conv_appears
  ult_empty := T.ult_empty

theorem flatten_preserves_readings (T : TwoTruths V) (x : Dharma) :
    ((flattenQueries T).XIdentity x ↔ T.XIdentity x) ∧
    ((flattenQueries T).XMutual x ↔ T.XMutual x) ∧
    ((flattenQueries T).XNotsep x ↔ T.XNotsep x) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem flatten_ignores_standpoint (T : TwoTruths V) (s t : Satya2) (x : Dharma) :
    (flattenQueries T).val s x = (flattenQueries T).val t x ∧
    (flattenQueries T).svAt s x = (flattenQueries T).svAt t x := ⟨rfl, rfl⟩

/-- A flat model already satisfies all three readings. Two different
standpoint labels are not a necessary mathematical condition for them. -/
theorem flat_model_satisfies_readings (x : Dharma) :
    (flattenQueries twoTruthsFDEConsistent.toTwoTruths).XIdentity x ∧
    (flattenQueries twoTruthsFDEConsistent.toTwoTruths).XMutual x ∧
    (flattenQueries twoTruthsFDEConsistent.toTwoTruths).XNotsep x :=
  twoTruthsFDEConsistent.two_truths_readings_coincide x

/-- Equality at one valuation is weaker than agreement at every valuation. -/
theorem value_identity_is_not_semantic_equivalence :
    (mvClassical.eval (fun _ : Bool => true) (.atom false) =
      mvClassical.eval (fun _ : Bool => true) (.atom true)) ∧
    ¬ (∀ v : Bool → Bool,
      mvClassical.eval v (.atom false) = mvClassical.eval v (.atom true)) := by
  refine ⟨rfl, ?_⟩
  intro h
  have bad : false = true := h id
  cases bad

/-- Pinpoint the equivalences in the existing definitional path layer.
The new dynamic model deliberately does not assume these equivalences. -/
theorem old_path_observations_collapse (G : GraspingModel V M) (m : M) :
    (G.fearsM m ↔ G.hinderedM m) ∧
    (G.suffersM m ↔ G.hinderedM m) ∧
    (G.invertedM m ↔ G.hinderedM m) :=
  ⟨G.fears_iff_hindered m, G.suffers_iff_hindered m, G.inverted_iff_hindered m⟩

end BuddhistComparativeLogic.AssumptionAudit
