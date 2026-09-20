/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.DependentOrigination

/-!
# Three modes of dependence and independent criteria for own-being

This module separates causal, mereological and conceptual dependence.  They
form one indexed family, but each mode has its own contexts, support changes
and manifestations.  Thus an edge in one mode is not definitionally an edge
in either of the others.

`own` remains primitive data.  `OwnBeingCriteria` records three explicit
invariance commitments: an own-being would not vary when a causal condition,
a constituent, or a scheme of designation is varied in the admitted
contexts.  Absence of own-being is consequently proved from a witnessed
variation; it is not defined as dependence or as its complement.
-/

namespace BuddhistComparativeLogic.DependenceModes

/-- The three dependence relations used in the reconstruction. -/
inductive Mode where
  | causal
  | mereological
  | conceptual
  deriving DecidableEq, Repr

/-- A mode-indexed family of contexts.  `support` means respectively that a
condition is enabled, a constituent is included, or a designation rule is
available.  `manifest` means respectively occurrence, constitution, or
classification of the subject. -/
structure Model (D : Type u) where
  Context : Mode → Type v
  support : (m : Mode) → Context m → D → Bool
  manifest : (m : Mode) → Context m → D → Bool
  own : D → Prop

namespace Model

variable (M : Model D)

/-- Dependence at one mode is witnessed by changing one distinct support,
holding all other supports fixed, while the subject's manifestation changes. -/
def DependsAt (m : Mode) (y x : D) : Prop :=
  y ≠ x ∧ ∃ c d : M.Context m,
    M.support m c y ≠ M.support m d y ∧
    (∀ z, z ≠ y → M.support m c z = M.support m d z) ∧
    M.manifest m c x ≠ M.manifest m d x

/-- The dependence relations regarded as a single indexed family. -/
def relationFamily : Mode → D → D → Prop := fun m => M.DependsAt m

def CausallyDepends (y x : D) : Prop := M.DependsAt .causal y x
def MereologicallyDepends (y x : D) : Prop := M.DependsAt .mereological y x
def ConceptuallyDepends (y x : D) : Prop := M.DependsAt .conceptual y x

/-- Each mode projects to the earlier one-context API, so all existing
contextual results remain available without identifying the three modes. -/
def toContextModelAt (m : Mode) :
    DependentOrigination.ContextModel (M.Context m) D where
  enabled := M.support m
  present := M.manifest m
  own := M.own

theorem context_projection_preserves_dependency (m : Mode) (y x : D) :
    (M.toContextModelAt m).depends y x ↔ M.DependsAt m y x :=
  Iff.rfl

/-- The coproduct presentation retains which kind of dependence witnesses
the edge. -/
inductive DependenceWitness (y x : D) : Prop where
  | causal (edge : M.CausallyDepends y x)
  | mereological (edge : M.MereologicallyDepends y x)
  | conceptual (edge : M.ConceptuallyDepends y x)

/-- Forgetting the tag gives the union of the three relations. -/
def AnyDepends (y x : D) : Prop := ∃ m, M.DependsAt m y x

theorem anyDepends_iff_witness (y x : D) :
    M.AnyDepends y x ↔ M.DependenceWitness y x := by
  constructor
  · rintro ⟨m, edge⟩
    cases m with
    | causal => exact .causal edge
    | mereological => exact .mereological edge
    | conceptual => exact .conceptual edge
  · intro edge
    cases edge with
    | causal h => exact ⟨.causal, h⟩
    | mereological h => exact ⟨.mereological, h⟩
    | conceptual h => exact ⟨.conceptual, h⟩

/-- One criterion at one mode.  This is an implication from primitive
own-being to invariance, rather than a definition of own-being. -/
def InvariantOwnAt (m : Mode) : Prop :=
  ∀ x, M.own x → ∀ c d : M.Context m,
    M.manifest m c x = M.manifest m d x

theorem context_projection_preserves_invariance (m : Mode) :
    (M.toContextModelAt m).InvariantOwn ↔ M.InvariantOwnAt m :=
  Iff.rfl

/-- The three distinct interpretive commitments about own-being. -/
structure OwnBeingCriteria : Prop where
  causal : M.InvariantOwnAt .causal
  mereological : M.InvariantOwnAt .mereological
  conceptual : M.InvariantOwnAt .conceptual

theorem OwnBeingCriteria.at (h : M.OwnBeingCriteria) (m : Mode) :
    M.InvariantOwnAt m := by
  cases m with
  | causal => exact h.causal
  | mereological => exact h.mereological
  | conceptual => exact h.conceptual

/-- Variation of manifestation contradicts the relevant own-being
criterion, independently of how the variation was produced. -/
theorem variation_refutes_own_at (m : Mode) (h : M.InvariantOwnAt m)
    {x : D} {c d : M.Context m}
    (changes : M.manifest m c x ≠ M.manifest m d x) : ¬ M.own x := by
  intro own
  exact changes (h x own c d)

def toDependenceAt (m : Mode) : AssumptionAudit.Dependence D where
  dep := M.DependsAt m
  own := M.own

def toAnyDependence : AssumptionAudit.Dependence D where
  dep := M.AnyDepends
  own := M.own

/-- The per-mode exclusion theorem. -/
theorem dependence_excludes_own_at (m : Mode) (h : M.InvariantOwnAt m) :
    (M.toDependenceAt m).Exclusion := by
  intro x y edge
  obtain ⟨_, c, d, _, _, changes⟩ := edge
  exact M.variation_refutes_own_at m h changes

theorem causal_dependence_excludes_own (h : M.InvariantOwnAt .causal) :
    (M.toDependenceAt .causal).Exclusion :=
  M.dependence_excludes_own_at .causal h

theorem mereological_dependence_excludes_own
    (h : M.InvariantOwnAt .mereological) :
    (M.toDependenceAt .mereological).Exclusion :=
  M.dependence_excludes_own_at .mereological h

theorem conceptual_dependence_excludes_own
    (h : M.InvariantOwnAt .conceptual) :
    (M.toDependenceAt .conceptual).Exclusion :=
  M.dependence_excludes_own_at .conceptual h

/-- The family-level bridge is derived from the corresponding criterion
after the witness mode is exposed. -/
theorem any_dependence_excludes_own (h : M.OwnBeingCriteria) :
    M.toAnyDependence.Exclusion := by
  intro x y edge
  obtain ⟨m, hm⟩ := edge
  exact M.dependence_excludes_own_at m (OwnBeingCriteria.at M h m) x y hm

theorem empty_of_mode_dependency (m : Mode) (h : M.InvariantOwnAt m)
    {x y : D} (edge : M.DependsAt m y x) :
    (M.toDependenceAt m).emptyOf x :=
  (M.toDependenceAt m).empty_of_arisen
    (M.dependence_excludes_own_at m h) ⟨y, edge⟩

theorem empty_of_any_dependency (h : M.OwnBeingCriteria)
    {x y : D} (edge : M.AnyDepends y x) :
    M.toAnyDependence.emptyOf x :=
  M.toAnyDependence.empty_of_arisen
    (M.any_dependence_excludes_own h) ⟨y, edge⟩

end Model

end BuddhistComparativeLogic.DependenceModes
