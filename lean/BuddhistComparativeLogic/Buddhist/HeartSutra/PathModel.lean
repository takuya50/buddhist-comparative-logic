/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.Path

/-!
# A grasping model for the path layer

Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_PathModel.thy`.  The model derives the eight path
conditions from predicates for grasping, seeing emptiness, and
impermanence.  The only substantive bridge field is that a dharma seen as
empty is not grasped.
-/

namespace BuddhistComparativeLogic

/-- Explicit-record counterpart of Isabelle's `grasping_model` locale. -/
structure GraspingModel (V : Type u) (M : Type v) extends Emptiness V where
  grasp : M → Dharma → Prop
  sees : M → Dharma → Prop
  anitya : Dharma → Prop
  buddha : Kala → M → Prop
  avalokitesvara : M
  no_grasp_when_seen : ∀ {m d}, sees m d → ¬ grasp m d
  sarva_anitya : ∀ d, anitya d
  avalokitesvara_sees : ∀ d, sees avalokitesvara d
  buddha_sees : ∀ {t b d}, buddha t b → sees b d

namespace GraspingModel

variable (G : GraspingModel V M)

def reliesPrajnaM (m : M) : Prop := ∀ d, G.sees m d

def hinderedM (m : M) : Prop := ∃ d, G.grasp m d

def fearsM (m : M) : Prop := ∃ d, G.grasp m d ∧ G.anitya d

def invertedM (m : M) : Prop :=
  ∃ d, G.grasp m d ∧ G.toEmptiness.emptyOf d

def nirvanaM (m : M) : Prop := ∀ d, ¬ G.grasp m d

def suffersM (m : M) : Prop := ∃ d, G.grasp m d ∧ G.anitya d

def bodhiM (m : M) : Prop := G.reliesPrajnaM m ∧ G.nirvanaM m

theorem relies_no_grasp {m : M} (h : G.reliesPrajnaM m) : G.nirvanaM m := by
  intro d
  exact G.no_grasp_when_seen (h d)

theorem inverted_iff_hindered (m : M) : G.invertedM m ↔ G.hinderedM m := by
  constructor
  · rintro ⟨d, hd, _⟩
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, hd, G.toEmptiness.sarva_dharma_sunya d⟩

theorem fears_iff_hindered (m : M) : G.fearsM m ↔ G.hinderedM m := by
  constructor
  · rintro ⟨d, hd, _⟩
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, hd, G.sarva_anitya d⟩

theorem suffers_iff_hindered (m : M) : G.suffersM m ↔ G.hinderedM m := by
  constructor
  · rintro ⟨d, hd, _⟩
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, hd, G.sarva_anitya d⟩

/-- The derived `BodhisattvaPath` instance, corresponding to Isabelle's
`sublocale path`. -/
def toPath : BodhisattvaPath V M where
  toEmptiness := G.toEmptiness
  reliesPrajna := G.reliesPrajnaM
  hindered := G.hinderedM
  fears := G.fearsM
  inverted := G.invertedM
  nirvana := G.nirvanaM
  suffers := G.suffersM
  bodhi := G.bodhiM
  buddha := G.buddha
  avalokitesvara := G.avalokitesvara
  hs02 := fun d => G.avalokitesvara_sees d
  hs20_21a := by
    intro m hRel hHind
    rcases hHind with ⟨d, hd⟩
    exact G.no_grasp_when_seen (hRel d) hd
  hs21b := by
    intro m hH hFear
    exact hH ((G.fears_iff_hindered m).mp hFear)
  hs22a := by
    intro m hH hInv
    exact hH ((G.inverted_iff_hindered m).mp hInv)
  hs22b := by
    intro m hNotInv d hd
    apply hNotInv
    exact ⟨d, hd, G.toEmptiness.sarva_dharma_sunya d⟩
  hs04_26 := by
    intro m hN hS
    rcases hS with ⟨d, hd, _⟩
    exact hN d hd
  hs23 := by
    intro t b hB d
    exact G.buddha_sees hB
  hs24 := by
    intro t b _ hRel
    exact ⟨hRel, G.relies_no_grasp hRel⟩

theorem derived_chain {m : M} (h : G.reliesPrajnaM m) :
    ¬ G.hinderedM m ∧ ¬ G.fearsM m ∧ ¬ G.invertedM m ∧
      G.nirvanaM m ∧ ¬ G.suffersM m := by
  exact G.toPath.hs21_22_chain h

theorem chain_converses (m : M) :
    (G.fearsM m → G.hinderedM m) ∧
    (G.nirvanaM m →
      ¬ G.invertedM m ∧ ¬ G.fearsM m ∧ ¬ G.suffersM m) := by
  constructor
  · exact fun h => (G.fears_iff_hindered m).mp h
  · intro hN
    constructor
    · intro hI
      rcases (G.inverted_iff_hindered m).mp hI with ⟨d, hd⟩
      exact hN d hd
    · constructor
      · intro hF
        rcases (G.fears_iff_hindered m).mp hF with ⟨d, hd⟩
        exact hN d hd
      · intro hS
        rcases (G.suffers_iff_hindered m).mp hS with ⟨d, hd⟩
        exact hN d hd

end GraspingModel

/-- Two ungrasping minds, only `true` seeing every dharma. -/
def twoMinds : GraspingModel Bool Bool where
  toEmptiness := classicalEmptiness
  grasp _ _ := False
  sees m _ := m = true
  anitya _ := True
  buddha _ m := m = true
  avalokitesvara := true
  no_grasp_when_seen _ := id
  sarva_anitya _ := trivial
  avalokitesvara_sees _ := rfl
  buddha_sees h := h

theorem grasping_model_nonvacuous : Nonempty (GraspingModel Bool Bool) :=
  ⟨twoMinds⟩

theorem nirvana_without_prajna :
    twoMinds.nirvanaM false ∧ ¬ twoMinds.reliesPrajnaM false := by
  constructor
  · intro d h
    exact h
  · intro h
    have := h Dharma.jnana
    contradiction

end BuddhistComparativeLogic
