/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.Emptiness

/-!
# The path clauses HS20--HS26

This is the explicit-record counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Path.thy`.  Its implication
fields are the sutra's own claims.  The theorems below establish only that
those implications compose.
-/

namespace BuddhistComparativeLogic

inductive Kala where
  | past | present | future
  deriving DecidableEq, Repr

/-- Isabelle's `bodhisattva_path` locale. -/
structure BodhisattvaPath (V : Type u) (M : Type v) extends Emptiness V where
  reliesPrajna : M → Prop
  hindered : M → Prop
  fears : M → Prop
  inverted : M → Prop
  nirvana : M → Prop
  suffers : M → Prop
  bodhi : M → Prop
  buddha : Kala → M → Prop
  avalokitesvara : M
  hs02 : reliesPrajna avalokitesvara
  hs20_21a : ∀ m, reliesPrajna m → ¬ hindered m
  hs21b : ∀ m, ¬ hindered m → ¬ fears m
  hs22a : ∀ m, ¬ hindered m → ¬ inverted m
  hs22b : ∀ m, ¬ inverted m → nirvana m
  hs04_26 : ∀ m, nirvana m → ¬ suffers m
  hs23 : ∀ t b, buddha t b → reliesPrajna b
  hs24 : ∀ t b, buddha t b → reliesPrajna b → bodhi b

namespace BodhisattvaPath

variable (P : BodhisattvaPath V M)

theorem hs21_22_chain {m : M} (h : P.reliesPrajna m) :
    ¬ P.hindered m ∧ ¬ P.fears m ∧ ¬ P.inverted m ∧
      P.nirvana m ∧ ¬ P.suffers m := by
  have hH := P.hs20_21a m h
  have hF := P.hs21b m hH
  have hI := P.hs22a m hH
  have hN := P.hs22b m hI
  have hS := P.hs04_26 m hN
  exact ⟨hH, hF, hI, hN, hS⟩

theorem hs23_24_three_times {t : Kala} {b : M} (h : P.buddha t b) :
    P.bodhi b := by
  exact P.hs24 t b h (P.hs23 t b h)

theorem hs01_04_avalokitesvara :
    P.nirvana P.avalokitesvara ∧ ¬ P.suffers P.avalokitesvara := by
  have h := P.hs21_22_chain P.hs02
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

end BodhisattvaPath

/-- A one-mind witness discharging every path assumption. -/
def pathConsistent : BodhisattvaPath Bool Unit where
  toEmptiness := classicalEmptiness
  reliesPrajna _ := True
  hindered _ := False
  fears _ := False
  inverted _ := False
  nirvana _ := True
  suffers _ := False
  bodhi _ := True
  buddha _ _ := True
  avalokitesvara := ()
  hs02 := trivial
  hs20_21a _ _ := id
  hs21b _ _ := id
  hs22a _ _ := id
  hs22b _ _ := trivial
  hs04_26 _ _ := id
  hs23 _ _ _ := trivial
  hs24 _ _ _ _ := trivial

theorem bodhisattva_path_nonvacuous :
    Nonempty (BodhisattvaPath Bool Unit) :=
  ⟨pathConsistent⟩

end BuddhistComparativeLogic
