/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.PathDynamics

/-!
# The argument from possible cessation against fixed suffering

Reconstruction of one argument discussed in MMK 24: suffering with a fixed
unchanging nature cannot cease. Connect that reasoning to the previously
checked dynamic path, without equating emptiness with a successful path.
The interpretation of intrinsic suffering as unchanging along this process
is an explicit criterion; no psychological law is claimed as a fact.
-/

namespace BuddhistComparativeLogic.CessationArgument

open PathDynamics

def RigidAt (P : Process S) (s : S) : Prop :=
  ∀ n, P.suffering (P.run s n) = P.suffering s

theorem positive_rigid_suffering_cannot_cease (P : Process S) (s : S)
    (rigid : RigidAt P s) (positive : 0 < P.suffering s) (n : Nat) :
    P.suffering (P.run s n) ≠ 0 := by
  rw [rigid n]
  exact Nat.ne_of_gt positive

theorem cessation_refutes_rigidity (P : Process S) (s : S)
    (positive : 0 < P.suffering s)
    (cessation : ∃ n, P.suffering (P.run s n) = 0) : ¬ RigidAt P s := by
  intro rigid
  obtain ⟨n, hn⟩ := cessation
  exact positive_rigid_suffering_cannot_cease P s rigid positive n hn

/-- The previous path theorem now discharges an actual premise of the
cessation argument, under its explicitly stated dynamics. -/
theorem path_refutes_rigidity (P : Process S) (h : P.Laws) (s : S)
    (insight : P.insight s) (positive : 0 < P.suffering s) : ¬ RigidAt P s := by
  apply cessation_refutes_rigidity P s positive
  exact ⟨P.grasp s + 2, (P.eventual_release h insight _ (Nat.le_refl _)).2.2⟩

/-- Own-being remains an independent predicate. The criterion is the
interpretive commitment linking it to unchanging suffering. -/
theorem path_refutes_intrinsic_suffering (P : Process S) (h : P.Laws)
    (own : S → Prop) (criterion : ∀ s, own s → RigidAt P s)
    (s : S) (insight : P.insight s) (positive : 0 < P.suffering s) : ¬ own s :=
  fun hs => path_refutes_rigidity P h s insight positive (criterion s hs)

theorem delayed_path_is_a_witness :
    delayed.Laws ∧ delayed.insight start ∧
    0 < delayed.suffering start ∧ ¬ RigidAt delayed start :=
  ⟨delayed_laws, rfl, by decide,
    path_refutes_rigidity delayed delayed_laws start rfl (by decide)⟩

/-- Vanishing suffering that was already zero does not refute rigidity. -/
def alreadyZero : Process Unit where
  step := id
  insight _ := True
  grasp _ := 0
  fear _ := 0
  suffering _ := 0

theorem positive_initial_suffering_needed :
    RigidAt alreadyZero () ∧
    (∀ n, alreadyZero.suffering (alreadyZero.run () n) = 0) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Refusing intrinsic nature does not on its own establish any update
law, so it cannot be used as a sufficient premise for release. -/
theorem no_intrinsic_suffering_does_not_guarantee_release :
    ∃ own : Unit → Prop,
      (∀ s, own s → RigidAt stalled s) ∧ ¬ own () ∧
      (∀ n, stalled.suffering (stalled.run () n) = 1) :=
  ⟨fun _ => False, fun _ h => False.elim h, fun h => h, fun _ => rfl⟩

end BuddhistComparativeLogic.CessationArgument
