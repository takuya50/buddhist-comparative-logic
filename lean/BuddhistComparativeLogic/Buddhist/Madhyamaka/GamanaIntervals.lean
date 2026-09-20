/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Madhyamaka.Gamana

/-!
# Motion as a relation over a temporal interval

`BuddhistComparativeLogic.Buddhist.Madhyamaka.Gamana` proves that the presently occupied place is a singleton and
therefore cannot itself be traversed.  Here motion is represented positively
by a trajectory relating distinct times and positions.  The trace of a
nonconstant trajectory over a closed interval contains its two endpoints and
is consequently traversable.  This makes the static-point result compatible
with motion rather than treating a place as the bearer of motion.
-/

namespace BuddhistComparativeLogic.GamanaIntervals

open BuddhistComparativeLogic.Gamana

structure Trajectory (Time : Type u) (Place : Type v) where
  position : Time → Place

/-- The order-theoretic closed interval from `start` to `finish`. -/
def inClosedInterval (time : StrictLinearOrder Time)
    (start finish : Time) : PredSet Time :=
  fun t => (t = start ∨ time.lt start t) ∧
    (t = finish ∨ time.lt t finish)

/-- The spatial image of a trajectory during a closed time interval. -/
def intervalTrace (time : StrictLinearOrder Time)
    (trajectory : Trajectory Time Place) (start finish : Time) : PredSet Place :=
  fun p => ∃ t, inClosedInterval time start finish t ∧ trajectory.position t = p

/-- Minimal relational motion: time advances and the two observed positions
are distinct. -/
def movesBetween (time : StrictLinearOrder Time)
    (trajectory : Trajectory Time Place) (start finish : Time) : Prop :=
  time.lt start finish ∧ trajectory.position start ≠ trajectory.position finish

/-- Oriented motion also records the direction in spatial order. -/
def advances (time : StrictLinearOrder Time) (space : StrictLinearOrder Place)
    (trajectory : Trajectory Time Place) (start finish : Time) : Prop :=
  time.lt start finish ∧
    space.lt (trajectory.position start) (trajectory.position finish)

theorem start_mem_interval (time : StrictLinearOrder Time)
    {start finish : Time} (h : time.lt start finish) :
    inClosedInterval time start finish start :=
  ⟨Or.inl rfl, Or.inr h⟩

theorem finish_mem_interval (time : StrictLinearOrder Time)
    {start finish : Time} (h : time.lt start finish) :
    inClosedInterval time start finish finish :=
  ⟨Or.inr h, Or.inl rfl⟩

theorem start_mem_trace (time : StrictLinearOrder Time)
    (trajectory : Trajectory Time Place) {start finish : Time}
    (h : time.lt start finish) :
    intervalTrace time trajectory start finish (trajectory.position start) :=
  ⟨start, start_mem_interval time h, rfl⟩

theorem finish_mem_trace (time : StrictLinearOrder Time)
    (trajectory : Trajectory Time Place) {start finish : Time}
    (h : time.lt start finish) :
    intervalTrace time trajectory start finish (trajectory.position finish) :=
  ⟨finish, finish_mem_interval time h, rfl⟩

/-- Relational motion has a positively traversable spatial trace. -/
theorem interval_motion_traverses (time : StrictLinearOrder Time)
    (trajectory : Trajectory Time Place) {start finish : Time}
    (motion : movesBetween time trajectory start finish) :
    traverses (intervalTrace time trajectory start finish) := by
  exact ⟨trajectory.position start, start_mem_trace time trajectory motion.1,
    trajectory.position finish, finish_mem_trace time trajectory motion.1, motion.2⟩

theorem advances_implies_motion
    (time : StrictLinearOrder Time) (space : StrictLinearOrder Place)
    (trajectory : Trajectory Time Place) {start finish : Time}
    (h : advances time space trajectory start finish) :
    movesBetween time trajectory start finish := by
  refine ⟨h.1, ?_⟩
  intro heq
  exact space.irrefl _ (heq ▸ h.2)

/-- Oriented motion composes over adjacent intervals. -/
theorem advances_transitive
    (time : StrictLinearOrder Time) (space : StrictLinearOrder Place)
    (trajectory : Trajectory Time Place) {first middle last : Time}
    (h₁ : advances time space trajectory first middle)
    (h₂ : advances time space trajectory middle last) :
    advances time space trajectory first last :=
  ⟨time.trans h₁.1 h₂.1, space.trans h₁.2 h₂.2⟩

theorem no_zero_duration_motion (time : StrictLinearOrder Time)
    (trajectory : Trajectory Time Place) (t : Time) :
    ¬ movesBetween time trajectory t t := by
  intro h
  exact time.irrefl t h.1

/-- Every instantaneous trace is a singleton, irrespective of whether the
trajectory moves over a larger interval. -/
theorem no_traversal_at_an_instant
    (trajectory : Trajectory Time Place) (t : Time) :
    ¬ traverses (fun p => trajectory.position t = p) := by
  rintro ⟨p, hp, q, hq, hpq⟩
  exact hpq (hp.symm.trans hq)

/-- MMK's nontraversability of the current place and a traversable temporal
trace hold together.  They concern different predicates. -/
theorem point_analysis_is_compatible_with_interval_motion
    (time : StrictLinearOrder Time) (space : StrictLinearOrder Place)
    (trajectory : Trajectory Time Place) {start finish current : Time}
    (motion : movesBetween time trajectory start finish) :
    (¬ traverses (gamyamana space (trajectory.position current))) ∧
      traverses (intervalTrace time trajectory start finish) :=
  ⟨no_motion_in_gamyamana space _, interval_motion_traverses time trajectory motion⟩

/-! ## A two-time countermodel to snapshot determination -/

def boolLt (x y : Bool) : Prop := x = false ∧ y = true

theorem boolLt_irrefl (x : Bool) : ¬ boolLt x x := by
  cases x <;> simp [boolLt]

theorem boolLt_trans {x y z : Bool} :
    boolLt x y → boolLt y z → boolLt x z := by
  intro hxy hyz
  cases y with
  | false => simp [boolLt] at hxy
  | true => simp [boolLt] at hyz

theorem boolLt_trichotomy (x y : Bool) :
    boolLt x y ∨ x = y ∨ boolLt y x := by
  cases x <;> cases y <;> simp [boolLt]

def boolOrder : StrictLinearOrder Bool where
  lt := boolLt
  irrefl := by
    exact boolLt_irrefl
  trans := by
    exact boolLt_trans
  trichotomy := by
    exact boolLt_trichotomy

def movingTrajectory : Trajectory Bool Bool where
  position t := t

def stationaryTrajectory : Trajectory Bool Bool where
  position _ := true

theorem moving_trajectory_advances :
    advances boolOrder boolOrder movingTrajectory false true := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem moving_trace_is_traversed :
    traverses (intervalTrace boolOrder movingTrajectory false true) :=
  interval_motion_traverses boolOrder movingTrajectory
    (advances_implies_motion boolOrder boolOrder movingTrajectory
      moving_trajectory_advances)

/-- Two histories have the same present position, although exactly one moves
from the earlier time.  A present-place observation therefore cannot determine
the temporal motion relation. -/
theorem same_present_different_motion :
    movingTrajectory.position true = stationaryTrajectory.position true ∧
      movesBetween boolOrder movingTrajectory false true ∧
      ¬ movesBetween boolOrder stationaryTrajectory false true := by
  constructor
  · rfl
  constructor
  · exact ⟨⟨rfl, rfl⟩, by decide⟩
  · intro h
    exact h.2 rfl

end BuddhistComparativeLogic.GamanaIntervals
