/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Blocks

/-! Time intervals, tape blocks and schedules of a concrete choice-string run. -/

namespace ComplexityTests.HPVBlocks

open Turing MultiTapeMachine

/-- On one work tape, write the coin and move right on `true`, left on `false`. The input head
moves right on `true` too. -/
private def zigzag : MultiTapePTM 1 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := if bit then 1 else 0,
      workTapes := fun _ => (some (some bit), if bit then 1 else -1),
      output := none, state := some () }
    Empty.elim Empty.elim

/-- Replays on upstream configurations, evaluated through the computable interpreter. -/
private theorem stepCoins_eq (coins : List Bool) (cfg : Cfg 1 Bool Unit [true, false]) :
    zigzag.stepCoins coins cfg =
      (zigzag.runClosedConfigFromCoins coins { tapes := cfg }).tapes :=
  (MultiTapePTM.tapes_runClosedConfigFromCoins zigzag coins { tapes := cfg }).symm

private def start : Cfg 1 Bool Unit [true, false] := Cfg.init () [true, false]

private def coins : List Bool := [true, true, true, false, true, true]

-- The work head visits 0, 1, 2, 3, 2, 3, 4; the input head is clamped at the right boundary.
example : ((zigzag.stepCoins coins start).headPos (some 0),
    (zigzag.stepCoins coins start).headPos none) = (4, 2) := by
  rw [stepCoins_eq]
  rfl

-- With blocks of length 2, the work head starts intervals 0, 1, 2, 3 in blocks 0, 1, 1, 2.
example : (List.range 4).map
    (fun i => (zigzag.intervalStart 2 coins start i).headPos (some 0) / 2) = [0, 1, 1, 2] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, MultiTapePTM.intervalStart,
    stepCoins_eq]
  rfl

-- So the schedule of the work head is `(1, 0, 1)`; the input head moves right then stays.
example : (List.ofFn fun i : Fin 3 => (zigzag.schedule 2 3 coins start i (some 0) : ℤ)) =
    [1, 0, 1] ∧
    (List.ofFn fun i : Fin 3 => (zigzag.schedule 2 3 coins start i none : ℤ)) = [1, 0, 0] := by
  simp only [List.ofFn_succ, List.ofFn_zero, MultiTapePTM.coe_schedule zigzag two_pos,
    MultiTapePTM.intervalStart, stepCoins_eq]
  constructor <;> rfl

-- The block index at the end is recovered from the schedule.
example : (zigzag.intervalStart 2 coins start 3).headPos (some 0) / (2 : ℕ) = 2 := by
  rw [zigzag.blockIndex_intervalStart two_pos coins start (some 0) le_rfl, Fin.sum_univ_three]
  simp only [MultiTapePTM.coe_schedule zigzag two_pos, MultiTapePTM.intervalStart, stepCoins_eq]
  rfl

-- There are `3 ^ 6` schedules of three intervals for the input head and one work head.
example : Fintype.card (MultiTapePTM.Schedule 1 3) = 729 := by
  rw [MultiTapePTM.card_schedule]
  norm_num

/-! ### Three blocks -/

/-- After one bit the work head is at offset `1` of block `0`, with blocks of length `2`. -/
private theorem headPos_one : (zigzag.stepCoins [true] start).headPos (some 0) = 1 := by
  rw [stepCoins_eq]
  rfl

-- Within two more bits it stays in blocks `-1, 0, 1`: here it reaches block `1`.
example : (zigzag.stepCoins [true, true] (zigzag.stepCoins [true] start)).headPos (some 0) = 3 ∧
    (3 : ℤ) ∈ Set.Ico (2 * (1 / 2 - 1)) (2 * (1 / 2 + 2)) := by
  refine ⟨?_, by decide⟩
  rw [← MultiTapePTM.stepCoins_append, stepCoins_eq]
  rfl

-- The bound needs at most `b` bits: three bits leave the three blocks.
example : (zigzag.stepCoins [true, true, true] (zigzag.stepCoins [true] start)).headPos (some 0) ∉
    Set.Ico (2 * ((zigzag.stepCoins [true] start).headPos (some 0) / 2 - 1))
      (2 * ((zigzag.stepCoins [true] start).headPos (some 0) / 2 + 2)) := by
  rw [headPos_one, ← MultiTapePTM.stepCoins_append, stepCoins_eq]
  decide

/-! ### Locality -/

/-- The start configuration with a written cell outside its window `[-2, 4)`. -/
private def marked : Cfg 1 Bool Unit [true, false] :=
  { start with workTapes := fun _ z => if z = 5 then some false else none }

private theorem agreeOn_marked : start.AgreeOn (start.blockWindow 2) marked :=
  ⟨rfl, rfl, rfl, fun _ z hz => by
    simp only [Cfg.blockWindow, start, Cfg.init, Set.mem_Ico] at hz
    simp [marked, start, show z ≠ 5 by omega]⟩

-- A window cell written by the run from `start` is written the same way from `marked`.
example : (zigzag.stepCoins [true, false] marked).workTapes 0 1 = some false := by
  have hstart : (zigzag.stepCoins [true, false] start).workTapes 0 1 = some false := by
    rw [stepCoins_eq]
    rfl
  rw [← hstart]
  exact ((zigzag.agreeOn_blockWindow_stepCoins two_pos (by simp) agreeOn_marked).1.workTapes_eq
    0 1 (by simp [Cfg.blockWindow, start])).symm

-- The cell outside the window keeps its mark.
example : (zigzag.stepCoins [true, false] marked).workTapes 0 5 = some false :=
  zigzag.workTapes_stepCoins_eq_of_notMem_blockWindow two_pos (by simp) marked
    (by simp [Cfg.blockWindow, marked, start])

end ComplexityTests.HPVBlocks
