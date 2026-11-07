/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Quantum.OutputSupport

/-! Target-only quantum support and restoration of the complete output register. -/

namespace ComplexityTests.QuantumOutputSupport

open Cslib Cslib.Quantum Cslib.BitString Cslib.Probability

-- Read order, repeated positions, and out-of-range false bits have explicit list semantics.
example : readPositions [4, 1, 4, 12] [true, false, true, false, true] =
    [true, false, true, false] := by decide

-- Restoring uses the first repeated position and leaves every unselected reference bit intact.
example : restorePositions [4, 1, 4] [true, false, true, false, false, true]
    [true, true, false] = [true, true, true, false, true, true] := by decide

-- A wire used only as a control is not a target; repeated targets appear once.
private def controlCircuit : List GateCode :=
  [(false, 3, [7]), (true, 3, []), (false, 1, [3])]

example : GateCode.targets controlCircuit = [3, 1] := by decide

example (input path : List Bool) :
    (pathRun controlCircuit input path).1.getD 7 false = input.getD 7 false :=
  getD_pathRun_of_not_mem_targets controlCircuit input path 7 (by decide)

private def pairCircuit : List GateCode := [(true, 2, []), (false, 5, [2])]

private theorem pairCircuit_wellFormed : ∀ g ∈ pairCircuit, g.WellFormed 10 := by
  intro g hg
  simp only [pairCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> decide

-- A Bell pair on wires 2 and 5 cannot produce a one on untouched wire 9.
example : (Circuit.measure (Circuit.ofCodes 10 pairCircuit) (fun _ => false))
    (fun i => decide (i.val = 9)) = 0 := by
  have hzero := run_ofCodes_apply_eq_zero_of_not_mem_targets pairCircuit_wellFormed
    (fun _ => false) (fun i => decide (i.val = 9)) ⟨9, by decide⟩ (by decide) (by decide)
  simp [Circuit.measure_apply, hzero]

-- Only two output bits need to be retained from this ten-wire measurement.
private def reference : List Bool :=
  [true, false, false, true, false, false, false, true, false, true]

example : (((Circuit.measure (Circuit.ofCodes reference.length pairCircuit)
      (inputState reference.length reference)).map (fun y => [2, 5].map (readBit y))).map
      (restorePositions [2, 5] reference)) =
    (Circuit.measure (Circuit.ofCodes reference.length pairCircuit)
      (inputState reference.length reference)).map List.ofFn :=
  measure_map_restorePositions reference pairCircuit_wellFormed [2, 5] (by decide)

-- Restoring a readback also works with repeated positions and a position past the end.
example : restorePositions [5, 2, 5, 100] reference
    (readPositions [5, 2, 5, 100]
      [true, false, true, true, false, true, false, true, false, true]) =
    [true, false, true, true, false, true, false, true, false, true] := by decide

-- No gates require no sampled output positions, independently of register width.
example : GateCode.targets [] = [] := by decide
example (input : List Bool) : restorePositions [] input [] = input := by
  simpa only [readPositions, List.map_nil] using
    restorePositions_readPositions [] input input rfl (by simp)

-- Empty registers and empty outputs are included without a positive-width hypothesis.
example : restorePositions [] [] [] = [] := by decide

end ComplexityTests.QuantumOutputSupport
