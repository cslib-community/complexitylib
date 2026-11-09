/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.ExactTriangle.DyadicParameters
import CslibFrontier.Algorithms.ExactTriangle.ParameterChoice.CostGeometry

/-!
# Actual parameter boundary and caller regressions

The large threshold fixture evaluates actual logarithm and power preparation, rather than ET on
a huge matrix. Kernel clients separately connect the full native initialized run, halt and
parameter geometry to the same final state, including the small/empty regime.
-/

set_option linter.hashCommand false

namespace CslibFrontierTests.WordRAMExactTriangleDyadicParameters

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open DyadicParameters

-- Zero is explicitly small; the nominal window/group values are one, not fast geometry.
#guard match DyadicParameters.entryProgram.eval 16 20 (.init [0]) with
  | some (y, _) => y.regs Reg.fast == 0 && y.regs Reg.window == 1 &&
      y.regs Reg.groups == 1 && y.regs Reg.level == 0 && y.mem 1 == 0
  | none => false

-- The former coarse transition is now a small input for the tuned parameter program.
#guard match DyadicParameters.entryProgram.eval 2048 2000 (.init [2 ^ 1296]) with
  | some (y, _) => y.regs Reg.fast == 0 && y.regs Reg.blocks == 0 &&
      y.regs Reg.window == 1 && y.regs Reg.groups == 1 && y.mem 1 == 2 ^ 1296
  | none => false

-- Just below the actual fast threshold, the computed block count is still zero.
#guard match DyadicParameters.entryProgram.eval 4096 2600 (.init [2 ^ 2394 - 1]) with
  | some (y, _) => y.regs Reg.fast == 0 && y.regs Reg.blocks == 0 &&
      y.regs Reg.window == 1 && y.mem 1 == 2 ^ 2394 - 1
  | none => false

-- The threshold itself enters the first fast block with all actual powers computed.
#guard match DyadicParameters.entryProgram.eval 4096 2600 (.init [2 ^ 2394]) with
  | some (y, _) => y.regs Reg.fast == 1 && y.regs Reg.blocks == 1 &&
      y.regs Reg.level == 63 && y.regs Reg.groups == 16 && y.regs Reg.window == 4 ^ 63 &&
      y.regs Reg.tensorDepth == 1323 && y.mem 1 == 2 ^ 2394
  | none => false

private def caller : Data 16 := (Data.init [777]).set Reg.side 16

-- A caller supplies n in a register; its unrelated memory is preserved by the real code.
example : ∃ y, ExecWithin 16 DyadicParameters.program caller y 49 ∧ y.regs Reg.side = 16 ∧
    y.regs Reg.fast = 0 ∧ y.regs Reg.window = 1 ∧ y.mem 1 = 777 := by
  obtain ⟨y, he, hn, _, _, hd, _, _, hf, hm⟩ :=
    DyadicParameters.exec (w := 16) (n := 16) caller rfl (by decide)
  have hd' : y.regs Reg.window = 1 := hd.trans (by decide +kernel)
  have hf' : y.regs Reg.fast = 0 := hf.trans (by decide +kernel)
  exact ⟨y, by simpa only [show DyadicParameters.timeBound 16 = 49 by decide +kernel] using he,
    hn, hf', hd', congrFun hm 1⟩

-- Every premise is discharged from a genuine empty input; the same-y prefix is polynomially
-- bounded even at a physical width larger than the minimum admission.
example : ∃ y t, t + 1 ≤ 36 ∧
    Runs 13 (DyadicParameters.entryProgram.program Reg.fast) (State.init [0])
      ⟨DyadicParameters.entryProgram.size, y⟩ t ∧
    Executes 13 (DyadicParameters.entryProgram.program Reg.fast) (State.init [0]) 0 (t + 1) ∧
    y.regs Reg.fast = 0 ∧ y.regs Reg.window = 1 ∧ ∀ i, y.regs i < 16384 := by
  obtain ⟨_, y, t, ht, run, halt, _, _, _, hd, _, _, hf, _, _⟩ :=
    DyadicParameters.runs_input (W := 13) (n := 0) (by decide +kernel)
  have hf' : y.regs Reg.fast = 0 := hf.trans (by decide +kernel)
  have hd' : y.regs Reg.window = 1 := hd.trans (by decide +kernel)
  have bounds := DyadicParameters.bounded_reachable_polynomial
    (n := 0) (W := 13) (by decide +kernel)
    ⟨DyadicParameters.entryProgram.size, y⟩ t run
  refine ⟨y, t, ?_, run, ?_, hf', hd', ?_⟩
  · simpa only [Nat.log_zero_right, Nat.mul_zero, Nat.zero_add] using ht
  · simpa only [hf'] using halt
  · simpa using bounds.1

-- This is a kernel proof client at the minimum width, with actual original-input execution,
-- rather than a result-only geometry witness or a large ET-solver interpreter experiment.
-- Permit normalization of this concrete 2394-bit boundary numeral during the final rewrites.
set_option exponentiation.threshold 2394 in
example : ∃ y t, t + 1 ≤ 38340 ∧
    Runs (DyadicParameters.admissionWidth (2 ^ 2394))
      (DyadicParameters.entryProgram.program Reg.fast) (State.init [2 ^ 2394])
      ⟨DyadicParameters.entryProgram.size, y⟩ t ∧
    Executes (DyadicParameters.admissionWidth (2 ^ 2394))
      (DyadicParameters.entryProgram.program Reg.fast) (State.init [2 ^ 2394])
      1 (t + 1) ∧ y.regs Reg.level = 63 ∧ y.regs Reg.window = 4 ^ 63 ∧
    y.regs Reg.groups = 16 ∧ y.regs Reg.tensorDepth = 1323 ∧
    y.regs Reg.window ^ 19 ≤ 2 ^ 2394 ∧ y.regs Reg.window ^ 18 ≤ 2 ^ 2394 ∧
    (y.regs Reg.groups : ℝ) ^ 2 ≤ Real.sqrt (y.regs Reg.window : ℝ) ∧
    (y.regs Reg.groups : ℝ) ^ 2 ≤ (y.regs Reg.window : ℝ) ^ (8 / 125 : ℝ) ∧
    y.mem 1 = 2 ^ 2394 := by
  obtain ⟨_, y, t, ht, run, halt, _, hb, hl, hd, hg, hL, hf, _, hm⟩ :=
    DyadicParameters.runs_input (n := 2 ^ 2394) le_rfl
  have block : ParameterChoice.blocks (2 ^ 2394) = 1 := by
    rw [ParameterChoice.blocks, Nat.log_pow (by decide)]
  have level : ParameterChoice.level (2 ^ 2394) = 63 := by
    simp only [ParameterChoice.level, block, Nat.mul_one]
  have window : ParameterChoice.window (2 ^ 2394) = 4 ^ 63 := by
    rw [ParameterChoice.window, level]
  have groups : ParameterChoice.groups (2 ^ 2394) = 16 := by
    rw [ParameterChoice.groups, block]
  have depth : ParameterChoice.tensorDepth (2 ^ 2394) = 1323 := by
    rw [ParameterChoice.tensorDepth, level]
  have hf' : y.regs Reg.fast = 1 := by
    simpa only [block, Nat.zero_lt_one, ite_true] using hf
  refine ⟨y, t, ?_, run, ?_, hl.trans level, hd.trans window, hg.trans groups,
    hL.trans depth, ?_, ?_, ?_, ?_, congrFun hm 1⟩
  · rw [Nat.log_pow (by decide : 1 < (2 : ℕ))] at ht
    exact ht
  · simpa only [hf'] using halt
  · rw [hd, ParameterChoice.window_pow, block, Nat.mul_one]
  · rw [hd]
    exact ParameterChoice.geometry (Nat.two_pow_pos 2394)
  · rw [hg, hd]
    exact ParameterChoice.groups_sq_le_sqrt _
  · rw [hg, hd]
    exact ParameterChoice.groups_sq_le_window_rpow _

end CslibFrontierTests.WordRAMExactTriangleDyadicParameters
