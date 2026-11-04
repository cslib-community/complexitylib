/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.BoxDyadicParameters
import Complexity.Algorithms.ExactTriangle.BoxParameterChoice.CostGeometry

/-!
# Actual parameter boundary and caller regressions

The large threshold fixture evaluates actual logarithm and power preparation, rather than ET on
a huge matrix. Kernel clients separately connect the full native initialized run, halt and
parameter geometry to the same final state, including the small/empty regime.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMBoxDyadicParameters

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open DyadicParameters

-- Zero is explicitly small; the nominal window/group values are one, not fast geometry.
#guard match BoxDyadicParameters.entryProgram.eval 16 20 (.init [0]) with
  | some (y, _) => y.regs Reg.fast == 0 && y.regs Reg.window == 1 &&
      y.regs Reg.groups == 1 && y.regs Reg.level == 0 && y.mem 1 == 0
  | none => false

-- Just below the actual fast threshold, the computed block count is still zero.
#guard match BoxDyadicParameters.entryProgram.eval 4096 2600 (.init [2 ^ 2394 - 1]) with
  | some (y, _) => y.regs Reg.fast == 0 && y.regs Reg.blocks == 0 &&
      y.regs Reg.window == 1 && y.mem 1 == 2 ^ 2394 - 1
  | none => false

-- The threshold itself enters the first fast block with all actual powers computed.
#guard match BoxDyadicParameters.entryProgram.eval 4096 2600 (.init [2 ^ 2394]) with
  | some (y, _) => y.regs Reg.fast == 1 && y.regs Reg.blocks == 1 &&
      y.regs Reg.level == 63 && y.regs Reg.groups == 16 && y.regs Reg.window == 4 ^ 63 &&
      y.regs Reg.tensorDepth == 1323 && y.mem 1 == 2 ^ 2394
  | none => false

private def caller : Data 16 := (Data.init [777]).set Reg.side 16

-- A caller supplies n in a register; its unrelated memory is preserved by the real code.
example : ∃ y, ExecWithin 16 BoxDyadicParameters.program caller y 49 ∧ y.regs Reg.side = 16 ∧
    y.regs Reg.fast = 0 ∧ y.regs Reg.window = 1 ∧ y.mem 1 = 777 := by
  obtain ⟨y, he, hn, _, _, hd, _, _, hf, hm⟩ :=
    BoxDyadicParameters.exec (w := 16) (n := 16) caller rfl (by decide)
  have hd' : y.regs Reg.window = 1 := hd.trans (by decide +kernel)
  have hf' : y.regs Reg.fast = 0 := hf.trans (by decide +kernel)
  exact ⟨y, by simpa only [show BoxDyadicParameters.timeBound 16 = 49 by decide +kernel] using he,
    hn, hf', hd', congrFun hm 1⟩

-- Every premise is discharged from a genuine empty input; the same-y prefix is polynomially
-- bounded even at a physical width larger than the minimum admission.
example : ∃ y t, t + 1 ≤ 36 ∧
    Runs 13 (BoxDyadicParameters.entryProgram.program Reg.fast) (State.init [0])
      ⟨BoxDyadicParameters.entryProgram.size, y⟩ t ∧
    Executes 13 (BoxDyadicParameters.entryProgram.program Reg.fast) (State.init [0]) 0 (t + 1) ∧
    y.regs Reg.fast = 0 ∧ y.regs Reg.window = 1 ∧ ∀ i, y.regs i < 16384 := by
  obtain ⟨_, y, t, ht, run, halt, _, _, _, hd, _, _, hf, _, _⟩ :=
    BoxDyadicParameters.runs_input (W := 13) (n := 0) (by decide +kernel)
  have hf' : y.regs Reg.fast = 0 := hf.trans (by decide +kernel)
  have hd' : y.regs Reg.window = 1 := hd.trans (by decide +kernel)
  have bounds := BoxDyadicParameters.bounded_reachable_polynomial
    (n := 0) (W := 13) (by decide +kernel)
    ⟨BoxDyadicParameters.entryProgram.size, y⟩ t run
  refine ⟨y, t, ?_, run, ?_, hf', hd', ?_⟩
  · simpa only [Nat.log_zero_right, Nat.mul_zero, Nat.zero_add] using ht
  · simpa only [hf'] using halt
  · simpa using bounds.1

-- This is a kernel proof client at the minimum width, with actual original-input execution,
-- rather than a result-only geometry witness or a large ET-solver interpreter experiment.
-- Permit normalization of this concrete 2394-bit boundary numeral during the final rewrites.
set_option exponentiation.threshold 2394 in
example : ∃ y t, t + 1 ≤ 38340 ∧
    Runs (BoxDyadicParameters.admissionWidth (2 ^ 2394))
      (BoxDyadicParameters.entryProgram.program Reg.fast) (State.init [2 ^ 2394])
      ⟨BoxDyadicParameters.entryProgram.size, y⟩ t ∧
    Executes (BoxDyadicParameters.admissionWidth (2 ^ 2394))
      (BoxDyadicParameters.entryProgram.program Reg.fast) (State.init [2 ^ 2394])
      1 (t + 1) ∧ y.regs Reg.level = 63 ∧ y.regs Reg.window = 4 ^ 63 ∧
    y.regs Reg.groups = 16 ∧ y.regs Reg.tensorDepth = 1323 ∧
    y.regs Reg.window ^ 19 ≤ 2 ^ 2394 ∧
    (y.regs Reg.groups : ℝ) ^ 2 ≤ Real.sqrt (y.regs Reg.window : ℝ) ∧
    y.mem 1 = 2 ^ 2394 := by
  obtain ⟨_, y, t, ht, run, halt, _, hb, hl, hd, hg, hL, hf, _, hm⟩ :=
    BoxDyadicParameters.runs_input (n := 2 ^ 2394) le_rfl
  have block : BoxParameterChoice.blocks (2 ^ 2394) = 1 := by
    rw [BoxParameterChoice.blocks, Nat.log_pow (by decide)]
  have level : BoxParameterChoice.level (2 ^ 2394) = 63 := by
    simp only [BoxParameterChoice.level, block, Nat.mul_one]
  have window : BoxParameterChoice.window (2 ^ 2394) = 4 ^ 63 := by
    rw [BoxParameterChoice.window, level]
  have groups : BoxParameterChoice.groups (2 ^ 2394) = 16 := by
    rw [BoxParameterChoice.groups, block]
  have depth : BoxParameterChoice.tensorDepth (2 ^ 2394) = 1323 := by
    rw [BoxParameterChoice.tensorDepth, level]
  have hf' : y.regs Reg.fast = 1 := by
    simpa only [block, Nat.zero_lt_one, ite_true] using hf
  refine ⟨y, t, ?_, run, ?_, hl.trans level, hd.trans window, hg.trans groups,
    hL.trans depth, ?_, ?_, congrFun hm 1⟩
  · rw [Nat.log_pow (by decide : 1 < (2 : ℕ))] at ht
    exact ht
  · simpa only [hf'] using halt
  · rw [hd, BoxParameterChoice.window_pow, block, Nat.mul_one]
  · rw [hg, hd]
    exact BoxParameterChoice.groups_sq_le_sqrt _

end ComplexityTests.WordRAMBoxDyadicParameters
