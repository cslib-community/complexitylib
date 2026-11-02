/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters

/-!
# Actual parameter boundary and caller regressions

The large threshold fixture runs only logarithm and power preparation, not an ET solver on
a huge matrix. Kernel clients separately connect the full native initialized run, halt and
parameter geometry to the same final state, including the small/empty regime.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleDyadicParameters

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters

-- Zero is explicitly small; the nominal window/group values are one, not fast geometry.
#guard match entryProgram.eval 16 20 (.init [0]) with
  | some (y, _) => y.regs Reg.fast == 0 && y.regs Reg.window == 1 &&
      y.regs Reg.groups == 1 && y.regs Reg.level == 0 && y.mem 1 == 0
  | none => false

-- Just below the actual fast threshold, the computed block count is still zero.
#guard match entryProgram.eval 2048 2000 (.init [2 ^ 1296 - 1]) with
  | some (y, _) => y.regs Reg.fast == 0 && y.regs Reg.blocks == 0 &&
      y.regs Reg.window == 1 && y.mem 1 == 2 ^ 1296 - 1
  | none => false

-- The threshold itself enters the first fast block with all actual powers computed.
#guard match entryProgram.eval 2048 2000 (.init [2 ^ 1296]) with
  | some (y, _) => y.regs Reg.fast == 1 && y.regs Reg.blocks == 1 &&
      y.regs Reg.level == 36 && y.regs Reg.groups == 4 && y.regs Reg.window == 4 ^ 36 &&
      y.regs Reg.tensorDepth == 684 && y.mem 1 == 2 ^ 1296
  | none => false

private def caller : Data 16 := (Data.init [777]).set Reg.side 16

-- A caller supplies n in a register; its unrelated memory is preserved by the real code.
example : ∃ y, ExecWithin 16 program caller y 49 ∧ y.regs Reg.side = 16 ∧
    y.regs Reg.fast = 0 ∧ y.regs Reg.window = 1 ∧ y.mem 1 = 777 := by
  obtain ⟨y, he, hn, _, _, hd, _, _, hf, hm⟩ := exec (w := 16) (n := 16) caller rfl (by decide)
  have hd' : y.regs Reg.window = 1 := hd.trans (by decide +kernel)
  have hf' : y.regs Reg.fast = 0 := hf.trans (by decide +kernel)
  exact ⟨y, by simpa only [show timeBound 16 = 49 by decide +kernel] using he,
    hn, hf', hd', congrFun hm 1⟩

-- Every premise is discharged from a genuine empty input; the same-y prefix is polynomially
-- bounded even at a physical width larger than the minimum admission.
example : ∃ y t, t + 1 ≤ 36 ∧
    Runs 12 (entryProgram.program Reg.fast) (State.init [0]) ⟨entryProgram.size, y⟩ t ∧
    Executes 12 (entryProgram.program Reg.fast) (State.init [0]) 0 (t + 1) ∧
    y.regs Reg.fast = 0 ∧ y.regs Reg.window = 1 ∧ ∀ i, y.regs i < 8192 := by
  obtain ⟨_, y, t, ht, run, halt, _, _, _, hd, _, _, hf, _, _⟩ :=
    runs_input (W := 12) (n := 0) (by decide +kernel)
  have hf' : y.regs Reg.fast = 0 := hf.trans (by decide +kernel)
  have hd' : y.regs Reg.window = 1 := hd.trans (by decide +kernel)
  have bounds := bounded_reachable_polynomial (n := 0) (W := 12) (by decide +kernel)
    ⟨entryProgram.size, y⟩ t run
  refine ⟨y, t, ?_, run, ?_, hf', hd', ?_⟩
  · simpa only [Nat.log_zero_right, Nat.mul_zero, Nat.zero_add] using ht
  · simpa only [hf'] using halt
  · simpa using bounds.1

-- This is a kernel proof client at the minimum width, with actual original-input execution,
-- rather than a result-only geometry witness or a large ET-solver interpreter experiment.
-- Permit normalization of this concrete 1296-bit boundary numeral during the final rewrites.
set_option exponentiation.threshold 1296 in
example : ∃ y t, t + 1 ≤ 15588 ∧
    Runs (admissionWidth (2 ^ 1296)) (entryProgram.program Reg.fast) (State.init [2 ^ 1296])
      ⟨entryProgram.size, y⟩ t ∧
    Executes (admissionWidth (2 ^ 1296)) (entryProgram.program Reg.fast) (State.init [2 ^ 1296])
      1 (t + 1) ∧ y.regs Reg.level = 36 ∧ y.regs Reg.window = 4 ^ 36 ∧
    y.regs Reg.groups = 4 ∧ y.regs Reg.tensorDepth = 684 ∧
    y.regs Reg.window ^ 18 ≤ 2 ^ 1296 ∧ y.regs Reg.groups ^ 36 = y.regs Reg.window ∧
    y.mem 1 = 2 ^ 1296 := by
  obtain ⟨_, y, t, ht, run, halt, _, hb, hl, hd, hg, hL, hf, _, hm⟩ :=
    runs_input (n := 2 ^ 1296) le_rfl
  have block : ParameterChoice.blocks (2 ^ 1296) = 1 := by
    rw [ParameterChoice.blocks, Nat.log_pow (by decide)]
  have level : ParameterChoice.level (2 ^ 1296) = 36 := by
    simp only [ParameterChoice.level, block, Nat.mul_one]
  have window : ParameterChoice.window (2 ^ 1296) = 4 ^ 36 := by
    rw [ParameterChoice.window, level]
  have groups : ParameterChoice.groups (2 ^ 1296) = 4 := by
    rw [ParameterChoice.groups, block, pow_one]
  have depth : ParameterChoice.tensorDepth (2 ^ 1296) = 684 := by
    rw [ParameterChoice.tensorDepth, level]
  have hf' : y.regs Reg.fast = 1 := by
    simpa only [block, Nat.zero_lt_one, ite_true] using hf
  refine ⟨y, t, ?_, run, ?_, hl.trans level, hd.trans window, hg.trans groups,
    hL.trans depth, ?_, ?_, congrFun hm 1⟩
  · rw [Nat.log_pow (by decide : 1 < (2 : ℕ))] at ht
    exact ht
  · simpa only [hf'] using halt
  · rw [hd, ParameterChoice.window_pow, block, Nat.mul_one]
  · rw [hg, hd]
    exact ParameterChoice.groups_pow _

end ComplexityTests.WordRAMExactTriangleDyadicParameters
