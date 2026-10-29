/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.FusionTree.MSBProgram

/-! Actual shift/transfer regressions and nonvacuous MSB execution clients. Full MSB
interpretation is deliberately avoided here; the charged execution theorem covers it. -/

open Cslib.WordRAM Cslib.WordRAM.Multiword

namespace WordRAMMSBTests

def shiftInput (s : ℕ) : Data 9 := ⟨![7, 7, 7, 7, 3, 3, 7, 7, s], fun _ => 7⟩

/-- Whole-digit, residual, zero, and beyond-capacity shifts execute on real instructions. -/
example : ∀ s ∈ [0, 1, 2, 3, 4, 5, 6],
    ((Shift.program 4 [4, 5] [6, 7] 8).eval 4 0 (shiftInput s)).map
      (fun (y, _) => y.regs 6 + 4 * y.regs 7) = some (15 >>> s) := by decide

def oddShiftInput (s : ℕ) : Data 9 := ⟨![7, 7, 7, 7, 1, 1, 7, 7, s], fun _ => 3⟩

example : ∀ s ∈ [0, 1, 2, 3, 4, 5, 6, 7],
    ((Shift.program 3 [4, 5] [6, 7] 8).eval 3 0 (oddShiftInput s)).map
      (fun (y, _) => y.regs 6 + 2 * y.regs 7) = some (3 >>> s) := by decide

/-- Both conversions are charged, including radix setup. -/
def roundTrip : Code .standard 8 :=
  .seq (Transfer.split 4 [5, 6, 7]) (Transfer.assemble [5, 6, 7] 4)

example : ∀ q ∈ List.range 8,
    (roundTrip.eval 3 0 ⟨![7, 7, 7, 7, q, 7, 7, 7], fun _ => 5⟩).map
      (fun (y, t) => (y.regs 4, t, y.mem 12)) = some (q, 28, 5) := by decide

open Cslib.Algorithms.WordRAM.FusionTree.MSB

/-- The singleton-input endpoint includes a real width-two instance. -/
example : ∃ t ≤ 200001, Executes 2 (Program.program 2) (State.init [3]) 1 t := by
  simpa using Program.executes_program (by decide : 2 ≤ 2) (by decide : 3 < 2 ^ 2)

/-- Dirty but fitting workspace, a fitting scalar input, and nonzero memory. -/
def input (w q : ℕ) : Data (Bank.capacity 44 + 4) :=
  ⟨fun i => if i = Bank.inputReg then q else 2 ^ w - 1, fun a => (a + 1) % 2 ^ w⟩

/-- Scalar MSB execution on `31` at width `5` and `0` at width `3`, plus fixed register capacity
and code-size bounds. -/
example (w : ℕ) :
    (∃ y, ExecWithin 5 (Program.scalarCode 5) (input 5 31) y 200000 ∧
      y.regs Program.output = 4 ∧ y.mem = (input 5 31).mem) ∧
    (∃ y, ExecWithin 3 (Program.scalarCode 3) (input 3 0) y 200000 ∧
      y.regs Program.output = 0 ∧ y.mem = (input 3 0).mem) ∧
    Bank.capacity 44 + 4 = 836 ∧
    (Program.scalarCode w).size ≤ 200000 := by
  have hlog : (31 : ℕ).log2 = 4 := by decide
  refine ⟨?_, ?_, by decide, Program.size_scalarCode w⟩
  · simpa only [input, ↓reduceIte, hlog] using
      Program.exec_scalarCode (by decide : 3 ≤ 5) (input 5 31) (by decide)
  · simpa only [input, ↓reduceIte, Nat.log2_zero] using
      Program.exec_scalarCode (by decide : 3 ≤ 3) (input 3 0) (by decide)

end WordRAMMSBTests
