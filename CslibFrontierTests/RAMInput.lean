/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.RAM.Input

/-!
# RAM input-preparation clients

Executable checks cover an unchanged destination, a genuinely overlapping shifted block, empty
input, and the boundary before arbitrary appended code. Symbolic clients exercise the exact
register-state theorem and its charged logarithmic bound.
-/

namespace ComplexityTests.RAMInput

open Cslib Cslib.RAM Cslib.RAM.Input

-- `R = 5` copies the block onto itself, including an interior zero word.
example :
    let s := run (prepare 5) (prepareSteps 5 [7, 0, 11]) (State.init (encode 5 [7, 0, 11]))
    s.pc = 17 ∧ (List.range 11).map s.regs.read = [0, 0, 0, 0, 0, 3, 7, 0, 11, 0, 0] := by
  decide

-- Source addresses `5..10` overlap destination addresses `7..12`.
example :
    let s := run (prepare 7) (prepareSteps 7 [3, 0, 4, 1, 5])
      (State.init (encode 5 [3, 0, 4, 1, 5]))
    s.pc = 19 ∧
      (List.range 15).map s.regs.read = [0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 4, 1, 5, 0, 0] := by
  decide

-- The zero length header is still copied and the scratch registers are cleared.
example :
    let s := run (prepare 8) (prepareSteps 8 []) (State.init (encode 5 []))
    s.pc = 20 ∧ (List.range 12).map s.regs.read = List.replicate 12 0 := by
  decide

-- Preparation stops before the appended instruction; exactly one more step executes it.
example :
    let p := prepare 7 ++ [.const 0 99]
    let s := State.init (encode 5 [3, 0, 4, 1, 5])
    (run p (prepareSteps 7 [3, 0, 4, 1, 5]) s).regs.read 0 = 0 ∧
      (run p (prepareSteps 7 [3, 0, 4, 1, 5] + 1) s).regs.read 0 = 99 := by
  decide

example (tail : Program) (input : List ℕ) :
    run (prepare 5 ++ tail) (prepareSteps 5 input) (State.init (encode 5 input)) =
      ⟨17, URM.Regs.ofInputs (encode 5 input)⟩ :=
  run_prepare_append (by decide) tail input

example (tail : Program) :
    time logCost (prepare 5 ++ tail) (prepareSteps 5 []) (State.init (encode 5 [])) ≤ 174 := by
  exact time_prepare_append_le (b := 1) (by decide) tail [] (by decide) (by simp)

example (tail : Program) :
    time logCost (prepare 7 ++ tail) (prepareSteps 7 [3, 0, 4, 1, 5])
      (State.init (encode 5 [3, 0, 4, 1, 5])) ≤ 3348 := by
  exact time_prepare_append_le (b := 3) (by decide) tail [3, 0, 4, 1, 5]
    (by decide) (by decide)

end ComplexityTests.RAMInput
