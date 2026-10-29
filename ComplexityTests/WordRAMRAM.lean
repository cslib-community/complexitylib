/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.RAMInput

/-!
# Word-RAM to RAM compiler boundary clients

Exercise source-register aliasing on indirect accesses, all equality and strict-order outcomes,
explicit halting with zero, and the length information lost by bare RAM input lists. These are
clients of the executable compiler and its proved padded and prepared input cost bounds.
-/

namespace ComplexityTests.WordRAMRAM

open Cslib Cslib.WordRAM

private def targetResult {r : ℕ} (p : Program .standard r) (input : List ℕ) : ℕ × Bool :=
  let q := ToRAM.paddedProgram p
  let s := RAM.run q 40 (RAM.State.init (ToRAM.paddedInput r input))
  (s.regs.output, decide (s.isHalted q))

private def selfLoad : Program .standard 1 := [.op (.const 0 1), .op (.load 0 0), .halt 0]

private def selfStore : Program .standard 1 :=
  [.op (.const 0 1), .op (.store 0 0), .op (.load 0 0), .halt 0]

/-- Aliasing load and store clients, plus the quantitative theorem on `selfLoad`. -/
example :
    targetResult selfLoad [7] = (7, true) ∧
    targetResult selfStore [7] = (1, true) ∧
    RAM.HaltsWithResultInTime RAM.logCost (ToRAM.paddedProgram selfLoad)
      (ToRAM.paddedInput 1 [7]) 7 (8 * (RAM.bitLength 6 + 1) * 4 * 4) :=
  ⟨by decide, by decide,
   ToRAM.haltsWithResultInTime_padded (by decide) (w := 3) (by decide)
     (Executes.of_run (fuel := 5) (by decide))⟩

private def compare (c : Cond 2) (a b : ℕ) : Program .standard 2 :=
  [.op (.const 0 a), .op (.const 1 b), .branch c 5, .op (.const 0 0), .halt 0,
    .op (.const 0 1), .halt 0]

/-- Equality, strict order, and explicit halting with zero. -/
example :
    (targetResult (compare (.eq 0 1) 0 1) [] = (0, true) ∧
      targetResult (compare (.eq 0 1) 1 0) [] = (0, true) ∧
      targetResult (compare (.eq 0 1) 1 1) [] = (1, true)) ∧
    (targetResult (compare (.lt 0 1) 0 1) [] = (1, true) ∧
      targetResult (compare (.lt 0 1) 1 0) [] = (0, true) ∧
      targetResult (compare (.lt 0 1) 1 1) [] = (0, true)) ∧
    targetResult [.halt (0 : Fin 1)] [] = (0, true) := by
  decide

/-- Zero-bit words and charged input preparation on `[.halt (0 : Fin 1)]` and `selfLoad`. -/
example :
    RAM.HaltsWithResultInTime RAM.logCost (ToRAM.paddedProgram [.halt (0 : Fin 1)])
      (ToRAM.paddedInput 1 []) 0 (8 * (RAM.bitLength 6 + 1) * 2) ∧
    RAM.HaltsWithResultInTime RAM.logCost (ToRAM.preparedProgram [.halt (0 : Fin 1)])
      (RAM.Input.encode 5 []) 0 (212 * 2) ∧
    RAM.HaltsWithResultInTime RAM.logCost (ToRAM.preparedProgram selfLoad)
      (RAM.Input.encode 5 [7]) 7 (212 * 5 * 4) :=
  ⟨by
     simpa [ToRAM.memoryBase] using
       ToRAM.haltsWithResultInTime_padded (p := [.halt (0 : Fin 1)]) (by decide)
         (input := []) (w := 0) (v := 0) (n := 1) (by decide)
         (Executes.of_run (fuel := 1) (by decide)),
   ToRAM.haltsWithResultInTime_prepared (p := [.halt (0 : Fin 1)]) (by decide)
     (input := []) (w := 0) (v := 0) (n := 1) (by decide)
     (Executes.of_run (fuel := 1) (by decide)),
   ToRAM.haltsWithResultInTime_prepared (by decide) (w := 3) (by decide)
     (Executes.of_run (fuel := 5) (by decide))⟩

/-- Unreflected source faults, empty-program behavior, and trailing-zero input distinction between
bare RAM and WordRAM's length header. -/
example :
    (run (B := .standard) 1 [.op (.const (0 : Fin 1) 2), .halt 0] 4 (.init []) = none ∧
      targetResult [.op (.const (0 : Fin 1) 2), .halt 0] [] = (2, true)) ∧
    (run 0 ([] : Program .standard 1) 1 (.init []) = none ∧
      targetResult ([] : Program .standard 1) [] = (0, true)) ∧
    RAM.State.init [] = RAM.State.init [0] ∧
    (State.init [] : State 1) ≠ State.init [0] := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · apply RAM.State.ext
    · rfl
    · funext i
      cases i <;> rfl
  · intro h
    have := congrArg (fun s : State 1 => s.data.mem 0) h
    simp [State.init] at this

end ComplexityTests.WordRAMRAM
