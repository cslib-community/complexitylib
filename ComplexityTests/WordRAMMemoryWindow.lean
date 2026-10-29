/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Computability.WordRAM.MemoryWindow
import Complexity.Computability.WordRAM.ArrayNormalize
import Mathlib.Tactic.FinCases

/-! # Dirty-memory, dynamic-base and frame clients for actual memory-window code -/

open Cslib.WordRAM

private def dirty : Data 6 :=
  ⟨![2, 0, 1, 17, 8, 0], fun a => if a = 19 then 27 else if a = 16 then 99
    else if a = 25 then 77 else 0⟩

private def sourceCode : Code .standard 3 :=
  .seq (.op (.load 1 0)) <| .seq (.op (.bin .add 1 1 2)) (.op (.store 0 1))

-- The real masked load reads 27 % 8 = 3, then actual arithmetic/store writes 4.
-- Omitting the remainder would write 28. Both adjacent caller sentinels survive.
example : ∃ y, ExecWithin 8 (MemoryWindow.compile sourceCode) dirty y 6 ∧
    y.mem 19 = 4 ∧ y.mem 16 = 99 ∧ y.mem 25 = 77 ∧ y.regs 3 = 17 ∧ y.regs 4 = 8 := by
  refine ⟨?y, ?run, ?value, ?left, ?right, ?base, ?modulus⟩
  case run =>
    apply ExecWithin.of_eval (fuel := 0) (n := 6)
    · rfl
    · decide
  all_goals decide +kernel

example : Fits 5 (17 + 2 ^ 3) ∧ ¬Fits 4 (17 + 2 ^ 3) := by decide +kernel

-- The source view is bounded despite dirty physical memory and caller words above 2^3.
example : (MemoryWindow.view 3 17 dirty : Data 3).Bounded 3 := by
  apply MemoryWindow.view_bounded
  intro i
  fin_cases i <;> decide +kernel

-- Only the requested span is normalized, including the final cell.
example : ∃ y, ExecWithin 8 ArrayNormalize.program
    ⟨![10, 2, 8, 99, 99, 99, 99], fun a => if a = 10 then 27 else 19⟩ y 18 ∧
      y.mem 9 = 19 ∧ y.mem 10 = 3 ∧ y.mem 11 = 3 ∧ y.mem 12 = 19 := by
  refine ⟨?y, ?run, ?values⟩
  case run => ram_eval 2 [ArrayNormalize.program, ArrayNormalize.body, ArrayNormalize.base,
    ArrayNormalize.length, ArrayNormalize.modulus, ArrayNormalize.index, ArrayNormalize.address,
    ArrayNormalize.value, ArrayNormalize.one, Fits, Fin.mk.injEq]
  case values => decide +kernel
