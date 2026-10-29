/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters

/-!
# Executed boundary cases for native Chan–He parameters

The observations include all nine outputs, the instruction count, and input memory cells.
The generic run clients below discharge the actual input magnitude and width hypotheses.
-/

-- This module contains only private execution checks.
set_option linter.privateModule false

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters

private def observe (κ : ℕ) (input : List ℤ) : Option (List ℕ × ℕ × List ℕ) :=
  ((program κ).eval 64 32 (Data.init (input.map Signed.encode))).map fun (x, t) =>
    ([x.regs len, x.regs magnitude, x.regs digits, x.regs height, x.regs fuel,
      x.regs want, x.regs primeBound, x.regs packedLen, x.regs padding], t,
      [x.mem 0, x.mem 1, x.mem 2])

-- Empty input, including the fixed exponent zero.
example : observe 0 [] = some ([0, 1, 3, 1, 1, 15, 192, 294912, 5], 83, [0, 0, 0]) := by
  decide

-- One position; the signed encoding of -1 remains in memory.
example : observe 0 [-1] = some ([1, 1, 3, 1, 1, 30, 372, 1107072, 5], 88, [1, 3, 0]) := by
  decide

-- Two positions at exponent zero: the ceiling logarithm and fuel increase.
example : observe 0 [-1, 1] =
    some ([2, 1, 3, 2, 4, 30, 372, 1107072, 5], 97, [2, 3, 2]) := by
  decide

-- Nonconstant polynomial magnitude, with both signed boundary values.
example : observe 1 [-4, 4] =
    some ([2, 4, 5, 2, 4, 50, 714, 4078368, 17], 110, [2, 9, 8]) := by
  decide

-- A native contract client, including all width/magnitude hypotheses and all memory framing.
example : ∃ y t, t ≤ 5 * Nat.sqrt 2 + 3400 * Nat.clog 2 4 ∧
    Runs 512 ((program 1).program packedLen) (State.init ([(-4 : ℤ), 4].map Signed.encode))
      ⟨(program 1).size, y⟩ t ∧ Output 2 4 y ∧
    y.mem = (Data.init ([(-4 : ℤ), 4].map Signed.encode) : Data 24).mem ∧ y.Bounded 512 := by
  apply runs_input (κ := 1) [(-4 : ℤ), 4] (by decide)
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> decide

-- The empty-input width remains positive and the final input-init theorem is satisfiable.
example : 0 < width 0 0 ∧ InputFits 512 (([] : List ℤ).map Signed.encode) := by
  constructor
  · decide
  · apply inputFits (κ := 0) [] (by decide)
    simp
