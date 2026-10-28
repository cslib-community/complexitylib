/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.Cell

/-!
# Native three-matrix cell construction regressions

These execute the actual unsigned instructions, including index and address computations.
-/

namespace ComplexityTests.ThreeSumCell

open Cslib
open WordRAM.Signed (encode result)
open Algorithms.WordRAM.ThreeSum.Cell

private def values (i : ℕ) : ℤ := [9, -2, -4].getD i 0

private def args (q s : ℕ) : WordRAM.Data 28 :=
  ⟨fun i => if i.val = 10 then 3 else if i.val = 11 then 5
    else if i.val = 12 then encode 19 else if i.val = 14 then q
    else if i.val = 15 then 2 else if i.val = 16 then s
    else if i.val = 17 then 20 else if i.val = 18 then 24
    else if i.val = 19 then 28 else 37,
    fun a => if 5 ≤ a ∧ a < 8 then encode (values (a - 5)) else 41⟩

/-- Every initial register and memory cell fits in the target word width. -/
example : (args 0 2).Bounded 8 := by
  constructor
  · intro i
    simp only [args, WordRAM.Fits]
    split_ifs <;> decide
  · intro a
    by_cases h : 5 ≤ a ∧ a < 8
    · have ha : a = 5 ∨ a = 6 ∨ a = 7 := by omega
      rcases ha with rfl | rfl | rfl <;> decide
    · simp [args, h, WordRAM.Fits]

/-- Valid AB, BC and AC cells read the expected signed values in the three orientations. -/
example : (WordRAM.Code.eval 8 0 step (args 0 2)).map
    (fun yn => (yn.1.mem 20, yn.1.mem 24, yn.1.mem 28)) = some (18, 9, 8) := by decide

/-- A negative BC index uses positive filler; the input and filler register are preserved. -/
example : (WordRAM.Code.eval 8 0 step (args 2 0)).map
    (fun yn => (yn.1.mem 22, yn.1.mem 26, yn.1.mem 30, yn.1.mem 6,
      yn.1.regs filler)) = some (9, 38, 8, 5, 38) := by decide

/-- Invalid AC indices retain positive filler after the selection and negation. -/
example : (WordRAM.Code.eval 8 0 step (args 1 2)).map
    (fun yn => (yn.1.mem 21, yn.1.mem 25, yn.1.mem 29)) = some (5, 38, 38) := by decide

/-- The assembled instruction list, including its charged halt, runs on an actual bounded input. -/
example : (WordRAM.run 8 (step.program result) 129 ⟨0, args 0 2⟩).isSome := by decide

/-- The charged theorem has satisfiable signed, address and disjointness hypotheses. -/
example : ∃ y, WordRAM.ExecWithin 8 step (args 0 2) y 128 ∧
    y.mem 20 = encode 9 ∧ y.regs cell = 0 := by
  obtain ⟨y, he, hm, -, hr⟩ := exec_step (w := 6) (N := 3) (b := 5)
    (ab := 20) (bc := 24) (ac := 28) (q := 0) (t := 2) (s := 2)
    (μ := values) (F := 19) (args 0 2)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by
      intro i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide)
    (by
      intro i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨y, he, ?_, hr cell (by decide)⟩
  rw [hm]
  decide

end ComplexityTests.ThreeSumCell
