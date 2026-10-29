/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.Fill

/-! # Executed matrix-builder regressions -/

namespace ComplexityTests.ThreeSumFill

open Cslib
open WordRAM WordRAM.Signed
open Algorithms.WordRAM.ThreeSum

private def values (i : ℕ) : ℤ := [9, -2, -4].getD i 0

private def layout : Fill.Args := ⟨3, 2, 2, 5, 20, 24, 28, values, 19⟩

private def input : Data 28 :=
  ⟨fun i => if i.val = 10 then 3 else if i.val = 11 then 5
    else if i.val = 12 then encode 19 else if i.val = 15 then 2
    else if i.val = 16 then 2 else if i.val = 17 then 20
    else if i.val = 18 then 24 else if i.val = 19 then 28 else 0,
    fun a => if 5 ≤ a ∧ a < 8 then encode (values (a - 5)) else 0⟩

/-- All input registers and memory are actual words at the claimed target width. -/
example : input.Bounded 10 := by
  constructor
  · intro i
    simp only [input, Fits]
    split_ifs <;> decide
  · intro a
    by_cases ha : 5 ≤ a ∧ a < 8
    · have : a = 5 ∨ a = 6 ∨ a = 7 := by omega
      rcases this with rfl | rfl | rfl <;> decide
    · simp [input, ha, Fits]

/-- Execute every matrix cell, including invalid indices, and inspect all twelve output words. -/
example : (Code.eval 10 4 Fill.program input).map
    (fun yn => (List.range 12).map fun i => yn.1.mem (20 + i)) =
      some [18, 5, 9, 38, 9, 38, 5, 38, 8, 38, 38, 38] := by decide

-- Reducing the flat interpreter traverses over 500 individual instructions.
set_option maxRecDepth 4096 in
/-- The assembled instruction list, including the charged halt, terminates within the bound. -/
example : (WordRAM.run 10 (Fill.program.program Cell.cell) (131 * 4 + 6)
    ⟨0, input⟩).map Prod.fst = some 4 := by decide

/-- The quantitative theorem has satisfiable hypotheses on the same executed input. -/
example : ∃ y, ExecWithin 10 Fill.program input y 529 ∧
    y.mem = layout.filled input.mem 4 ∧ y.mem 5 = encode 9 ∧ y.mem 32 = 0 := by
  obtain ⟨y, he, hm, -⟩ := Fill.exec (w := 8) layout input
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by
      intro i hi
      change i < 3 at hi
      have h : 5 ≤ 5 + i ∧ 5 + i < 8 := by omega
      simp only [input, layout, h, true_and, ↓reduceIte, Nat.add_sub_cancel_left])
    (by decide) (by decide) (by decide)
    (by
      intro i hi
      change i < 3 at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  exact ⟨y, he, hm, by rw [hm]; decide, by rw [hm]; decide⟩

/-- The memory theorem identifies the completed matrices with the mathematical reduction. -/
example : layout.filled input.mem 4 (20 + 0 * 2 + 1) =
      encode (Algorithms.ThreeSum.weightAB 3 values 19 (0 : Fin 2) 1) ∧
    layout.filled input.mem 4 (24 + 1 * 2 + 0) =
      encode (Algorithms.ThreeSum.weightBC 3 2 values 19 (1 : Fin 2) 0) ∧
    layout.filled input.mem 4 (28 + 0 * 2 + 0) =
      encode (Algorithms.ThreeSum.weightAC 3 2 values 19 (0 : Fin 2) 0) :=
  layout.matrices_filled input.mem (by decide) (by decide) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2)

/-- Zero-side matrices skip the loop and pay only initialization and the final test. -/
example : (Code.eval 10 0 Fill.program (input.set Cell.side 0)).map
    (fun yn => (yn.1.regs Cell.cell, yn.2)) = some (0, 5) := by decide

end ComplexityTests.ThreeSumFill
