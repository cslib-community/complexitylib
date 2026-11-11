/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Yates

/-!
# Tests for Yates's algorithm on tables

Concrete runs of `Complexity.Algorithms.Lean.Yates`:

* the cells of subsets (`maskIndex`, `maskSet`);
* the fast zeta and Möbius transforms on tables with `4` and `8` cells, their exact tick counts,
  and the degenerate table with one cell (`n = 0`, no passes);
* a run checked against `getElem_ret_zetaM_maskIndex`.
-/

namespace ComplexityTests.Algorithms.Lean.Yates

open Cslib.Algorithms.Lean.Yates Cslib.BitString

/-! ### Cells -/

/-- The cell of `{0, 2} ⊆ Fin 3` is `0b101 = 5`. -/
example : (maskIndex ({0, 2} : Finset (Fin 3)) : ℕ) = 5 := by decide +kernel

/-- The set of cell `6 = 0b110` is `{1, 2}`. -/
example : maskSet 3 6 = {1, 2} := by decide +kernel

/-! ### Zeta and Möbius transforms -/

/-- Cells `∅, {0}, {1}, {0, 1}` hold `1, 2, 3, 4`; their subset sums are `1, 3, 4, 10`. -/
example : (zetaM (n := 2) #v[1, 2, 3, 4]).ret = #v[1, 3, 4, 10] := by decide +kernel

/-- Two passes over four cells: `2 * 2 ^ 2 = 8` ticks. -/
example : (zetaM (n := 2) #v[1, 2, 3, 4]).time = 8 := by decide +kernel

/-- The fast Möbius transform inverts it. -/
example : (mobiusM (n := 2) #v[(1 : ℤ), 3, 4, 10]).ret = #v[1, 2, 3, 4] := by decide +kernel

/-- Eight cells, all `1`: the subset sums are the powers of two `2 ^ #S`. -/
example : (zetaM (n := 3) (Vector.replicate 8 1)).ret = #v[1, 2, 2, 4, 2, 4, 4, 8] := by
  decide +kernel

/-- Three passes over eight cells: `24` ticks. -/
example : (zetaM (n := 3) (Vector.replicate 8 1)).time = 24 := by decide +kernel

/-- Edge case `n = 0`: one cell, no passes, no ticks. -/
example : (zetaM (n := 0) #v[5]).ret = #v[5] ∧ (zetaM (n := 0) #v[5]).time = 0 := by
  decide +kernel

/-- The run above, read at the cell of `{0, 1}`, against `getElem_ret_zetaM_maskIndex`. -/
example : subsetZeta (fun T => (#v[1, 2, 3, 4] : Vector ℕ (2 ^ 2))[(maskIndex T : ℕ)])
    (Finset.univ : Finset (Fin 2)) = 10 := by
  rw [← getElem_ret_zetaM_maskIndex]
  decide +kernel

end ComplexityTests.Algorithms.Lean.Yates
