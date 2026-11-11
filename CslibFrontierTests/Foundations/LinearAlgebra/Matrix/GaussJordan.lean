/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.GaussJordan
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for staged Gauss–Jordan elimination

A `3 × 3` matrix over `ZMod 2` whose rows sum to zero: `reduce` computes its reduced form, which
has two nonzero rows, so the matrix has rank `2`. The identity is fixed by `reduce`, a `1 × 2`
example shows that one nonzero row may own several columns, and the division-free `ZMod 2` form of
a stage agrees with `stage` on the first example.
-/

public section

namespace Cslib.LinearAlgebra.GaussJordanTests

open Matrix Matrix.GaussJordan

/-- A rank-`2` matrix over `ZMod 2`: the third row is the sum of the first two. -/
def gf2Example : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 1, 0; 0, 1, 1; 1, 0, 1]

/-- The first column's pivot is row `0`. -/
example : pivotRow gf2Example 0 = some 0 := by
  decide +kernel

/-- Gauss–Jordan elimination clears the first two columns and leaves a zero row. -/
example : reduce gf2Example = !![1, 0, 1; 0, 1, 1; 0, 0, 0] := by
  decide +kernel

/-- The matrix has rank `2`, read off from the two nonzero rows of its reduced form. -/
example : gf2Example.rank = 2 := by
  rw [rank_eq_card_reduce_ne_zero]
  decide +kernel

/-- The identity has no row to clear. -/
example : reduce (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
  decide +kernel

/-- One nonzero row may own several columns: `!![1, 1]` is already reduced, and its single
nonzero row is the only nonzero entry in both columns, but the rank is `1`. -/
example : reduce !![(1 : ZMod 2), 1] = !![1, 1] ∧ (!![(1 : ZMod 2), 1]).rank = 1 := by
  refine ⟨by decide +kernel, ?_⟩
  rw [rank_eq_card_reduce_ne_zero]
  decide +kernel

/-- The division-free form clears row `2` of the first column: it adds the pivot row `0`. -/
example : stage gf2Example 0 2 0 = 0 := by
  rw [stage_apply_zmod_two]
  decide +kernel

end Cslib.LinearAlgebra.GaussJordanTests
