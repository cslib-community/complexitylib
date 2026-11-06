/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import Complexity.Foundations.LinearAlgebra.Tensor.Polynomial

/-! # Finite tensors: checked instances

The bilinear map of `mm 2 2 2` on the entries of two `2 × 2` matrices is their product, the full
product tensor `full 2 2` multiplies `1 + 2 z` by `3 + 4 z` into `3 + 10 z + 8 z ^ 2`, the unit
tensor is the diagonal, and the trivial rank bounds `Rank 8 (mm 2 2 2)` and `Rank 3 (full 2 2)`
are instances of `rank_mm` and `rank_full`. -/

namespace ComplexityTests.TensorBasic

open Cslib.Tensor

/-- `unit 2` is the diagonal tensor. -/
example : (unit 2 : Cslib.Tensor ℚ _ _ _) 0 0 0 = 1 ∧ (unit 2 : Cslib.Tensor ℚ _ _ _) 0 1 0 = 0 := by
  simp [unit]

/-- The entry `(0, 1)` of a `2 × 2` matrix product, through `bil_mm`:
`[[1, 2], [3, 4]] * [[5, 6], [7, 8]]` has entry `(0, 1)` equal to `1 * 6 + 2 * 8 = 22`. -/
example :
    (mm 2 2 2 : Cslib.Tensor ℚ _ _ _).bil (fun p => ![![1, 2], ![3, 4]] p.1 p.2)
      (fun p => ![![5, 6], ![7, 8]] p.1 p.2) (0, 1) = 22 := by
  rw [bil_mm]
  simp [Fin.sum_univ_two]
  norm_num

/-- `(1 + 2 z) (3 + 4 z) = 3 + 10 z + 8 z ^ 2`: the coefficient `1` of the full product. -/
example : (full 2 2 : Cslib.Tensor ℚ _ _ _).bil ![1, 2, 0] ![3, 4, 0] 1 = 10 := by
  simp [bil, full, Fin.sum_univ_succ]
  norm_num

/-- The trivial algorithm for `2 × 2` matrices uses `8` multiplications. -/
example : Rank 8 (mm 2 2 2 : Cslib.Tensor ℚ _ _ _) :=
  rank_mm 2 2 2

/-- Multiplying two linear polynomials needs at most `3` multiplications (evaluation at three
points). -/
example : Rank 3 (full 2 2 : Cslib.Tensor ℚ _ _ _) :=
  rank_full 2 2

/-- The middle product has the same rank bound. -/
example : Rank 3 (mid 2 2 : Cslib.Tensor ℚ _ _ _) :=
  rank_mid 2 2

end ComplexityTests.TensorBasic
