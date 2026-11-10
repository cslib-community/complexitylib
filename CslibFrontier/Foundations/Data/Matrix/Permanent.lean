/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin

/-!
# Laplace expansion of the permanent

Mathlib proves cofactor expansion of the determinant along the first row and column
(`Matrix.det_succ_row_zero`, `Matrix.det_succ_column_zero`). This file proves the analogous
expansions of the permanent, without signs: for an `(n + 1) × (n + 1)` matrix `A`,
`A.permanent = ∑ j, A 0 j * (A.submatrix Fin.succ j.succAbove).permanent`.

## Main results

* `Matrix.permanent_succ_column_zero`: Laplace expansion of the permanent along column 0.
* `Matrix.permanent_succ_row_zero`: Laplace expansion of the permanent along row 0.
-/

public section

namespace Matrix

open Equiv Finset Fintype

variable {R : Type*} [CommSemiring R]

/-- **Laplace expansion of the permanent along column 0.** -/
theorem permanent_succ_column_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent = ∑ i : Fin (n + 1), A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp [Fin.prod_univ_succ, Matrix.permanent, Finset.mul_sum]
  · rw [← permanent_permute_cols i.cycleRange, Matrix.permanent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Fin.prod_univ_succ, Fin.succAbove_cycleRange]

/-- **Laplace expansion of the permanent along row 0.** -/
theorem permanent_succ_row_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent = ∑ j : Fin (n + 1), A 0 j * (A.submatrix Fin.succ j.succAbove).permanent := by
  rw [← permanent_transpose A, permanent_succ_column_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← permanent_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

end Matrix
