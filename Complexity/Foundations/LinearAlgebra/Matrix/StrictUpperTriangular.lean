/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, beside `LinearAlgebra/Matrix/Block`)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Strictly upper triangular matrices

A square matrix over an ordered index type is *strictly upper triangular* when its entry at
`(i, j)` vanishes unless `i < j` (`Matrix.IsStrictUpperTriangular`). Mathlib's
`Matrix.IsUpperTriangular` allows a nonzero diagonal; the strict version is closed under sums,
negation, differences and products, and `1 + E` then has determinant one.

## Main definitions

* `Matrix.IsStrictUpperTriangular`: entries vanish unless the row index is below the column index.

## Main results

* `Matrix.IsStrictUpperTriangular.isUpperTriangular`: strict implies Mathlib's non-strict notion.
* `Matrix.IsStrictUpperTriangular.add`, `.neg`, `.sub`, `.mul`: closure properties.
* `Matrix.IsStrictUpperTriangular.det_one_add`: `det (1 + E) = 1` for strictly upper triangular
  `E`.
-/

public section

namespace Matrix

section Triangular

variable {V R : Type*}

/-- A square matrix is *strictly upper triangular* when its entry at `(i, j)` vanishes unless
`i < j`. For the time-layered transition matrices of a machine, ordered by time, this says that
every transition moves strictly forward. -/
@[expose] def IsStrictUpperTriangular [LT V] [Zero R] (M : Matrix V V R) : Prop :=
  ∀ ⦃i j⦄, ¬ i < j → M i j = 0

namespace IsStrictUpperTriangular

variable [Preorder V] {M N : Matrix V V R}

/-- A strictly upper triangular matrix is upper triangular. -/
theorem isUpperTriangular [Zero R] (h : M.IsStrictUpperTriangular) : M.IsUpperTriangular :=
  fun _ _ hji => h (lt_asymm hji)

theorem add [AddZeroClass R] (hM : M.IsStrictUpperTriangular) (hN : N.IsStrictUpperTriangular) :
    (M + N).IsStrictUpperTriangular := fun i j hij => by
  simp only [Matrix.add_apply, hM hij, hN hij, add_zero]

theorem neg [SubtractionMonoid R] (hM : M.IsStrictUpperTriangular) :
    (-M).IsStrictUpperTriangular := fun i j hij => by
  simp only [Matrix.neg_apply, hM hij, neg_zero]

theorem sub [SubtractionMonoid R] (hM : M.IsStrictUpperTriangular)
    (hN : N.IsStrictUpperTriangular) : (M - N).IsStrictUpperTriangular := fun i j hij => by
  simp only [Matrix.sub_apply, hM hij, hN hij, sub_zero]

theorem mul [Fintype V] [NonUnitalNonAssocSemiring R] (hM : M.IsStrictUpperTriangular)
    (hN : N.IsStrictUpperTriangular) : (M * N).IsStrictUpperTriangular := fun i j hij => by
  refine Finset.sum_eq_zero fun k _ => ?_
  change M i k * N k j = 0
  by_cases hik : i < k
  · rw [hN fun hkj => hij (hik.trans hkj), mul_zero]
  · rw [hM hik, zero_mul]

/-- `1 + E` has determinant one when `E` is strictly upper triangular. -/
theorem det_one_add {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [CommRing R]
    {E : Matrix V V R} (h : E.IsStrictUpperTriangular) : (1 + E).det = 1 := by
  have hT : (1 + E).IsUpperTriangular := fun i j (hji : j < i) => by
    rw [Matrix.add_apply, one_apply_ne (ne_of_lt hji).symm, h.isUpperTriangular hji, add_zero]
  rw [det_of_isUpperTriangular hT]
  exact Finset.prod_eq_one fun i _ => by
    rw [Matrix.add_apply, one_apply_eq, h (lt_irrefl i), add_zero]

end IsStrictUpperTriangular

end Triangular

end Matrix
