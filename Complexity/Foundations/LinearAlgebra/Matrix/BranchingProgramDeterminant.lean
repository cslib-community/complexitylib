/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `LinearAlgebra/Matrix/Adjugate.lean`)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Branching programs as determinants

Let `N` be the weighted adjacency matrix of a directed acyclic graph on the vertices
`0, …, m`, numbered in topological order, so `N i j = 0` unless `i < j`. The total weights
`q j` of the paths from `0` to `j` satisfy `q = Pi.single 0 1 + q ᵥ* N`. The matrix `1 - N` is
upper unitriangular, so it has determinant `1` and its inverse is its adjugate. Hence
`q = Pi.single 0 1 ᵥ* (1 - N)⁻¹` is the first row of the adjugate. Its last entry, the value
of the branching program, is the `m × m` determinant of `N - 1` with its last row and first
column deleted (`Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul`). This is the step
from algebraic branching programs to determinants in Grenet's construction
(`Matrix.permanent_eq_det_grenetMatrix`). The general form for any `B` with `det B = 1` is
`Matrix.eq_det_neg_submatrix_of_vecMul_eq_single`.

## Main results

* `Matrix.eq_det_neg_submatrix_of_vecMul_eq_single`: if `q ᵥ* B = Pi.single 0 1` and
  `det B = 1`, then `q (last m)` is the determinant of `-B` without its last row and first column.
* `Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul`: the value of a branching program is
  an `m × m` determinant.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

/-- If `q ᵥ* B = Pi.single 0 1` and `det B = 1`, then `q (last m)` is the `m × m` determinant
of `-B` with its last row and first column deleted. -/
theorem eq_det_neg_submatrix_of_vecMul_eq_single (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hB : B.det = 1) {q : Fin (m + 1) → R} (hq : q ᵥ* B = Pi.single 0 1) :
    q (Fin.last m) = (-B.submatrix Fin.castSucc Fin.succ).det := by
  have hq' : q = Pi.single 0 1 ᵥ* B.adjugate := by
    rw [← hq, vecMul_vecMul, mul_adjugate, hB, one_smul, vecMul_one]
  rw [hq', single_one_vecMul, row_apply, adjugate_fin_succ_eq_det_submatrix, det_neg,
    Fintype.card_fin, Fin.succAbove_last, Fin.succAbove_zero]
  simp

/-- **Branching programs as determinants.** Let `N` be the weighted adjacency matrix of a
directed acyclic graph on `0, …, m` in topological order (`N i j = 0` unless `i < j`), and let
`q j` be the total weight of the paths from `0` to `j`, characterized by
`q = Pi.single 0 1 + q ᵥ* N`. Then the total weight `q (last m)` of the paths from the source
`0` to the sink `last m` is the determinant of the `m × m` matrix `N - 1` with its last row and
first column deleted. -/
theorem eq_det_submatrix_sub_one_of_eq_single_add_vecMul
    (N : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (hN : ∀ i j, j ≤ i → N i j = 0)
    {q : Fin (m + 1) → R} (hq : q = Pi.single 0 1 + q ᵥ* N) :
    q (Fin.last m) = ((N - 1).submatrix Fin.castSucc Fin.succ).det := by
  have hdet : (1 - N).det = 1 := by
    rw [det_of_isUpperTriangular]
    · simp [hN]
    · intro i j hij
      have hij' : j < i := hij
      rw [Matrix.sub_apply, one_apply_ne hij'.ne', hN i j hij'.le, sub_zero]
  rw [eq_det_neg_submatrix_of_vecMul_eq_single (1 - N) hdet (q := q)]
  · congr 1
    ext i j
    simp
  · rw [vecMul_sub, vecMul_one]
    nth_rw 1 [hq]
    abel

end Matrix
