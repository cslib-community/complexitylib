/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/Laplacian.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Laplacian of a weight matrix

A square matrix `A : Matrix κ κ R` can be read as the arc weights of a weighted digraph on `κ`.
Its *Laplacian* `Matrix.laplacian A` is the diagonal matrix of the row sums of `A`, minus `A`.
Row `u` of the Laplacian is `∑ v, A u v • (eᵤ - eᵥ)`. In particular every row sums to zero, and
the diagonal entries `A u u` (loops) cancel. For the adjacency matrix of a simple graph this is
Mathlib's `SimpleGraph.lapMatrix`. For a digraph it is the out-degree Laplacian.

The determinants of its principal minors count spanning trees and arborescences. These are the
matrix-tree theorems in `CslibFrontier.Foundations.Combinatorics.SimpleGraph.MatrixTree` and
`CslibFrontier.Foundations.Combinatorics.Digraph.MatrixTree`. Both proofs evaluate determinants of
matrices that become triangular after the index set is ordered by a weight. The determinant of
such a matrix is the product of its diagonal (`Matrix.det_eq_prod_diag_of_weight`).

## Main definitions

* `Matrix.laplacian`: the Laplacian `diagonal (fun u => ∑ v, A u v) - A`.

## Main results

* `Matrix.laplacian_apply`: the entries of the Laplacian.
* `Matrix.det_eq_prod_diag_of_weight`: a matrix whose nonzero off-diagonal entries strictly
  increase a natural-number weight has determinant the product of its diagonal entries.
-/

public section

namespace Matrix

variable {κ R : Type*} [Fintype κ] [DecidableEq κ]

/-- The **Laplacian** of a square matrix `A`, read as the arc weights of a weighted digraph: the
diagonal matrix of the row sums of `A`, minus `A`. Its row `u` is `∑ v, A u v • (eᵤ - eᵥ)`, so the
diagonal entries `A u u` (loops) cancel. -/
def laplacian [AddCommGroup R] (A : Matrix κ κ R) : Matrix κ κ R :=
  diagonal (fun u => ∑ v, A u v) - A

/-- The entries of the Laplacian. -/
theorem laplacian_apply [AddCommGroup R] (A : Matrix κ κ R) (u v : κ) :
    A.laplacian u v = (if u = v then ∑ w, A u w else 0) - A u v := by
  rw [laplacian, Matrix.sub_apply, diagonal_apply]

/-- A square matrix whose off-diagonal nonzero entries `M i j` all satisfy `d i < d j` for a
weight `d` has determinant the product of its diagonal entries. -/
theorem det_eq_prod_diag_of_weight [CommRing R] (M : Matrix κ κ R) (d : κ → ℕ)
    (hM : ∀ i j, i ≠ j → M i j ≠ 0 → d i < d j) :
    M.det = ∏ i, M i i := by
  rw [det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra! h
      exact hσ (Equiv.ext h)
    suffices ∃ j, M (σ j) j = 0 by
      obtain ⟨j, hj⟩ := this
      rw [Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hj, smul_zero]
    by_contra! h
    have hle : ∀ j, d (σ j) ≤ d j := fun j => by
      by_cases hj : σ j = j
      · rw [hj]
      · exact (hM _ _ hj (h j)).le
    have hsum : ∑ j, d (σ j) = ∑ j, d j := Equiv.sum_comp σ d
    have := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hM _ _ hi (h i)⟩
    omega
  · simp

end Matrix
