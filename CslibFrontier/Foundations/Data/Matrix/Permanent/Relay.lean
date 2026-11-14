/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Matrix.Permanent
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import Mathlib.Algebra.BigOperators.Fin

/-!
# Laplace expansion along any row and relay vertices

`Matrix.permanent_succ_row` and `Matrix.permanent_succ_column` expand the permanent of an
`(n + 1) × (n + 1)` matrix along an arbitrary row or column, generalizing the expansions along
row and column `0` in `CslibFrontier.Foundations.Data.Matrix.Permanent`. As a consequence, the
permanent is affine in each single entry (`Matrix.permanent_add_single`).

Read a square matrix `M` as the weighted adjacency matrix of a digraph, so that its permanent is
the total weight of its cycle covers. A *relay vertex* is a vertex with a self-loop of weight `1`,
one incoming edge `s → z` of weight `a` and one outgoing edge `z → t` of weight `b`. A cycle
cover either uses the self-loop at `z`, or passes `s → z → t`. Removing `z` and adding `a * b` to
the weight of `s → t` therefore preserves the permanent (`Matrix.permanent_eq_of_relay`). This is
the local replacement behind the reduction from nonnegative integer matrices to 0/1 matrices
[Valiant][Valiant1979], [Goldreich, proof of Proposition 6.22][Goldreich2007Draft].

## Main results

* `Matrix.permanent_succ_row`, `Matrix.permanent_succ_column`: Laplace expansions.
* `Matrix.permanent_add_single`: adding `c` to entry `(s, t)` adds `c` times its minor.
* `Matrix.permanent_eq_of_relay`: removing a relay vertex.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

public section

namespace Matrix

open Finset

variable {R : Type*} [CommSemiring R]

/-- The reindexing of `Fin (n + 1)` sending `0` to `s` and `i.succ` to `s.succAbove i`. -/
private def rowFront {n : ℕ} (s : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) :=
  (finSuccEquiv n).trans (finSuccEquiv' s).symm

private theorem rowFront_zero {n : ℕ} (s : Fin (n + 1)) : rowFront s 0 = s := by
  simp [rowFront, finSuccEquiv_zero, finSuccEquiv'_symm_none]

private theorem rowFront_succ {n : ℕ} (s : Fin (n + 1)) (i : Fin n) :
    rowFront s i.succ = s.succAbove i := by
  simp [rowFront, finSuccEquiv_succ, finSuccEquiv'_symm_some]

/-- **Laplace expansion of the permanent along row `s`.** -/
theorem permanent_succ_row {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1)) :
    A.permanent = ∑ j : Fin (n + 1), A s j * (A.submatrix s.succAbove j.succAbove).permanent := by
  rw [← permanent_submatrix_equiv_equiv (rowFront s) (Equiv.refl _) A,
    permanent_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [submatrix_apply, rowFront_zero, Equiv.refl_apply]
  congr 2

/-- **Laplace expansion of the permanent along column `t`.** -/
theorem permanent_succ_column {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (t : Fin (n + 1)) :
    A.permanent = ∑ i : Fin (n + 1), A i t * (A.submatrix i.succAbove t.succAbove).permanent := by
  rw [← permanent_transpose A, permanent_succ_row _ t]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← permanent_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

/-- **The permanent is affine in each entry**: adding `c` to entry `(s, t)` adds `c` times the
`(s, t)` minor. -/
theorem permanent_add_single {n : ℕ} (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (s t : Fin (n + 1)) (c : R) :
    (X + Matrix.of fun i j => if i = s ∧ j = t then c else 0).permanent =
      X.permanent + c * (X.submatrix s.succAbove t.succAbove).permanent := by
  rw [permanent_succ_row _ s, permanent_succ_row X s]
  have hminor : ∀ j : Fin (n + 1),
      ((X + Matrix.of fun i j => if i = s ∧ j = t then c else 0).submatrix s.succAbove
        j.succAbove) = X.submatrix s.succAbove j.succAbove := by
    intro j
    ext i l
    simp [Fin.succAbove_ne]
  have hentry : ∀ j, (X + Matrix.of fun i j => if i = s ∧ j = t then c else 0) s j =
      X s j + if j = t then c else 0 := fun j => by simp
  simp_rw [hminor, hentry, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Removing a relay vertex.** If the last vertex of `M` has a self-loop of weight `1`, its only
other outgoing edge goes to `t` with weight `b`, and its only other incoming edge comes from `s`
with weight `a`, then deleting it and adding `a * b` to entry `(s, t)` preserves the
permanent. -/
theorem permanent_eq_of_relay {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (s t : Fin (n + 1)) (a b : R) (hll : M (Fin.last _) (Fin.last _) = 1)
    (hrow : ∀ j : Fin (n + 1), M (Fin.last _) j.castSucc = if j = t then b else 0)
    (hcol : ∀ i : Fin (n + 1), M i.castSucc (Fin.last _) = if i = s then a else 0) :
    M.permanent = (M.submatrix Fin.castSucc Fin.castSucc +
      Matrix.of fun i j => if i = s ∧ j = t then a * b else 0).permanent := by
  rw [permanent_add_single, permanent_succ_row M (Fin.last _), Fin.sum_univ_castSucc]
  simp only [hll, hrow, Fin.succAbove_last, one_mul, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [add_comm]
  congr 1
  rw [permanent_succ_column _ (Fin.last n)]
  have hlast : (t.castSucc).succAbove (Fin.last n) = Fin.last (n + 1) := by
    rw [Fin.succAbove_of_le_castSucc _ _ (by simpa using Fin.le_last t), Fin.succ_last]
  simp only [submatrix_apply, hlast, hcol, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Fin.succAbove_last]
  rw [← mul_assoc, mul_comm b a]
  congr 2
  ext i j
  simp

end Matrix
