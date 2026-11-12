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
* `Matrix.det_submatrix_eq_of_sum_eq_zero`: all `(n - 1) × (n - 1)` principal minors of a matrix
  whose row sums and column sums vanish are equal.
* `Matrix.det_laplacian_submatrix_eq`: all reduced Laplacian determinants of a balanced weight
  matrix are equal across roots.
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

/-- For a matrix `L` whose row sums and column sums all vanish, all principal cofactors obtained by
deleting a single row and matching column are equal. -/
theorem det_submatrix_eq_of_sum_eq_zero {R V : Type*} [CommRing R] [Fintype V] [DecidableEq V]
    (L : Matrix V V R) (hrow : ∀ u, ∑ v, L u v = 0) (hcol : ∀ v, ∑ u, L u v = 0) (u v : V) :
    (L.submatrix (Subtype.val : {x // x ≠ u} → V) Subtype.val).det =
      (L.submatrix (Subtype.val : {x // x ≠ v} → V) Subtype.val).det := by
  by_cases huv : u = v
  · subst huv
    rfl
  · set v' : {x // x ≠ u} := ⟨v, fun h => huv h.symm⟩
    set M : Matrix {x // x ≠ u} {x // x ≠ u} R := L.submatrix Subtype.val Subtype.val
    have hsum_col : ∀ j : {x // x ≠ u}, (∑ k : {x // x ≠ u}, M k j) = - L u j := fun j => by
      have hs := Fintype.sum_eq_add_sum_subtype_ne (fun x => L x j) u
      rw [hcol j] at hs
      exact eq_neg_of_add_eq_zero_right hs.symm
    set N : Matrix {x // x ≠ u} {x // x ≠ u} R := M.updateRow v' (fun j : {x // x ≠ u} => - L u j)
    have hMN : M.det = N.det := by
      have h := det_updateRow_sum M v' (fun _ => (1 : R))
      simp only [one_smul] at h
      have hs : (∑ k : {x // x ≠ u}, M k) = fun j : {x // x ≠ u} => - L u j := by
        ext j
        exact (Finset.sum_apply j Finset.univ M).trans (hsum_col j)
      rw [hs] at h
      exact h.symm
    set P : Matrix {x // x ≠ u} {x // x ≠ u} R := (Nᵀ.updateRow v' (∑ k : {x // x ≠ u}, Nᵀ k))ᵀ
    have hNP : N.det = P.det := by
      have h := det_updateRow_sum Nᵀ v' (fun _ => (1 : R))
      simp only [one_smul] at h
      rw [← det_transpose N, ← h, det_transpose]
    let e : {x // x ≠ u} ≃ {x // x ≠ v} :=
      { toFun := fun x => ⟨Equiv.swap u v x, fun hx => x.2 ((Equiv.swap u v).injective
          (by simp only [hx, Equiv.swap_apply_left]))⟩
        invFun := fun y => ⟨Equiv.swap u v y, fun hy => y.2 ((Equiv.swap u v).injective
          (by simp only [hy, Equiv.swap_apply_right]))⟩
        left_inv := fun x => Subtype.ext (by simp only [Equiv.swap_apply_self])
        right_inv := fun y => Subtype.ext (by simp only [Equiv.swap_apply_self]) }
    let s : {x // x ≠ u} → R := fun x => if x = v' then -1 else 1
    have hcol_sum : ∀ i : {x // x ≠ u},
        (∑ k : {x // x ≠ u}, Nᵀ k) i = if i = v' then L u u else - L i u := fun i => by
      refine (Finset.sum_apply i Finset.univ (fun k => Nᵀ k)).trans ?_
      by_cases hi : i = v'
      · subst hi
        have hs := Fintype.sum_eq_add_sum_subtype_ne (fun y => L u y) u
        rw [hrow u] at hs
        simp only [↓reduceIte, transpose_apply, N, updateRow_self]
        rw [Finset.sum_neg_distrib]
        exact (eq_neg_of_add_eq_zero_left hs.symm).symm
      · have hs := Fintype.sum_eq_add_sum_subtype_ne (fun y => L i y) u
        rw [hrow i] at hs
        simp only [hi, ↓reduceIte, transpose_apply, N, updateRow_ne hi, M, submatrix_apply]
        exact eq_neg_of_add_eq_zero_right hs.symm
    have hP : P = diagonal s * ((L.submatrix Subtype.val Subtype.val).submatrix e e) *
        diagonal s := by
      ext i j
      simp only [P, transpose_apply, updateRow_apply, hcol_sum, N, M, submatrix_apply,
        diagonal_mul, mul_diagonal, e, Equiv.coe_fn_mk, s]
      by_cases hi : i = v' <;> by_cases hj : j = v'
      · subst hi hj
        simp only [↓reduceIte, v', Equiv.swap_apply_right, neg_one_mul, mul_neg, mul_one, neg_neg]
      · subst hi
        have hj' : (j : V) ≠ v := fun h => hj (Subtype.ext h)
        have hj_swap : Equiv.swap u v (j : V) = j := Equiv.swap_apply_of_ne_of_ne j.2 hj'
        simp only [hj, ↓reduceIte, hj_swap, v', Equiv.swap_apply_right, neg_one_mul, mul_one]
      · subst hj
        have hi' : (i : V) ≠ v := fun h => hi (Subtype.ext h)
        have hi_swap : Equiv.swap u v (i : V) = i := Equiv.swap_apply_of_ne_of_ne i.2 hi'
        simp only [hi, ↓reduceIte, hi_swap, v', Equiv.swap_apply_right, one_mul, mul_neg, mul_one]
      · have hi' : (i : V) ≠ v := fun h => hi (Subtype.ext h)
        have hj' : (j : V) ≠ v := fun h => hj (Subtype.ext h)
        have hi_swap : Equiv.swap u v (i : V) = i := Equiv.swap_apply_of_ne_of_ne i.2 hi'
        have hj_swap : Equiv.swap u v (j : V) = j := Equiv.swap_apply_of_ne_of_ne j.2 hj'
        simp only [hi, hj, ↓reduceIte, hi_swap, hj_swap, one_mul, mul_one]
    have hs_sq : (∏ i : {x // x ≠ u}, s i) * (∏ i : {x // x ≠ u}, s i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      by_cases hi : i = v' <;> simp only [s, hi, ↓reduceIte, mul_one, neg_mul, one_mul, neg_neg]
    rw [hMN, hNP, hP, det_mul, det_mul, det_diagonal, mul_right_comm, hs_sq, one_mul,
      det_submatrix_equiv_self]

/-- For a balanced weight matrix `A` (`∑ w, A v w = ∑ u, A u v`), all reduced Laplacian
determinants are equal across roots. -/
theorem det_laplacian_submatrix_eq {R V : Type*} [CommRing R] [Fintype V] [DecidableEq V]
    (A : Matrix V V R) (hbal : ∀ v, ∑ w, A v w = ∑ u, A u v) (u v : V) :
    (A.laplacian.submatrix (Subtype.val : {x // x ≠ u} → V) Subtype.val).det =
      (A.laplacian.submatrix (Subtype.val : {x // x ≠ v} → V) Subtype.val).det := by
  refine det_submatrix_eq_of_sum_eq_zero A.laplacian (fun x => ?_) (fun y => ?_) u v
  · simp only [laplacian_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, sub_self]
  · simp only [laplacian_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, hbal y, sub_self]

end Matrix
