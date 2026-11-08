/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Hessians of the generic determinant)

public import Complexity.Foundations.Data.MvPolynomial.HessianChainRule
public import Complexity.Foundations.LinearAlgebra.Matrix.PartialDerivatives
import Complexity.Foundations.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Hessians of the determinant at singular matrices

The Hessian of a permutation sum `∑ σ, w σ • ∏ i, X (σ i, i)` at `x`, at the entries `a` and
`b`, sums the weighted products over the remaining columns of the permutations through `a` and
`b`. If a column `z` of `x` vanishes, every such product for the determinant vanishes unless `a`
or `b` lies in column `z`, so the Hessian is supported on `2 · m` rows and columns and has rank at
most `2 · m`. A general singular matrix becomes one with a zero column after right multiplication
by an invertible matrix whose column `z` spans the kernel. That substitution is linear and
multiplies the determinant by a nonzero constant. By the chain rule
(`MvPolynomial.rank_hessian_aeval_le`), the Hessian of the determinant of any `m × m` matrix of
affine polynomials has rank at most `2 · m` at every zero of the determinant
[Mignon and Ressayre][MignonRessayre2004]. The statements hold over every field.

## Main results

* `Matrix.hessian_sum_smul_prod_X`: the Hessian of a permutation sum.
* `Matrix.rank_hessian_det_mvPolynomialX_le`: the generic determinant's Hessian has rank at most
  `2 · m` at a singular matrix.
* `Matrix.rank_hessian_det_le`: the same bound for the determinant of a matrix of affine
  polynomials at a zero of its determinant.

## References

* [T. Mignon, N. Ressayre, *A quadratic bound for the determinant and permanent
  problem*][MignonRessayre2004]
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], chapter "Determinantal Complexity Lower Bounds",
  Lemma `lem:MR-det-ub`.
-/

public section

namespace Matrix

open MvPolynomial Equiv Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

/-- The Hessian of a weighted permutation sum. -/
theorem hessian_sum_smul_prod_X (w : Perm ι → K) (x : ι × ι → K) (a b : ι × ι) :
    hessian x (∑ σ : Perm ι, w σ • ∏ i, X (σ i, i) : MvPolynomial (ι × ι) K) a b =
      ∑ σ : Perm ι, if a.2 ≠ b.2 ∧ σ a.2 = a.1 ∧ σ b.2 = b.1 then
        w σ * ∏ i ∈ (univ.erase b.2).erase a.2, x (σ i, i) else 0 := by
  obtain ⟨r, c⟩ := a
  obtain ⟨r', c'⟩ := b
  simp only [hessian, map_sum, Derivation.map_smul, pderiv_prod_X]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h' : σ c' = r'
  · simp only [mem_univ, h', and_self, ite_true, pderiv_prod_X, mem_erase]
    by_cases h : c ≠ c' ∧ σ c = r
    · simp [h]
    · rw [ite_eq_right_iff.2 (fun h'' => absurd ⟨h''.1.1, h''.2⟩ h),
        ite_eq_right_iff.2 (fun h'' => absurd ⟨h''.1, h''.2.1⟩ h)]
      simp
  · simp [h']

/-- The generic determinant as a signed permutation sum. -/
theorem det_mvPolynomialX_eq_sum :
    (mvPolynomialX ι ι K).det = ∑ σ : Perm ι, ((Perm.sign σ : ℤ) : K) • ∏ i, X (σ i, i) := by
  simp [det_apply, Units.smul_def, Int.cast_smul_eq_zsmul]

/-- The generic permanent as a permutation sum. -/
theorem permanent_mvPolynomialX_eq_sum :
    (mvPolynomialX ι ι K).permanent = ∑ σ : Perm ι, (1 : K) • ∏ i, X (σ i, i) := by
  simp [permanent]

/-- If column `z` of `x` vanishes, the Hessian of the generic determinant at `x` vanishes off the
rows and columns indexed by column `z`. -/
private theorem hessian_det_mvPolynomialX_eq_zero {x : ι × ι → K} {z : ι}
    (hz : ∀ i, x (i, z) = 0) {a b : ι × ι} (ha : a.2 ≠ z) (hb : b.2 ≠ z) :
    hessian x (mvPolynomialX ι ι K).det a b = 0 := by
  rw [det_mvPolynomialX_eq_sum, hessian_sum_smul_prod_X]
  refine Finset.sum_eq_zero fun σ _ => ?_
  split_ifs
  · rw [Finset.prod_eq_zero (i := z) (by simp [Ne.symm ha, Ne.symm hb]) (hz _), mul_zero]
  · rfl

omit [DecidableEq ι] in
/-- A matrix over `ι × ι` vanishing off the rows and columns of a fixed second coordinate `z`
has rank at most `2 * card ι`. -/
private theorem rank_le_two_mul_card_of_eq_zero (H : Matrix (ι × ι) (ι × ι) K) (z : ι)
    (hH : ∀ a b : ι × ι, a.2 ≠ z → b.2 ≠ z → H a b = 0) :
    H.rank ≤ 2 * Fintype.card ι := by
  classical
  set E : Matrix (ι × ι) ι K := Matrix.of fun a k => if a = (k, z) then 1 else 0 with hE
  set D' : Matrix (ι × ι) (ι × ι) K := Matrix.diagonal fun a => if a.2 = z then 0 else 1
    with hD'
  have hD : E * E.transpose = Matrix.diagonal fun a => if a.2 = z then 1 else 0 := by
    ext ⟨r, c⟩ ⟨r', c'⟩
    rw [Matrix.mul_apply]
    simp only [hE, transpose_apply, of_apply, diagonal_apply, Prod.mk.injEq]
    by_cases hc : c = z <;> by_cases hc' : c' = z <;>
      simp [hc, hc', Finset.sum_ite_eq, @eq_comm _ z]
  have hsplit : H = E * (E.transpose * H) + (D' * H * E) * E.transpose := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (D' * H), hD]
    ext a b
    simp only [hD']
    by_cases ha : a.2 = z <;> by_cases hb : b.2 = z <;> simp [ha, hb, hH a b]
  rw [hsplit, two_mul]
  refine (Matrix.rank_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  · exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans
      (Matrix.rank_le_card_width _))

/-- **The determinant's Hessian at a singular matrix** has rank at most `2 * m`
[Mignon and Ressayre][MignonRessayre2004]. -/
theorem rank_hessian_det_mvPolynomialX_le {x : ι × ι → K}
    (hx : eval x (mvPolynomialX ι ι K).det = 0) :
    (hessian x (mvPolynomialX ι ι K).det).rank ≤ 2 * Fintype.card ι := by
  set M : Matrix ι ι K := Matrix.of fun i j => x (i, j) with hM
  rw [eval_det_mvPolynomialX] at hx
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hx
  obtain ⟨z, hz⟩ : ∃ z, v z ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  set Q : Matrix ι ι K := (1 : Matrix ι ι K).updateCol z v with hQ
  have hQdet : Q.det = v z := by
    simpa [Matrix.one_apply] using Matrix.det_updateCol_sum (1 : Matrix ι ι K) z v
  set L' : ι × ι → MvPolynomial (ι × ι) K := fun p => ∑ k, X (p.1, k) * C (Q k p.2)
    with hL'def
  have hL' : ∀ p, (L' p).totalDegree ≤ 1 := fun p => by
    refine totalDegree_finsetSum_le fun k _ => (totalDegree_mul _ _).trans ?_
    simp
  have haeval : aeval L' (mvPolynomialX ι ι K).det = (mvPolynomialX ι ι K).det * C Q.det := by
    rw [AlgHom.map_det, RingHom.map_det (C : K →+* MvPolynomial (ι × ι) K) Q, ← det_mul]
    congr 1
    ext i j
    simp [L', Matrix.mul_apply]
  have hy : ∀ i, eval x (L' (i, z)) = 0 := fun i => by
    have := congrFun hv i
    simp only [L', map_sum, map_mul, eval_X, eval_C, hQ, updateCol_self]
    simpa [Matrix.mulVec, dotProduct, hM] using this
  have hQ0 : Q.det ≠ 0 := hQdet ▸ hz
  have key : (hessian x (aeval L' (mvPolynomialX ι ι K).det)).rank ≤ 2 * Fintype.card ι :=
    (rank_hessian_aeval_le x L' hL' _).trans
      (rank_le_two_mul_card_of_eq_zero _ z fun a b ha hb =>
        hessian_det_mvPolynomialX_eq_zero hy ha hb)
  rwa [haeval, hessian_mul_C,
    rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hQ0)] at key

/-- **Mignon–Ressayre upper bound**: the determinant of an `m × m` matrix of affine polynomials
has Hessian of rank at most `2 * m` at every zero of the determinant
[Mignon and Ressayre][MignonRessayre2004]. -/
theorem rank_hessian_det_le {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ (MvPolynomial σ K)) (hA : ∀ i j, (A i j).totalDegree ≤ 1) {x : σ → K}
    (hx : eval x A.det = 0) : (hessian x A.det).rank ≤ 2 * Fintype.card κ := by
  set L : κ × κ → MvPolynomial σ K := fun p => A p.1 p.2 with hL
  have hdet : A.det = aeval L (mvPolynomialX κ κ K).det := by
    rw [AlgHom.map_det, hL, mvPolynomialX_mapMatrix_aeval]
  rw [hdet, eval_aeval] at hx
  have h1 := MvPolynomial.rank_hessian_aeval_le x L (fun p => hA p.1 p.2)
    (mvPolynomialX κ κ K).det
  have h2 := rank_hessian_det_mvPolynomialX_le hx
  rw [hdet]
  exact h1.trans h2

end Matrix
