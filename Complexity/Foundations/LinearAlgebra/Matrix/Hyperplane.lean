/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A nonsingularity criterion from a positive hyperplane

A symmetric real matrix that is strictly positive on the orthogonal complement of a vector,
and strictly negative on that vector, has trivial kernel. The proof uses quadratic forms directly:
projecting a kernel vector onto the hyperplane would give a nonpositive quadratic form there.
No ordering of eigenvalues or perturbation theorem is required.

## Main results

* `Matrix.eq_zero_of_mulVec_eq_zero_of_pos_on_orthogonal`: the kernel criterion.
* `Matrix.mulVec_injective_of_pos_on_orthogonal`: its injectivity form.
-/

public section

namespace Matrix

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A symmetric real matrix with a negative direction and positive quadratic form on its
orthogonal hyperplane has no nonzero kernel vector. -/
theorem eq_zero_of_mulVec_eq_zero_of_pos_on_orthogonal
    {A : Matrix ι ι ℝ} (hA : A.IsSymm) {e : ι → ℝ}
    (hpos : ∀ x : ι → ℝ, e ⬝ᵥ x = 0 → x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x)
    (hneg : e ⬝ᵥ A *ᵥ e < 0) {x : ι → ℝ} (hx : A *ᵥ x = 0) : x = 0 := by
  have hxe : x ⬝ᵥ A *ᵥ e = 0 := by
    rw [hA.dotProduct_mulVec_comm, hx, dotProduct_zero]
  let a : ℝ := e ⬝ᵥ x
  let b : ℝ := e ⬝ᵥ e
  let y : ι → ℝ := b • x - a • e
  have hyorth : e ⬝ᵥ y = 0 := by
    simp only [y, dotProduct_sub, dotProduct_smul, smul_eq_mul, a, b]
    ring
  have hyform : y ⬝ᵥ A *ᵥ y = a ^ 2 * (e ⬝ᵥ A *ᵥ e) := by
    simp only [y, mulVec_sub, mulVec_smul, hx, smul_zero, zero_sub,
      sub_dotProduct, smul_dotProduct, dotProduct_neg, dotProduct_smul, smul_eq_mul, hxe]
    ring
  have hy_nonneg : 0 ≤ y ⬝ᵥ A *ᵥ y := by
    by_cases hy : y = 0
    · simp [hy]
    · exact (hpos y hyorth hy).le
  have ha : a = 0 := by
    rw [hyform] at hy_nonneg
    by_contra ha
    exact (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ha) hneg).not_ge hy_nonneg
  by_contra hx0
  have := hpos x ha hx0
  simp [hx] at this

/-- The linear operator of a symmetric real matrix is injective when its quadratic form is
positive on the orthogonal hyperplane of a negative direction. -/
theorem mulVec_injective_of_pos_on_orthogonal
    {A : Matrix ι ι ℝ} (hA : A.IsSymm) {e : ι → ℝ}
    (hpos : ∀ x : ι → ℝ, e ⬝ᵥ x = 0 → x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x)
    (hneg : e ⬝ᵥ A *ᵥ e < 0) : Function.Injective A.mulVec := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_mulVec_eq_zero_of_pos_on_orthogonal hA hpos hneg
  rw [mulVec_sub, hxy, sub_self]

end Matrix
