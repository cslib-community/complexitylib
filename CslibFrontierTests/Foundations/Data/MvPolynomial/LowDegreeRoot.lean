/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.LowDegreeRoot

/-!
# The low-degree part of a root: concrete checks

The polynomial `x₀ x₁` is the root of `y - x₀ x₁` and a double root of `(y - x₀ x₁)²`. In both
cases the formula for roots applies, in the second after one derivative in `y`.
-/

public section

namespace CslibFrontierTests.LowDegreeRoot

open MvPolynomial

/-- The root `x₀ x₁`. -/
noncomputable def root : MvPolynomial (Fin 2) ℚ := X 0 * X 1

/-- The equation `y - x₀ x₁ = 0`. -/
noncomputable def eqn : Polynomial (MvPolynomial (Fin 2) ℚ) :=
  Polynomial.X - Polynomial.C root

theorem eval_eqn : eqn.eval root = 0 := by
  simp [eqn]

theorem eqn_ne_zero : eqn ≠ 0 :=
  Polynomial.X_sub_C_ne_zero _

theorem totalDegree_root : root.totalDegree ≤ 1 + 1 :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_X, totalDegree_X])

theorem constantCoeff_root : constantCoeff root = 0 := by
  simp [root]

/-- The root `x₀ x₁` of `y - x₀ x₁` is given, to degree two, by Lagrange inversion: here
`y - P / a` is the constant polynomial `x₀ x₁`. -/
example : truncateTotalDegree 2 root = truncateTotalDegree 2 (∑ m ∈ Finset.range (2 * (2 + 1)),
    ((m : ℚ) + 1)⁻¹ • ((Polynomial.X -
      Polynomial.C (C (constantCoeff (eqn.coeff 1))⁻¹) * eqn) ^ (m + 1)).coeff m) :=
  truncateTotalDegree_root_eq constantCoeff_root eval_eqn (by simp [eqn]) 2

/-- Any root of a nonzero polynomial has the form of the general theorem. -/
example : ∃ (j : ℕ) (x₀ : Fin 2 → ℚ),
    constantCoeff ((Polynomial.taylor (C (eval x₀ root)) ((Polynomial.derivative^[j] eqn).map
      (shift x₀ : _ →ₐ[ℚ] _).toRingHom)).coeff 1) ≠ 0 :=
  let ⟨j, x₀, h, _⟩ := exists_shift_eq_truncate_sum_of_root eqn_ne_zero eval_eqn
  ⟨j, x₀, h⟩

/-- The double root `x₀ x₁` of `(y - x₀ x₁)²` is a root of the first derivative whose second
derivative does not vanish. -/
example : ∃ j : ℕ, (Polynomial.derivative^[j] (eqn ^ 2)).eval root = 0 ∧
    (Polynomial.derivative^[j + 1] (eqn ^ 2)).eval root ≠ 0 :=
  exists_iterate_derivative_eval_ne_zero (pow_ne_zero 2 eqn_ne_zero)
    (by rw [Polynomial.eval_pow, eval_eqn, zero_pow two_ne_zero])

end CslibFrontierTests.LowDegreeRoot
