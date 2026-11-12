/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.LowDegreeRoot

/-!
# The structure of a low-degree root: concrete checks

The polynomial `x₀ x₁` is the root of `y - x₀ x₁` and a double root of `(y - x₀ x₁)²`. In both
cases the structure theorem applies, in the second after one derivative in `y`. The universal
root exists for the constants `(0, 1)`.
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

/-- The root `x₀ x₁` of `y - x₀ x₁` has the form of the structure theorem. -/
example : ∃ (j : ℕ) (x₀ : Fin 2 → ℚ) (A : MvPolynomial (Fin 3) ℚ), A.totalDegree ≤ 2 ∧
    shift x₀ root = C (eval x₀ root) + truncateTotalDegree 2
      (aeval (fun i : Fin 3 =>
        (Polynomial.taylor (C (eval x₀ root))
          ((Polynomial.derivative^[j] eqn).map (shift x₀ : _ →ₐ[ℚ] _).toRingHom)).coeff i -
        C (constantCoeff ((Polynomial.taylor (C (eval x₀ root))
          ((Polynomial.derivative^[j] eqn).map (shift x₀ : _ →ₐ[ℚ] _).toRingHom)).coeff i))) A) :=
  exists_shift_eq_truncate_aeval_of_root eqn_ne_zero totalDegree_root eval_eqn

/-- The double root `x₀ x₁` of `(y - x₀ x₁)²` is a root of the first derivative whose second
derivative does not vanish. -/
example : ∃ j : ℕ, (Polynomial.derivative^[j] (eqn ^ 2)).eval root = 0 ∧
    (Polynomial.derivative^[j + 1] (eqn ^ 2)).eval root ≠ 0 :=
  exists_iterate_derivative_eval_ne_zero (pow_ne_zero 2 eqn_ne_zero)
    (by rw [Polynomial.eval_pow, eval_eqn, zero_pow two_ne_zero])

/-- The universal root for the constants `(0, 1)`. -/
example : ∃ A : MvPolynomial (Fin 2) ℚ, A ∈ idealOfVars (Fin 2) ℚ ∧ A.totalDegree ≤ 1 ∧
    ∑ i, (C ((![0, 1] : Fin 2 → ℚ) i) + X i) * A ^ (i : ℕ) ∈ idealOfVars (Fin 2) ℚ ^ 2 :=
  exists_universalRoot (d := 0) ![0, 1] rfl one_ne_zero

end CslibFrontierTests.LowDegreeRoot
