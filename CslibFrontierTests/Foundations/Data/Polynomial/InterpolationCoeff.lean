/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Polynomial.InterpolationCoeff

/-!
# Coefficients of a polynomial from its values

A polynomial of degree at most two over the `ℚ`-algebra `ℚ[X]` has its coefficients determined
by its values at `0`, `1` and `2`.
-/

public section

namespace CslibFrontierTests.InterpolationCoeff

open Polynomial Finset

/-- The coefficient of degree one of a quadratic over `ℚ[X]` from its values at `0`, `1`, `2`. -/
theorem coeff_one_of_natDegree_le_two {q : ℚ[X][X]} (hq : q.natDegree ≤ 2) :
    q.coeff 1 = ∑ j ∈ range 3,
      (Lagrange.basis (range 3) (fun j : ℕ => (j : ℚ)) j).coeff 1 •
        q.eval (algebraMap ℚ ℚ[X] j) :=
  Lagrange.coeff_eq_sum_coeff_basis_smul_eval Nat.cast_injective.injOn
    (by simpa using Nat.lt_succ_of_le hq) 1

end CslibFrontierTests.InterpolationCoeff
