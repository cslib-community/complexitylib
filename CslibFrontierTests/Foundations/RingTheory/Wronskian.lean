/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.PDerivConst
public import CslibFrontier.Foundations.RingTheory.Derivation.Wronskian
public import CslibFrontier.Foundations.RingTheory.PowerSeries.Constants
public import Mathlib.Algebra.Polynomial.Derivation

/-!
# Wronskians, constants of derivations and partial derivatives

For the ordinary derivative of rational polynomials, the Wronskian of `(1, X)` is `1`. The
derivative of the power series `X ^ 3` is divisible by `X ^ 2`. Differentiating `X 0 ^ 2` three
times gives zero.
-/

public section

namespace CslibFrontierTests.Wronskian

open Polynomial

/-- The Wronskian of `(1, X)` for the ordinary derivative is `1`. -/
theorem wronskian_one_X :
    (Polynomial.derivative' (R := ℚ)).wronskian ![1, X] = 1 := by
  simp [Derivation.wronskian, Derivation.wronskianMatrix, Matrix.det_fin_two]

/-- The derivative of `X ^ 3` is divisible by `X ^ 2`. -/
theorem X_sq_dvd_derivative_X_cube :
    (PowerSeries.X : PowerSeries ℚ) ^ 2 ∣
      (PowerSeries.derivative : Derivation ℚ (PowerSeries ℚ) (PowerSeries ℚ)) (PowerSeries.X ^ 3) :=
  PowerSeries.X_pow_dvd_derivative (B := 3) (dvd_refl _)

/-- Differentiating `X 0 ^ 2` three times gives zero. -/
theorem iterate_pderiv_X_sq :
    (MvPolynomial.pderiv 0)^[3] (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) ℚ) = 0 :=
  MvPolynomial.iterate_pderiv_eq_zero 0
    (lt_of_le_of_lt (MvPolynomial.totalDegree_X_pow (0 : Fin 1) 2).le (by norm_num))

end CslibFrontierTests.Wronskian
