/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.MixedOperator

/-!
# Polynomials acting by differentiation and multiplication

With the variable `0` differentiating and the variable `1` multiplying, `X 0 * X 1` sends
`X 0 ^ 2` to `2 * (X 0 * X 1)`, a constant acts as a scalar, and the operator of a product is
the composition of the operators of its factors.
-/

public section

open MvPolynomial

namespace CslibFrontierTests.MixedOperator

abbrev s : Fin 2 → Prop := (· = 0)

example : mixedOp s (X 0 * X 1) (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) = 2 * (X 0 * X 1) := by
  rw [map_mul, Module.End.mul_apply, mixedOp_X_of_pos (by decide), mixedOp_X_of_neg (by decide)]
  simp
  ring

example (c : ℚ) (p : MvPolynomial (Fin 2) ℚ) : mixedOp s (C c) p = c • p := mixedOp_C s c p

/-- The operator of a product is the composition of the operators of its factors. -/
theorem mixedOp_mul_apply (P Q p : MvPolynomial (Fin 2) ℚ) :
    mixedOp s (P * Q) p = mixedOp s P (mixedOp s Q p) := by
  rw [map_mul, Module.End.mul_apply]

end CslibFrontierTests.MixedOperator
