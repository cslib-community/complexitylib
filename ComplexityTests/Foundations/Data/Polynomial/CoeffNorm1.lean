/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.CoeffNorm1

/-!
# Tests for `Polynomial.coeffNorm1`

Smoke tests for the `ℓ₁` coefficient norm `Polynomial.coeffNorm1` on `ℤ[X]`.
-/

@[expose] public section

namespace Polynomial.CoeffNorm1Tests

example : coeffNorm1 0 = 0 ∧ coeffNorm1 1 = 1 ∧ coeffNorm1 (C (-5)) = 5 := by
  refine ⟨coeffNorm1_zero, coeffNorm1_one, ?_⟩
  rw [coeffNorm1_C]
  rfl

example (p q : ℤ[X]) :
    coeffNorm1 (p - q) ≤ coeffNorm1 p + coeffNorm1 q ∧
      coeffNorm1 (p * q) ≤ coeffNorm1 p * coeffNorm1 q ∧
      coeffNorm1 (p ^ 3) ≤ coeffNorm1 p ^ 3 ∧
      coeffNorm1 ((1 - X) ^ 3 * p) ≤ 8 * coeffNorm1 p ∧
      (coeffNorm1 (C (-3) * p) : ℤ) ≤ 3 * (coeffNorm1 p : ℤ) := by
  refine ⟨coeffNorm1_sub_le p q, coeffNorm1_mul_le p q, coeffNorm1_pow_le p 3,
    coeffNorm1_one_sub_X_pow_mul_le 3 p, ?_⟩
  simpa using natCast_coeffNorm1_C_mul_le (-3) p

end Polynomial.CoeffNorm1Tests
