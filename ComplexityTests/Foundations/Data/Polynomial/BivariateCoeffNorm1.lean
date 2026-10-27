/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.BivariateCoeffNorm1

/-!
# Tests for `Complexity.Foundations.Data.Polynomial.BivariateCoeffNorm1`
-/

namespace ComplexityTests.BivariateCoeffNorm1

open Polynomial

/-- Concrete check of `bivariateCoeffNorm1_zero`, `bivariateCoeffNorm1_one`, and
`bivariateCoeffNorm1_C`. -/
example :
    (0 : Polynomial (Polynomial ℤ)).bivariateCoeffNorm1 = 0 ∧
      (1 : Polynomial (Polynomial ℤ)).bivariateCoeffNorm1 = 1 ∧
      (C (C (-3 : ℤ))).bivariateCoeffNorm1 = 3 := by
  refine ⟨bivariateCoeffNorm1_zero, bivariateCoeffNorm1_one, ?_⟩
  rw [bivariateCoeffNorm1_C, coeffNorm1_C]
  rfl

/-- Concrete check of `coeffNorm1_coeff_le_bivariateCoeffNorm1`, `bivariateCoeffNorm1_add_le`, and
`bivariateCoeffNorm1_mul_le`. -/
example (P Q : Polynomial (Polynomial ℤ)) (s : ℕ) :
    (P.coeff s).coeffNorm1 ≤ P.bivariateCoeffNorm1 ∧
      (P + Q).bivariateCoeffNorm1 ≤ P.bivariateCoeffNorm1 + Q.bivariateCoeffNorm1 ∧
      (P * Q).bivariateCoeffNorm1 ≤ P.bivariateCoeffNorm1 * Q.bivariateCoeffNorm1 :=
  ⟨coeffNorm1_coeff_le_bivariateCoeffNorm1 P s,
    bivariateCoeffNorm1_add_le P Q,
    bivariateCoeffNorm1_mul_le P Q⟩

end ComplexityTests.BivariateCoeffNorm1
