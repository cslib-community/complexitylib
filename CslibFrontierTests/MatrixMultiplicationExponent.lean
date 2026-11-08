/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.NineQuarters

/-! # The matrix multiplication exponent: checked instances

The trivial algorithm shows that `3` is an admissible exponent over `ℚ`, so the set of admissible
exponents is nonempty; every admissible exponent is at least `2`, so `omega ℚ` is a true infimum
with `2 ≤ omega ℚ ≤ 3`; and the headline gives `omega ℚ ≤ 9 / 4` and circuits of size
`O(n ^ (9/4 + 1/100))`. -/

namespace ComplexityTests.MatrixMultiplicationExponent

open Cslib.Circuits.Arithmetic.MatrixMultiplication

/-- The trivial algorithm: `3` is admissible. -/
example : AdmissibleExponent ℚ 3 :=
  admissibleExponent_three

/-- Admissible exponents are at least `2`. -/
example : 2 ≤ (3 : ℝ) :=
  two_le_of_admissibleExponent (K := ℚ) admissibleExponent_three

/-- `omega ℚ ≤ 3`. -/
example : omega ℚ ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

/-- `omega ℚ ≥ 2`: the infimum is over exponents at least `2`. -/
example : 2 ≤ omega ℚ :=
  le_csInf ⟨3, admissibleExponent_three⟩ fun _ hτ => two_le_of_admissibleExponent hτ

/-- Block recursion on the trivial algorithm for `2 × 2` matrices (`8 ≤ 2 ^ 3`) recovers the
exponent `3`. -/
example : AdmissibleExponent ℚ 3 :=
  admissibleExponent_of_rank (by norm_num) (Cslib.Tensor.rank_mm 2 2 2)
    (by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num) (by norm_num)

/-- **`ω ≤ 9/4` over `ℚ`.** -/
example : omega ℚ ≤ 9 / 4 :=
  omega_le_nine_quarters ℚ

/-- Circuits of size `O(n ^ (9/4 + 1/100))` for every `n`. -/
example : AdmissibleExponent ℚ (9 / 4 + 1 / 100) :=
  admissibleExponent_nine_quarters ℚ (by norm_num)

/-- The same over any field of characteristic zero, for instance `ℝ`. -/
example : omega ℝ ≤ 9 / 4 :=
  omega_le_nine_quarters ℝ

end ComplexityTests.MatrixMultiplicationExponent
