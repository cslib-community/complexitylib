/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Basic/ENNReal/Inv.lean`)

public import CslibFrontier.Init
public import Mathlib.Basic.ENNReal.Inv

/-!
# Fractions in `ℝ≥0∞`

A probability computed by counting is a fraction `a / b` of natural numbers in `ℝ≥0∞`. Comparing
two such fractions reduces to comparing the cross products in `ℕ`, and the probability that `m`
independent trials all succeed is a power `(a / b) ^ m`, which distributes over the quotient.

Mathlib's `div_pow` needs a `DivisionCommMonoid`, which `ℝ≥0∞` is not (`0 * ⊤ = 0` breaks
`(a * b)⁻¹ = a⁻¹ * b⁻¹`), so the quotient form of the power is stated here directly.

## Main results

* `ENNReal.natCast_div_le_natCast_div_iff`: for `b, d ≠ 0`, `a / b ≤ c / d ↔ a * d ≤ c * b`.
* `ENNReal.div_pow`: `(a / b) ^ n = a ^ n / b ^ n` for all `a b : ℝ≥0∞`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- Two fractions of natural numbers with nonzero denominators compare in `ℝ≥0∞` as their cross
products compare in `ℕ`: `a / b ≤ c / d ↔ a * d ≤ c * b`. -/
theorem natCast_div_le_natCast_div_iff {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℝ≥0∞) / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hb)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd))
      (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast Iff.rfl

/-- A power of a quotient in `ℝ≥0∞` is the quotient of the powers, with no side conditions. -/
protected theorem div_pow (a b : ℝ≥0∞) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

end ENNReal
