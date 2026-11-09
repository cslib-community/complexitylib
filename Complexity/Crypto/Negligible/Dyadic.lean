/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Negligibility of dyadic bounds

A constant numerator over `2 ^ n` is negligible. An entropy surplus of twice the security parameter
gives geometric decay after taking a square root. Polynomially many output rows preserve
negligibility. The output and source bit counts need not themselves be polynomially bounded or
computable.

## Main results

* `negligible_const_div_two_pow`: a constant numerator over `2 ^ n` is negligible.
* `sqrt_pow_two_div_pow_two_le`: the pointwise geometric estimate.
* `negligible_mul_sqrt_pow_two_div_pow_two`: polynomial losses preserve the estimate, including
  when the entropy margin holds only eventually.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

/-- A constant numerator over `2 ^ n` is negligible. -/
theorem negligible_const_div_two_pow (c : ℕ) :
    Negligible (fun n => (c : ℝ≥0) / 2 ^ n) := by
  have h : (fun n => (c : ℝ≥0) / 2 ^ n) =
      fun n => (c : ℝ≥0) * (1 / 2 : ℝ≥0) ^ n := by
    funext n
    rw [div_eq_mul_inv, one_div, inv_pow]
  rw [h]
  exact (negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)).polynomiallyBounded_mul
    (.const c)

/-- Twice the security parameter in surplus bits bounds the square-root ratio by `2⁻ⁿ`. -/
theorem sqrt_pow_two_div_pow_two_le {outputBits sourceBits n : ℕ}
    (hmargin : outputBits + 2 * n ≤ sourceBits) :
    NNReal.sqrt ((2 : ℝ≥0) ^ outputBits / 2 ^ sourceBits) ≤ (1 / 2 : ℝ≥0) ^ n := by
  rw [NNReal.sqrt_le_iff_le_sq]
  calc
    _ ≤ (2 : ℝ≥0) ^ outputBits / 2 ^ (outputBits + 2 * n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) hmargin)
    _ = _ := by
      rw [pow_add, mul_comm 2 n, pow_mul]
      simp only [one_div, inv_pow]
      field_simp

open Filter in
/-- A polynomial number of square-root dyadic errors is negligible under an eventual entropy
surplus of twice the security parameter. -/
theorem negligible_mul_sqrt_pow_two_div_pow_two
    {count outputBits sourceBits : ℕ → ℕ} (hcount : PolynomiallyBounded count)
    (hmargin : ∀ᶠ n in atTop, outputBits n + 2 * n ≤ sourceBits n) :
    Negligible (fun n => (count n : ℝ≥0) *
      NNReal.sqrt ((2 : ℝ≥0) ^ outputBits n / 2 ^ sourceBits n)) := by
  apply negligible_of_eventually_le
    ((negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)).polynomiallyBounded_mul
      hcount)
  filter_upwards [hmargin] with n hn
  exact mul_le_mul' le_rfl (sqrt_pow_two_div_pow_two_le hn)

end Cslib.Crypto
