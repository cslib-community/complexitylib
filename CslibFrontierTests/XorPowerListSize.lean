/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.XorPowerListSize
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Tests: the list size of the `k`-fold XOR code

The first coordinate and its complement on one bit have correlation `-2`, so their threefold XORs
have correlation `(-2) ^ 3 = -8`; their twofold XORs coincide, which is why the list-size bound
needs odd `k`. With `k = 3`, `ε = 1 / 2` and `δ₀ = 1 / 4`, so that `(1 - 2 δ₀) ^ 3 = 1 / 8 ≤ 1 / 2`,
at most two Boolean functions on two bits have a given threefold XOR, and in general the list has
at most `2 exp (2 ^ n H(1 / 4))` functions.
-/

namespace CslibFrontierTests.XorPowerListSize

open Cslib Cslib.BitString Cslib.Circuits.Boolean Finset

/-- The threefold XORs of the first coordinate and its complement have correlation `-8`. -/
example :
    ∑ x, signVal (xorPower (fun y : BitString 1 => y 0) 3 x) *
      signVal (xorPower (fun y : BitString 1 => !y 0) 3 x) = -8 := by
  rw [sum_signVal_xorPower_mul_signVal_xorPower]
  simp only [signVal_not, mul_neg, signVal_mul_self, sum_neg_distrib, sum_const, card_univ,
    BitString.card, nsmul_eq_mul, mul_one]
  norm_num

/-- For even `k` the XOR code is not injective: the first coordinate and its complement have the
same twofold XOR. -/
example : xorPower (fun y : BitString 1 => y 0) 2 = xorPower (fun y : BitString 1 => !y 0) 2 := by
  decide

/-- **The list size for `k = 3`, `ε = 1 / 2`, `δ₀ = 1 / 4`** on two bits: the radius is `0`, so
at most `1 / (2 ε ^ 2) = 2` Boolean functions have threefold XORs agreeing everywhere with `w`. -/
example (w : BitString (3 * 2) → Bool) :
    (#{g : BooleanFunction 2 |
      ((1 : ℝ) / 2 + 1 / 2) * 2 ^ (3 * 2) ≤ (#{x | xorPower g 3 x = w x} : ℝ)} : ℝ) *
      (2 * (1 / 2) ^ 2) ≤ ((∑ j ∈ range (0 + 1), (2 ^ 2).choose j : ℕ) : ℝ) :=
  card_filter_xorPower_mul_two_mul_sq_le (n := 2) (k := 3) (by decide) w (ε := 1 / 2)
    (δ₀ := 1 / 4) (r := 0) (by norm_num) (by norm_num) (by norm_num)

/-- **The entropy form** for `k = 3`, `ε = 1 / 2`, `δ₀ = 1 / 4`: on `n` bits, the list has at most
`2 exp (2 ^ n H(1 / 4))` functions. -/
example {n : ℕ} (w : BitString (3 * n) → Bool) :
    (#{g : BooleanFunction n |
      ((1 : ℝ) / 2 + 1 / 2) * 2 ^ (3 * n) ≤ (#{x | xorPower g 3 x = w x} : ℝ)} : ℝ) *
      (2 * (1 / 2) ^ 2) ≤ Real.exp (2 ^ n * Real.binEntropy (1 / 4)) :=
  card_filter_xorPower_mul_two_mul_sq_le_exp (n := n) (k := 3) (by decide) w (ε := 1 / 2)
    (δ₀ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CslibFrontierTests.XorPowerListSize
