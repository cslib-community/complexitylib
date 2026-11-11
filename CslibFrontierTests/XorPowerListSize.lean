/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.XorPowerListSize
import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests: the list size of the `k`-fold XOR code

The first coordinate and its complement on one bit have correlation `-2`, so their threefold XORs
have correlation `(-2) ^ 3 = -8`; their twofold XORs coincide, which is why the list-size bound
needs odd `k`. With `k = 3`, `ε = 1 / 2` and `δ₀ = 1 / 4`, so that `(1 - 2 δ₀) ^ 3 = 1 / 8 ≤ 1 / 2`,
at most two Boolean functions on two bits have a given threefold XOR, and in general the list has
at most `2 exp (2 ^ n H(1 / 4))` functions. In the regime of the partial MCSP reduction,
`ε = 1 / (2 Δ)`, `δ₀ = 1 / 4` and `k = 2 Δ + 1` give at most `2 Δ ^ 2 exp (2 ^ n H(1 / 4))`.
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

/-- **The list size in the regime of the partial MCSP reduction**: with `ε = 1 / (2 Δ)`,
`δ₀ = 1 / 4` and odd `k = 2 Δ + 1`, so that `(1 / 2) ^ (2 Δ + 1) ≤ 1 / (2 Δ ^ 2)`, at most
`2 Δ ^ 2 exp (2 ^ n H(1 / 4))` functions have `k`-fold XORs agreeing with `w` on a
`1 / 2 + 1 / (2 Δ)` fraction of the inputs. -/
example {n Δ : ℕ} (hΔ : 1 ≤ Δ) (w : BitString ((2 * Δ + 1) * n) → Bool) :
    (#{g : BooleanFunction n | (1 / 2 + 1 / (2 * (Δ : ℝ))) * 2 ^ ((2 * Δ + 1) * n) ≤
        #{x | xorPower g (2 * Δ + 1) x = w x}} : ℝ) ≤
      2 * (Δ : ℝ) ^ 2 * Real.exp (2 ^ n * Real.binEntropy (1 / 4)) := by
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hε : (0 : ℝ) ≤ 1 / (2 * Δ) := by positivity
  have e2 : 2 * (1 / (2 * (Δ : ℝ))) ^ 2 = 1 / (2 * Δ ^ 2) := by field_simp
  have h4 : (Δ : ℝ) ^ 2 ≤ 4 ^ Δ := by
    have : Δ ^ 2 ≤ 4 ^ Δ :=
      calc Δ ^ 2 ≤ (2 ^ Δ) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
        _ = 4 ^ Δ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact_mod_cast this
  have hk : (1 - 2 * (1 / 4 : ℝ)) ^ (2 * Δ + 1) ≤ 2 * (1 / (2 * (Δ : ℝ))) ^ 2 := by
    have e1 : (1 - 2 * (1 / 4 : ℝ)) ^ (2 * Δ + 1) = 1 / (2 * 4 ^ Δ) := by
      rw [show (1 - 2 * (1 / 4 : ℝ)) = 1 / 2 by norm_num, one_div_pow, pow_succ, pow_mul]
      norm_num [mul_comm]
    rw [e1, e2]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h := card_filter_xorPower_mul_two_mul_sq_le_exp (n := n) (k := 2 * Δ + 1)
    (odd_two_mul_add_one Δ) w hε (by norm_num) (by norm_num) hk
  rw [e2, mul_one_div, div_le_iff₀ (by positivity)] at h
  linarith

end CslibFrontierTests.XorPowerListSize
