/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Scalar bounds for fine-grained runtime transfers

These arithmetic estimates absorb additive linear changes of a natural parameter into a fixed
exponential factor, compare and absorb terms into exponential-times-polynomial envelopes
`2 ^ x * (L + 1) ^ e`, and bound the time of a polynomial-time reduction followed by a
computation. They are shared by decision, function-computation and randomized runtime transfers
without mentioning a machine or error model.

## Main results

* `Cslib.Complexity.two_rpow_le_two_rpow_mul_of_le_mul_add`,
  `Cslib.Complexity.two_rpow_le_natCeil_mul_of_le_mul_add`,
  `Cslib.Complexity.two_rpow_mul_pow_le_natCeil_mul_add`: rescale an exponential rate, alone or
  in an envelope, under an additive linear parameter bound.
* `Cslib.Complexity.two_rpow_mul_pow_le_natCeil_mul_add_of_le`: replace the exponential factor of
  an envelope by one that dominates it up to a constant factor.
* `Cslib.Complexity.natCast_mul_div_add_one_le`: the rate rescaling `c * (δ / (c + 1)) ≤ δ` behind
  subexponential transfers.
* `Cslib.Complexity.one_le_two_rpow_mul_pow`,
  `Cslib.Complexity.two_rpow_mul_pow_le_two_rpow_mul_pow`,
  `Cslib.Complexity.pow_le_two_rpow_mul_pow`: envelopes are at least `1`, monotone in the exponent
  and degree, and dominate polynomials of lower degree.
* `Cslib.Complexity.le_two_mul_mul_of_le_mul_add`: absorb an additive constant into an envelope.
* `Cslib.Complexity.reduction_add_time_le`: combine reduction and target runtimes while
  retaining the target's exponential envelope and the polynomial input-length factor.
-/

public section

namespace Cslib.Complexity

/-- An additive linear bound on a natural parameter splits its exponential at rate `δ ≥ 0` into a
constant factor and an exponential at rate `c * δ`. -/
theorem two_rpow_le_two_rpow_mul_of_le_mul_add {δ : ℝ} {n m c : ℕ}
    (hδ : 0 ≤ δ) (hn : n ≤ c * m + c) :
    (2 : ℝ) ^ (δ * n) ≤ 2 ^ (δ * c) * 2 ^ (c * δ * m) := by
  rw [← Real.rpow_add (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (n : ℝ) ≤ c * m + c := by exact_mod_cast hn
  nlinarith

/-- An additive linear bound on a natural parameter rescales its exponential rate, with the
additive part absorbed by a natural ceiling constant. -/
theorem two_rpow_le_natCeil_mul_of_le_mul_add {δ : ℝ} {n m c : ℕ}
    (hδ : 0 ≤ δ) (hn : n ≤ c * m + c) :
    (2 : ℝ) ^ (δ * n) ≤ (⌈(2 : ℝ) ^ (δ * c)⌉₊ : ℝ) * 2 ^ (c * δ * m) :=
  (two_rpow_le_two_rpow_mul_of_le_mul_add hδ hn).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Real.rpow_nonneg (by norm_num) _))

/-- Rescaling a rate `δ ≥ 0` by `1 / (c + 1)` leaves room for a factor `c`: the step that
transfers a bound for every rate `δ > 0` along a parameter change by the factor `c`. -/
theorem natCast_mul_div_add_one_le {δ : ℝ} (hδ : 0 ≤ δ) (c : ℕ) : c * (δ / (c + 1)) ≤ δ := by
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Exponential-times-polynomial envelopes

Exponential runtime bounds have the form `2 ^ x * (L + 1) ^ e` for an exponent `x ≥ 0` and the
length `L` of the encoded input. The envelope is at least `1`, grows in `x` and `e`, and absorbs
polynomials of lower degree and additive constants. -/

section Envelope

variable {x y : ℝ} {L d e : ℕ}

/-- An exponential-times-polynomial envelope with nonnegative exponent is at least `1`. -/
theorem one_le_two_rpow_mul_pow (hx : 0 ≤ x) : 1 ≤ (2 : ℝ) ^ x * ((L : ℝ) + 1) ^ e :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) hx)
    (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg L)))

/-- An exponential-times-polynomial envelope grows with its exponent and its degree. -/
theorem two_rpow_mul_pow_le_two_rpow_mul_pow (hxy : x ≤ y) (hde : d ≤ e) :
    (2 : ℝ) ^ x * ((L : ℝ) + 1) ^ d ≤ 2 ^ y * ((L : ℝ) + 1) ^ e :=
  mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hxy)
    (pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg L)) hde) (by positivity)
    (by positivity)

/-- A polynomial of degree `d ≤ e` is below the envelope `2 ^ x * (L + 1) ^ e`, `x ≥ 0`. -/
theorem pow_le_two_rpow_mul_pow (hx : 0 ≤ x) (hde : d ≤ e) :
    ((L : ℝ) + 1) ^ d ≤ 2 ^ x * ((L : ℝ) + 1) ^ e :=
  (pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg L)) hde).trans
    (le_mul_of_one_le_left (by positivity) (Real.one_le_rpow (by norm_num) hx))

/-- An exponential factor bounded by `K` times another one passes to the envelopes, with `K`
rounded up to a natural constant: the bound that `TimeO.mono` needs to replace one exponential
rate by another. -/
theorem two_rpow_mul_pow_le_natCeil_mul_add_of_le {K : ℝ} (h : (2 : ℝ) ^ x ≤ K * 2 ^ y) :
    (2 : ℝ) ^ x * ((L : ℝ) + 1) ^ e ≤ ⌈K⌉₊ * (2 ^ y * ((L : ℝ) + 1) ^ e) + ⌈K⌉₊ := by
  rw [← mul_assoc]
  exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right
    (h.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) (by positivity))) (by positivity))
    (Nat.cast_nonneg _)

/-- An additive linear bound on a natural parameter rescales an exponential-times-polynomial
envelope at rate `δ ≥ 0` to one at rate `c * δ`, up to a natural ceiling constant: the bound that
`TimeO.mono` needs to transfer an exponential runtime along the parameter change. -/
theorem two_rpow_mul_pow_le_natCeil_mul_add {δ : ℝ} {n m c : ℕ} (hδ : 0 ≤ δ)
    (hn : n ≤ c * m + c) :
    (2 : ℝ) ^ (δ * n) * ((L : ℝ) + 1) ^ e ≤
      ⌈(2 : ℝ) ^ (δ * c)⌉₊ * (2 ^ (c * δ * m) * ((L : ℝ) + 1) ^ e) + ⌈(2 : ℝ) ^ (δ * c)⌉₊ :=
  two_rpow_mul_pow_le_natCeil_mul_add_of_le (two_rpow_le_two_rpow_mul_of_le_mul_add hδ hn)

end Envelope

/-- A runtime `t ≤ c * Y + c` with `Y ≤ X` and `1 ≤ X` is at most `2 * c * X`: an additive
constant is absorbed into an envelope that is at least `1`. -/
theorem le_two_mul_mul_of_le_mul_add {t X Y : ℝ} {c : ℕ} (ht : t ≤ c * Y + c) (hY : Y ≤ X)
    (hX : 1 ≤ X) : t ≤ 2 * c * X := by
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith

/-- **Running a computation on a reduced instance.** If the reduction runs within time `P ≥ 1`
and its output has length `n ≤ l * (P + 1)`, a subsequent computation with time
`T ≤ k * (Y * (n + 1) ^ e) + k`, where `Y ≤ C * X`, `C ≥ 0` and `X ≥ 1`, has total time
bounded by a constant times `X * P ^ (e + 1)`. -/
theorem reduction_add_time_le {P X Y C T : ℝ} {n l k e : ℕ} (hP : 1 ≤ P) (hX : 1 ≤ X)
    (hC : 0 ≤ C) (hn : (n : ℝ) ≤ l * (P + 1)) (hY : Y ≤ C * X)
    (hT : T ≤ k * (Y * (n + 1) ^ e) + k) :
    P + T ≤ (1 + k * C * (2 * l + 1) ^ e + k) * (X * P ^ (e + 1)) := by
  -- Bound the polynomial in the reduced input length by a power of `P`.
  have hpow : ((n : ℝ) + 1) ^ e ≤ (2 * l + 1) ^ e * P ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) e
  have hT' := mul_le_mul_of_nonneg_left (mul_le_mul hY hpow (by positivity) (by positivity))
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  -- Absorb the reduction time and additive constants into `X * P ^ (e + 1)`.
  have h₁ : P ≤ X * P ^ (e + 1) :=
    (le_self_pow₀ hP (Nat.succ_ne_zero e)).trans (le_mul_of_one_le_left (by positivity) hX)
  have h₂ : X * P ^ e ≤ X * P ^ (e + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (Nat.le_add_right e 1)) (by positivity)
  have h₂' := mul_le_mul_of_nonneg_left h₂
    (by positivity : (0 : ℝ) ≤ k * C * (2 * l + 1) ^ e)
  have h₃ : (k : ℝ) * 1 ≤ k * (X * P ^ (e + 1)) := mul_le_mul_of_nonneg_left
    (one_le_mul_of_one_le_of_one_le hX (one_le_pow₀ hP)) (Nat.cast_nonneg k)
  linarith

end Cslib.Complexity
