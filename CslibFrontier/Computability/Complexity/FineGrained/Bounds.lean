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
exponential factor and bound the time of a polynomial-time reduction followed by a computation.
They are shared by decision, function-computation and randomized runtime transfers without
mentioning a machine or error model.

## Main results

* `Cslib.Complexity.two_rpow_le_natCeil_mul_of_le_mul_add`: rescale an exponential rate under an
  additive linear parameter bound.
* `Cslib.Complexity.reduction_add_time_le`: combine reduction and target runtimes while
  retaining the target's exponential envelope and the polynomial input-length factor.
-/

public section

namespace Cslib.Complexity

/-- An additive linear bound on a natural parameter rescales its exponential rate, with the
additive part absorbed by a natural ceiling constant. -/
theorem two_rpow_le_natCeil_mul_of_le_mul_add {δ : ℝ} {n m c : ℕ}
    (hδ : 0 ≤ δ) (hn : n ≤ c * m + c) :
    (2 : ℝ) ^ (δ * n) ≤ (⌈(2 : ℝ) ^ (δ * c)⌉₊ : ℝ) * 2 ^ (c * δ * m) := by
  have hexp : (2 : ℝ) ^ (δ * n) ≤ 2 ^ (δ * c) * 2 ^ (c * δ * m) := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (n : ℝ) ≤ c * m + c := by exact_mod_cast hn
    nlinarith
  exact hexp.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Real.rpow_nonneg (by norm_num) _))

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
