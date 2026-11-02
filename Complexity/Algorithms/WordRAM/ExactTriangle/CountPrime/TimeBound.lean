/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Flat
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Charged subcubic native modular-counter time

The actual initialized execution, including halt, is bounded by a quadratic polynomial in
the runtime cyclic length p times seven to the computed ceiling-logarithmic matrix depth.
The real-power consequence has n exponent 2.81, strictly below three. Dependence on p remains
explicit; this does not claim subcubic time after arbitrary growth of p with n, nor complete
prime selection or the full ExactTriangle/3SUM endpoint.

All constants bound the proved native execution. They do not inherit the Light machine's
ring-operation constants from the pinned source.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

/-- Every actual initialized setup, memory/coefficient operation, recursion, scan and halt
fits this native seven-to-depth budget. -/
theorem cost_le_seven_pow (n p : ℕ) :
    cost n p + 10 ≤ (42 * p * p + 254 * p + 463) * 7 ^ Nat.clog 2 n := by
  let k := Nat.clog 2 n
  have hn : n ≤ 2 ^ k := Nat.le_pow_clog (by decide) n
  have hn2 : n * n ≤ 4 ^ k := by
    calc
      _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul hn hn
      _ = 4 ^ k := by rw [← mul_pow]; rfl
  have h4 : 4 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by decide) _
  have h2 : 2 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by decide) _
  have hN := Nat.mul_le_mul_left 91 (hn2.trans h4)
  have hsub := Nat.mul_le_mul_left 11 ((Nat.sub_le (2 ^ k) 1).trans h2)
  have hk := Nat.mul_le_mul_left 13 (Nat.lt_pow_self (n := k) (by decide : 1 < 7)).le
  have hunit : 1 ≤ 7 ^ k := Nat.one_le_pow _ _ (by decide)
  have hc := Nat.mul_le_mul_left 122 hunit
  have hmat := Nat.mul_le_mul_left (14 * p + 48) h4
  have ht := Strassen.traceBudget_potential_le p k
  have htrace : Strassen.traceBudget p k ≤ (42 * p * p + 240 * p + 178) * 7 ^ k :=
    ((Nat.le_add_right (Strassen.traceBudget p k) (231 * p * 4 ^ k)).trans
      (Nat.le_add_right _ 150)).trans ht
  change Strassen.traceBudget p k + (14 * p + 48) * 4 ^ k + 11 * (2 ^ k - 1) +
    91 * (n * n) + 4 * k + 81 + 9 * k + 31 + 10 ≤ _
  nlinarith only [htrace, hmat, hN, hsub, hk, hc]

/-- A simple quadratic p envelope for the complete actual initialized instruction charge. -/
theorem cost_le_square (n p : ℕ) :
    cost n p + 10 ≤ 463 * (p + 1) ^ 2 * 7 ^ Nat.clog 2 n := by
  have hc : 42 * p * p + 254 * p + 463 ≤ 463 * (p + 1) ^ 2 := by nlinarith
  exact (cost_le_seven_pow n p).trans (Nat.mul_le_mul_right _ hc)

private theorem seven_le_two_rpow : (7 : ℝ) ≤ (2 : ℝ) ^ (281 / 100 : ℝ) := by
  have seed : (7 : ℕ) ^ 100 ≤ 2 ^ 281 := by decide +kernel
  have seedR : (7 : ℝ) ^ 100 ≤ (2 : ℝ) ^ 281 := by exact_mod_cast seed
  have power : ((2 : ℝ) ^ (281 / 100 : ℝ)) ^ 100 = (2 : ℝ) ^ 281 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have h : (7 : ℝ) ^ 100 ≤ ((2 : ℝ) ^ (281 / 100 : ℝ)) ^ 100 := by
    rw [power]
    exact seedR
  apply (Real.rpow_le_rpow_iff (by norm_num : 0 ≤ (7 : ℝ))
    (by positivity) (by norm_num : 0 < (100 : ℝ))).mp
  change (7 : ℝ) ^ ((100 : ℕ) : ℝ) ≤
    ((2 : ℝ) ^ (281 / 100 : ℝ)) ^ ((100 : ℕ) : ℝ)
  simpa only [Real.rpow_natCast] using h

private theorem seven_pow_clog_le (n : ℕ) :
    (7 : ℝ) ^ Nat.clog 2 n ≤ 8 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) := by
  let k := Nat.clog 2 n
  have pad : 2 ^ k ≤ 2 * (n + 1) :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (Nat.clog_mono_right 2 (by omega : n ≤ n + 1))).trans
        (Nat.pow_clog_le_mul (by decide) (by omega : n + 1 ≠ 0))
  have padR : (2 : ℝ) ^ k ≤ 2 * (n + 1 : ℝ) := by exact_mod_cast pad
  have h7 := pow_le_pow_left₀ (by norm_num : 0 ≤ (7 : ℝ)) seven_le_two_rpow k
  have reordered : ((2 : ℝ) ^ (281 / 100 : ℝ)) ^ k =
      ((2 : ℝ) ^ k) ^ (281 / 100 : ℝ) := by
    rw [← Real.rpow_mul_natCast (by norm_num),
      mul_comm (281 / 100 : ℝ) (k : ℝ), Real.rpow_natCast_mul (by norm_num)]
  have height : (2 : ℝ) ^ (281 / 100 : ℝ) ≤ 8 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ))
      (by norm_num : (281 / 100 : ℝ) ≤ 3)
    convert h using 1; norm_num
  calc
    (7 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ (281 / 100 : ℝ) := by simpa only [reordered] using h7
    _ ≤ (2 * (n + 1 : ℝ)) ^ (281 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) padR (by norm_num)
    _ = (2 : ℝ) ^ (281 / 100 : ℝ) * (n + 1 : ℝ) ^ (281 / 100 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 8 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_right height (by positivity)

/-- The actual initialized native counter has subcubic n exponent 2.81 and quadratic p
factor, with every ring coefficient operation charged. The bound includes the final halt. -/
theorem cost_le_subcubic (n p : ℕ) :
    ((cost n p + 10 : ℕ) : ℝ) ≤
      3704 * (p + 1 : ℝ) ^ 2 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) := by
  have hc : ((cost n p + 10 : ℕ) : ℝ) ≤
      463 * (p + 1 : ℝ) ^ 2 * (7 : ℝ) ^ Nat.clog 2 n := by
    exact_mod_cast cost_le_square n p
  calc
    _ ≤ 463 * (p + 1 : ℝ) ^ 2 * (7 : ℝ) ^ Nat.clog 2 n := hc
    _ ≤ 463 * (p + 1 : ℝ) ^ 2 * (8 * (n + 1 : ℝ) ^ (281 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_left (seven_pow_clog_le n) (by positivity)
    _ = _ := by ring

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
