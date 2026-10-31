/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.SqrtLog
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

/-!
# Rescaling square-root-logarithm lower bounds

A natural-number bound at lengths `d * n` transfers to the usual real-valued
`N * √(log₂ N)` scale. If `n ≥ max d 512`, then `√(log₂ (d * n))` is at most twice
`Nat.sqrt (Nat.log 2 n)`. Consequently, a strict lower bound
`n * Nat.sqrt (Nat.log 2 (n + 2)) / K < f (d * n)` implies the real lower bound
`(d * n) * √(log₂ (d * n)) / (2 * K * d) < f (d * n)`.

The strict inequality removes the rounding loss: for natural numbers, `a / K < v`
is equivalent to `a < v * K` when `K > 0`. The infinitely-often version keeps the
coefficient `1 / (2 * K * d)` explicit. In particular, the budget `K = 12 * (A + 1)`
gives the coefficient `1 / (24 * (A + 1) * d)`.

## Main results

* `Nat.sqrt_logb_mul_le_two_mul_sqrt_log_two`: an explicit comparison of real and natural
  square-root logarithms after a constant rescaling of the argument.
* `Nat.mul_sqrt_logb_div_lt_of_div_lt`: the pointwise transfer, including natural division.
* `Nat.frequently_mul_sqrt_logb_div_lt`: the transfer of an infinitely-often lower bound
  from the subsequence of lengths `d * n` to the full sequence.
-/

public section

namespace Nat

/-- For `n ≥ max d 512`, rescaling the argument by `d` and removing both floors costs
at most a factor of two in the square-root logarithm. -/
theorem sqrt_logb_mul_le_two_mul_sqrt_log_two {d n : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (hn : 512 ≤ n) :
    Real.sqrt (Real.logb 2 ((d * n : ℕ) : ℝ)) ≤ 2 * (sqrt (log 2 n) : ℝ) := by
  set L := log 2 n
  set q := sqrt L
  have hn0 : 0 < n := by omega
  have hq : 3 ≤ q := le_sqrt.2 (by
    have hpow : 2 ^ 9 ≤ n := by norm_num; omega
    simpa only [show 3 * 3 = 9 by rfl] using le_log_of_pow_le one_lt_two hpow)
  have hlogn : Real.logb 2 (n : ℝ) < (L : ℝ) + 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)]
    have hpow : (n : ℝ) < (2 : ℝ) ^ (L + 1) := by
      exact_mod_cast lt_pow_succ_log_self one_lt_two n
    rw [← Real.rpow_natCast] at hpow
    exact_mod_cast hpow
  have hL : (L : ℝ) + 1 ≤ ((q : ℝ) + 1) ^ 2 := by
    have h : L + 1 ≤ (q + 1) ^ 2 := by
      simpa only [pow_two] using Nat.succ_le_of_lt (lt_succ_sqrt L)
    exact_mod_cast h
  have hlogd : Real.logb 2 (d : ℝ) ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hd) (by exact_mod_cast hdn)
  have hlogdn : Real.logb 2 ((d * n : ℕ) : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) := by
    rw [Nat.cast_mul, Real.logb_mul (by exact_mod_cast hd.ne') (by exact_mod_cast hn0.ne')]
    linarith
  rw [Real.sqrt_le_left (by positivity)]
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  nlinarith [sq_nonneg ((q : ℝ) - 3)]

/-- A strict natural-number lower bound at a rescaled length implies a real
`N * √(log₂ N)` lower bound, with the coefficient `1 / (2 * K * d)`. -/
theorem mul_sqrt_logb_div_lt_of_div_lt {K d n v : ℕ}
    (hK : 0 < K) (hd : 0 < d) (hdn : d ≤ n) (hn : 512 ≤ n)
    (h : n * sqrt (log 2 (n + 2)) / K < v) :
    ((d * n : ℕ) : ℝ) * Real.sqrt (Real.logb 2 ((d * n : ℕ) : ℝ)) /
        (2 * (K : ℝ) * d) < v := by
  set q := sqrt (log 2 (n + 2))
  have hsqrt := sqrt_logb_mul_le_two_mul_sqrt_log_two hd hdn hn
  have hq : (sqrt (log 2 n) : ℝ) ≤ q := by
    exact_mod_cast sqrt_log_two_mono (show n ≤ n + 2 by omega)
  have hsqrt' : Real.sqrt (Real.logb 2 ((d * n : ℕ) : ℝ)) ≤ 2 * (q : ℝ) := by
    linarith
  have hnat : n * q < v * K := (div_lt_iff_lt_mul hK).1 h
  have hreal : (n : ℝ) * q < (v : ℝ) * K := by exact_mod_cast hnat
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_lt_iff₀ (by positivity)]
  have hscaled := mul_lt_mul_of_pos_left hreal (show (0 : ℝ) < 2 * d by positivity)
  have hle := mul_le_mul_of_nonneg_left hsqrt' (show (0 : ℝ) ≤ (d * n : ℕ) by positivity)
  push_cast at hle ⊢
  nlinarith

open Filter in
/-- Infinitely many strict natural-number lower bounds at lengths `d * n` yield
infinitely many real square-root-logarithm lower bounds with an explicit coefficient. -/
theorem frequently_mul_sqrt_logb_div_lt {f : ℕ → ℕ} {K d : ℕ}
    (hK : 0 < K) (hd : 0 < d)
    (h : ∃ᶠ n in atTop, n * sqrt (log 2 (n + 2)) / K < f (d * n)) :
    ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * Real.sqrt (Real.logb 2 N) / (2 * (K : ℝ) * d) < f N := by
  refine frequently_atTop.2 fun M => ?_
  obtain ⟨n, hn, hf⟩ := frequently_atTop.1 h (max M (max d 512))
  refine ⟨d * n, ?_, mul_sqrt_logb_div_lt_of_div_lt hK hd (by omega) (by omega) hf⟩
  have : n ≤ d * n := Nat.le_mul_of_pos_left n hd
  omega

end Nat
