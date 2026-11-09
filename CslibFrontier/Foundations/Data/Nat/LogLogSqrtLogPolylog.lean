/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.LogLogSqrtLog
public import Cslib.Foundations.Data.Nat.PolynomialBound

/-!
# Absorbing fixed polylogarithmic exponents into the single-loglog scale

Every fixed polynomial in the ceiling logarithm is eventually below the rounded scale.
A fixed additive constant handles all exceptional sizes, including zero. These comparisons
support actual initial-search and candidate-enumeration costs; no squared-loglog scale occurs.
-/

public section

open Filter

namespace Nat

/-- Every fixed multiple of a shifted ceiling-logarithm power is eventually absorbed. -/
theorem eventually_mul_clog_add_one_pow_le_logLogSqrtLogScale (C d : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * (clog 2 n + 1) ^ d ≤ logLogSqrtLogScale n := by
  have he := (tendsto_log_atTop one_lt_two).eventually
    (eventually_mul_add_one_pow_le_pow (C ^ 2 * 2 ^ (d * 2)) (d * 2) one_lt_two)
  filter_upwards [he, eventually_sqrt_mul_clog_le_logLogSqrtLogScale 1,
    eventually_ge_atTop 1] with n hn heta hn1
  have hc : clog 2 n + 1 ≤ 2 * (log 2 n + 1) := by
    have := (clog_le_iff_le_pow one_lt_two).mpr (lt_pow_succ_log_self one_lt_two n).le
    omega
  have hsquare : (C * (clog 2 n + 1) ^ d) ^ 2 ≤ n := by
    calc
      _ ≤ (C * (2 * (log 2 n + 1)) ^ d) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hc d)) 2
      _ = C ^ 2 * 2 ^ (d * 2) * (log 2 n + 1) ^ (d * 2) := by
        simp only [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ 2 ^ log 2 n := hn
      _ ≤ n := pow_log_le_self 2 (by omega)
  exact (le_sqrt.mpr (by simpa only [pow_two] using hsquare)).trans
    ((Nat.le_mul_of_pos_right (sqrt n) (by omega : 0 < 1 + clog 2 n)).trans heta)

/-- Every fixed polynomial in the ceiling logarithm is eventually absorbed. -/
theorem eventually_polynomial_clog_le_logLogSqrtLogScale {q : ℕ → ℕ}
    (hq : Cslib.PolynomiallyBounded q) :
    ∀ᶠ n : ℕ in atTop, q (clog 2 n) ≤ logLogSqrtLogScale n := by
  obtain ⟨C, d, h⟩ := Cslib.polynomiallyBounded_iff_le.mp hq
  exact (eventually_mul_clog_add_one_pow_le_logLogSqrtLogScale C d).mono
    (fun n hn => (h _).trans hn)

/-- A fixed additive exponent handles every exceptional input size. -/
theorem exists_polynomial_clog_le_logLogSqrtLogScale_add {q : ℕ → ℕ}
    (hq : Cslib.PolynomiallyBounded q) :
    ∃ A : ℕ, ∀ n, q (clog 2 n) ≤ logLogSqrtLogScale n + A := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_polynomial_clog_le_logLogSqrtLogScale hq)
  let A := ∑ i ∈ Finset.range N, q (clog 2 i)
  refine ⟨A, fun n => ?_⟩
  by_cases hn : n < N
  · exact (Finset.single_le_sum (fun i _ => Nat.zero_le (q (clog 2 i)))
      (Finset.mem_range.mpr hn)).trans (Nat.le_add_left A _)
  · exact (hN n (by omega)).trans (Nat.le_add_right _ _)

end Nat
