/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.LogLogSqrtLog
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Compare rounded counting exponents with the real source scale

All logarithms in the real scale have base two. The comparison keeps one iterated logarithm,
charges every floor/ceiling by an explicit constant, and includes fixed linear enlargement of
an input parameter. It is a numerical estimate, not a counting-algorithm premise.

## Main definitions

* `Real.logLogSqrtLogScale`: the unshifted base-two real source scale.

## Main results

* `Nat.cast_logLogSqrtLogScale_le`: explicit rounding comparison for n≥16.
* `Nat.cast_logLogSqrtLogScale_le_of_le_mul`: linear query-variable rescaling.
-/

public section

namespace Real

/-- The base-two source counting exponent `x loglog x / sqrt(log x)`. -/
@[expose] noncomputable def logLogSqrtLogScale (x : ℝ) : ℝ :=
  x * logb 2 (logb 2 x) / sqrt (logb 2 x)

end Real

namespace Nat

/-- The rounded exponent is at most six times the real base-two source scale on n≥16. -/
theorem cast_logLogSqrtLogScale_le {n : ℕ} (hn : 16 ≤ n) :
    (logLogSqrtLogScale n : ℝ) ≤ 6 * Real.logLogSqrtLogScale n := by
  let L := Real.logb 2 (n : ℝ)
  let H := Real.logb 2 L
  let r := sqrt (log 2 n)
  have hn4 : 4 ≤ log 2 n := le_log_of_pow_le one_lt_two hn
  have hL : 4 ≤ L := (show (4 : ℝ) ≤ log 2 n by exact_mod_cast hn4).trans
    (Real.natLog_le_logb n 2)
  have hH : 1 ≤ H := by
    have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ L by linarith)
    rw [Real.logb_self_eq_one (by norm_num)] at h
    exact h
  have hc (m : ℕ) : (clog 2 m : ℝ) ≤ Real.logb 2 m + 1 := by
    have hnat : clog 2 m ≤ log 2 m + 1 :=
      (clog_le_iff_le_pow one_lt_two).mpr (lt_pow_succ_log_self one_lt_two m).le
    have hcast : (clog 2 m : ℝ) ≤ (log 2 m : ℝ) + 1 := by exact_mod_cast hnat
    have hl := Real.natLog_le_logb m 2
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have hlam : (clog 2 n : ℝ) ≤ 2 * L := by linarith [hc n]
  have hlampos : (0 : ℝ) < clog 2 n := by
    exact_mod_cast (log_le_clog 2 n).trans_lt'
      (show 0 < log 2 n by omega)
  have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hlampos hlam
  rw [Real.logb_mul (by norm_num) (by linarith : L ≠ 0),
    Real.logb_self_eq_one (by norm_num)] at hlog
  have hν : (clog 2 (clog 2 n) : ℝ) ≤ 3 * H := by
    have hh := hc (clog 2 n)
    dsimp only [H] at *
    linarith
  have hr : 1 ≤ r := one_le_sqrt_log_two (by omega)
  have hfloor : L < (log 2 n : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (Real.logb (2 : ℕ) (n : ℝ))
    rw [Real.natFloor_logb_natCast] at h
    simpa only [Nat.cast_ofNat] using h
  have hq : (log 2 n : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 2 := by
    have h := lt_succ_sqrt (log 2 n)
    have h' : log 2 n + 1 ≤ (r + 1) ^ 2 := by nlinarith
    exact_mod_cast h'
  have hsqrt : Real.sqrt L ≤ 2 * (r : ℝ) := by
    have hs := Real.sqrt_le_iff.mpr ⟨by positivity, hfloor.le.trans hq⟩
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hdiv : (logLogSqrtLogScale n : ℝ) * r ≤
      (n : ℝ) * (clog 2 (clog 2 n) : ℝ) := by
    exact_mod_cast div_mul_le_self (n * clog 2 (clog 2 n)) r
  have hprod : (logLogSqrtLogScale n : ℝ) * Real.sqrt L ≤ 6 * (n : ℝ) * H := by
    have he0 : (0 : ℝ) ≤ logLogSqrtLogScale n := by positivity
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsqrt he0, mul_le_mul_of_nonneg_left hν hn0]
  have hspos : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  change (logLogSqrtLogScale n : ℝ) ≤ 6 * ((n : ℝ) * H / Real.sqrt L)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hspos).mpr
  nlinarith

/-- Convert a proved integer exponential budget to the real source exponent. -/
theorem two_pow_mul_logLogSqrtLogScale_le (A : ℕ) {n : ℕ} (hn : 16 ≤ n) :
    (2 : ℝ) ^ (A * logLogSqrtLogScale n) ≤
      (2 : ℝ) ^ (((6 * A : ℕ) : ℝ) * Real.logLogSqrtLogScale n) := by
  have he := mul_le_mul_of_nonneg_left (cast_logLogSqrtLogScale_le hn)
    (show (0 : ℝ) ≤ A by positivity)
  have hexp : ((A * logLogSqrtLogScale n : ℕ) : ℝ) ≤
      ((6 * A : ℕ) : ℝ) * Real.logLogSqrtLogScale n := by
    push_cast at *
    nlinarith
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- Fixed linear query enlargement changes only the constant in the real source exponent.
The queried variable count m may be smaller than the source parameter. -/
theorem cast_logLogSqrtLogScale_le_of_le_mul (C : ℕ) {m n : ℕ}
    (hm : m ≤ C * n) (hn : max 16 C ≤ n) :
    (logLogSqrtLogScale m : ℝ) ≤ 120 * C * Real.logLogSqrtLogScale n := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · have hm0 : m = 0 := by omega
    simp [hm0, logLogSqrtLogScale]
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hCn : C ≤ n := (le_max_right _ _).trans hn
  have hbig : 4 ≤ C * n := (show 4 ≤ n by omega).trans (Nat.le_mul_of_pos_left n hC)
  have hd := (logLogSqrtLogScale_le_of_le hm hbig).trans
    (Nat.mul_le_mul_left 5 (logLogSqrtLogScale_mul_le C (by omega)))
  have hdR : (logLogSqrtLogScale m : ℝ) ≤ 20 * C * (logLogSqrtLogScale n : ℝ) := by
    have hdN : logLogSqrtLogScale m ≤ 20 * C * logLogSqrtLogScale n := by nlinarith
    exact_mod_cast hdN
  have hr := mul_le_mul_of_nonneg_left (cast_logLogSqrtLogScale_le hn16)
    (show (0 : ℝ) ≤ 20 * C by positivity)
  nlinarith

end Nat
