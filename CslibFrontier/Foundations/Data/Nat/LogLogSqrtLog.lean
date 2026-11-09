/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.SqrtLog
public import CslibFrontier.Foundations.Data.Nat.Asymptotics

/-!
# Integer logarithmic scale for sharper counting

The scale is `n * clog₂(clog₂ n) / sqrt(log₂ n)`, with natural division and integer square root.
These are explicit rounding conventions; identifying this with a real source asymptotic requires
comparison estimates, rather than silently replacing the floor or ceiling functions.
The estimates below absorb the degree-array exponent `sqrt n * (C + clog₂ n)`.

## Main definitions

* `Nat.logLogSqrtLogScale`: the explicitly rounded single-iterated-log scale.

## Main results

* `Nat.eventually_sqrt_mul_clog_le_logLogSqrtLogScale`: array-exponent absorption.
* `Nat.logLogSqrtLogScale_le_of_le`: constant-factor comparison at smaller dimensions.
* `Nat.logLogSqrtLogScale_mul_le`: fixed linear enlargement.
-/

public section

open Filter

namespace Nat

/-- Discrete logarithmic counting scale, with a single iterated-logarithm factor. -/
@[expose] def logLogSqrtLogScale (n : ℕ) : ℕ :=
  n * clog 2 (clog 2 n) / sqrt (log 2 n)

/-- The iterated upper logarithm is positive from four on. -/
theorem one_le_clog_clog_two {n : ℕ} (hn : 4 ≤ n) : 1 ≤ clog 2 (clog 2 n) := by
  apply clog_pos one_lt_two
  have h : 2 ≤ clog 2 n :=
    (clog_pow 2 2 one_lt_two).symm.trans_le (clog_mono_right 2 hn)
  omega

/-- The scale includes the high-incidence branching exponent. -/
theorem div_sqrt_log_two_le_logLogSqrtLogScale {n : ℕ} (hn : 4 ≤ n) :
    n / sqrt (log 2 n) ≤ logLogSqrtLogScale n :=
  Nat.div_le_div_right (Nat.le_mul_of_pos_right n (one_le_clog_clog_two hn))

/-- The scale is positive on the source's large-input range. -/
theorem one_le_logLogSqrtLogScale {n : ℕ} (hn : 4 ≤ n) :
    1 ≤ logLogSqrtLogScale n :=
  (one_le_div_sqrt_log_two (by omega)).trans (div_sqrt_log_two_le_logLogSqrtLogScale hn)

private theorem eventually_clog_add_fourth_le (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, (C + clog 2 n) ^ 4 ≤ n := by
  have he := (tendsto_log_atTop one_lt_two).eventually
    (eventually_mul_add_one_pow_le_pow ((C + 1) ^ 4) 4 one_lt_two)
  filter_upwards [he, eventually_ge_atTop 1] with n hn hn1
  have hc : clog 2 n ≤ log 2 n + 1 :=
    (clog_le_iff_le_pow one_lt_two).mpr (lt_pow_succ_log_self one_lt_two n).le
  calc (C + clog 2 n) ^ 4 ≤ ((C + 1) * (log 2 n + 1)) ^ 4 :=
        Nat.pow_le_pow_left (by nlinarith) _
    _ = (C + 1) ^ 4 * (log 2 n + 1) ^ 4 := mul_pow _ _ _
    _ ≤ 2 ^ log 2 n := hn
    _ ≤ n := pow_log_le_self 2 (by omega)

/-- The complete square-root/logarithmic array exponent is eventually bounded by the counting
scale. The threshold depends on C; no varying-input bound is supplied as advice. -/
theorem eventually_sqrt_mul_clog_le_logLogSqrtLogScale (C : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      sqrt n * (C + clog 2 n) ≤ logLogSqrtLogScale n := by
  filter_upwards [eventually_clog_add_fourth_le C, eventually_ge_atTop 4] with n hn hn4
  have hr : 0 < sqrt (log 2 n) := one_le_sqrt_log_two (by omega)
  have hb : (C + clog 2 n) * (C + clog 2 n) ≤ sqrt n := by
    apply le_sqrt.mpr
    nlinarith
  have hl : sqrt (log 2 n) ≤ C + clog 2 n :=
    (sqrt_le_self _).trans ((log_le_clog 2 n).trans (Nat.le_add_left _ _))
  have hmul : sqrt n * (C + clog 2 n) * sqrt (log 2 n) ≤ n := by
    calc _ = sqrt n * ((C + clog 2 n) * sqrt (log 2 n)) := by ring
      _ ≤ sqrt n * ((C + clog 2 n) * (C + clog 2 n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hl)
      _ ≤ sqrt n * sqrt n := Nat.mul_le_mul_left _ hb
      _ ≤ n := sqrt_le n
  exact ((le_div_iff_mul_le hr).mpr hmul).trans
    (div_sqrt_log_two_le_logLogSqrtLogScale hn4)

/-- Increasing the padded size only increases the logarithmic divisor. -/
theorem mul_padded_div_sqrt_log_two_le (A : ℕ) {n : ℕ} (hn : 4 ≤ n) :
    A * (n * clog 2 (clog 2 n)) / sqrt (log 2 (n * clog 2 (clog 2 n))) ≤
      A * logLogSqrtLogScale n + A := by
  have hns : n ≤ n * clog 2 (clog 2 n) :=
    Nat.le_mul_of_pos_right n (one_le_clog_clog_two hn)
  calc _ ≤ A * (n * clog 2 (clog 2 n)) / sqrt (log 2 n) :=
        div_le_div_left (sqrt_log_two_mono hns) (one_le_sqrt_log_two (by omega))
    _ ≤ _ := mul_div_le_mul_div_add _ _ _

/-- Changing to a smaller variable count loses only a constant in the rounded scale. -/
theorem logLogSqrtLogScale_le_of_le {m n : ℕ} (hmn : m ≤ n) (hn : 4 ≤ n) :
    logLogSqrtLogScale m ≤ 5 * logLogSqrtLogScale n := by
  let ν := clog 2 (clog 2 n)
  have hν : clog 2 (clog 2 m) ≤ ν := clog_mono_right 2 (clog_mono_right 2 hmn)
  have hbase := div_sqrt_log_two_le_of_le hmn
  have hη : ν * (n / sqrt (log 2 n)) ≤ logLogSqrtLogScale n := by
    simpa only [logLogSqrtLogScale, mul_comm] using mul_div_le_mul_div_assoc ν n (sqrt (log 2 n))
  have hνle : ν ≤ logLogSqrtLogScale n :=
    (Nat.le_mul_of_pos_right ν (one_le_div_sqrt_log_two (by omega))).trans hη
  calc logLogSqrtLogScale m ≤
      clog 2 (clog 2 m) * (m / sqrt (log 2 m)) + clog 2 (clog 2 m) := by
        simpa only [logLogSqrtLogScale, mul_comm] using
          mul_div_le_mul_div_add (clog 2 (clog 2 m)) m (sqrt (log 2 m))
    _ ≤ ν * (2 * (n / sqrt (log 2 n)) + 2) + ν :=
        Nat.add_le_add (Nat.mul_le_mul hν hbase) hν
    _ ≤ _ := by nlinarith

/-- Fixed linear enlargement preserves the single-iterated-log scale. The explicit threshold
also makes this applicable to a query with at most C times the source variable count. -/
theorem logLogSqrtLogScale_mul_le (C : ℕ) {n : ℕ} (hn : max 4 C ≤ n) :
    logLogSqrtLogScale (C * n) ≤ 4 * C * logLogSqrtLogScale n := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · simp [logLogSqrtLogScale]
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hCn : C ≤ n := (le_max_right _ _).trans hn
  let lam := clog 2 n
  let ν := clog 2 lam
  have hν : 1 ≤ ν := one_le_clog_clog_two hn4
  have hlam : clog 2 (C * n) ≤ 2 * lam := by
    apply (clog_le_iff_le_pow one_lt_two).mpr
    calc C * n ≤ n * n := Nat.mul_le_mul_right _ hCn
      _ ≤ 2 ^ lam * 2 ^ lam := Nat.mul_le_mul (le_pow_clog one_lt_two _) (le_pow_clog one_lt_two _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hνC : clog 2 (clog 2 (C * n)) ≤ 2 * ν := by
    have hpow : 2 * lam ≤ 2 ^ (ν + 1) := by
      rw [pow_succ]
      simpa only [mul_comm] using Nat.mul_le_mul_left 2 (le_pow_clog one_lt_two lam)
    exact ((clog_le_iff_le_pow one_lt_two).mpr (hlam.trans hpow)).trans (by omega)
  have hr : 0 < sqrt (log 2 n) := one_le_sqrt_log_two (by omega)
  have hns : n ≤ C * n := Nat.le_mul_of_pos_left n hC
  have hη : 1 ≤ logLogSqrtLogScale n := one_le_logLogSqrtLogScale hn4
  calc logLogSqrtLogScale (C * n) ≤ (2 * C) * (n * ν) / sqrt (log 2 n) := by
        apply (div_le_div_left (sqrt_log_two_mono hns) hr).trans
        apply Nat.div_le_div_right
        nlinarith [Nat.mul_le_mul_left (C * n) hνC]
    _ ≤ (2 * C) * logLogSqrtLogScale n + 2 * C := mul_div_le_mul_div_add _ _ _
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_left (2 * C) hη]

end Nat
