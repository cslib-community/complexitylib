/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Fixed powers of shifted natural logarithms are subpolynomial

This bridge applies Mathlib's real logarithm little-o estimate to natural logarithms with
fixed base, input shift and additive constant. It is general mathematics intended for Mathlib.
The native 3SUM host uses it for packed-side, catalogue-count and preprocessing logarithms.

## Main results

* `Nat.eventually_mul_log_add_pow_le_rpow`: every fixed positive multiple of a fixed
  logarithmic power is eventually bounded by any positive real power of the original input.
* `Nat.exists_size_add_one_pow_le_mul_rpow`: a fixed power of the binary length is bounded by a
  constant times any positive real power of the shifted input, for every input.
-/

public section

open Filter

namespace Nat

/-- Fixed shifts and additive constants do not change the subpolynomial growth of a natural
logarithm. The threshold may depend on all fixed parameters, but not on the varying input. -/
theorem eventually_mul_log_add_pow_le_rpow {b : ℕ} (hb : 1 < b) (s c d : ℕ)
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      K * ((Nat.log b (n + s) : ℝ) + c) ^ d ≤ (n : ℝ) ^ ε := by
  let a : ℝ := 2 / Real.log b + c
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hcoeff : 0 < K * a ^ d := mul_pos hK (pow_pos ha _)
  have hsmall := (isLittleO_log_rpow_rpow_atTop (d : ℝ) hε).comp_tendsto
    tendsto_natCast_atTop_atTop
  filter_upwards [hsmall.bound (inv_pos.mpr hcoeff),
    eventually_ge_atTop (max 16 (s + 2))] with n he hn
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hlog1 : 1 ≤ Real.log (n : ℝ) :=
    (Real.le_log_iff_exp_le hn0).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hshiftN : n + s ≤ n ^ 2 := by have := (le_max_right _ _).trans hn; nlinarith
  have hshiftR : (n : ℝ) + s ≤ (n : ℝ) ^ 2 := by exact_mod_cast hshiftN
  have hlogShift : Real.log (n + s : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    calc _ ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) hshiftR
      _ = _ := by rw [Real.log_pow]; norm_num
  have hnlog : (Nat.log b (n + s) : ℝ) ≤ Real.log (n + s : ℝ) / Real.log b := by
    simpa only [Real.logb, Nat.cast_add] using Real.natLog_le_logb (n + s) b
  have hbase : (Nat.log b (n + s) : ℝ) + c ≤ a * Real.log (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hlogShift hlogb.le
    have hc := mul_le_mul_of_nonneg_left hlog1 (show (0 : ℝ) ≤ c by positivity)
    have hsum := _root_.add_le_add (hnlog.trans hdiv) hc
    calc
      _ ≤ (2 * Real.log (n : ℝ)) / Real.log b + c * Real.log (n : ℝ) := by
        simpa only [_root_.mul_one] using hsum
      _ = _ := by dsimp only [a]; ring
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Nat.log b (n + s) : ℝ) + c)
    hbase d
  have hpow0 : 0 ≤ (n : ℝ) ^ ε := Real.rpow_nonneg (by positivity) _
  dsimp only [Function.comp_apply] at he
  rw [Real.norm_eq_abs, Real.rpow_natCast, abs_of_nonneg (pow_nonneg (by linarith) _),
    Real.norm_eq_abs, abs_of_nonneg hpow0] at he
  calc K * ((Nat.log b (n + s) : ℝ) + c) ^ d
      ≤ K * (a * Real.log (n : ℝ)) ^ d := mul_le_mul_of_nonneg_left hp hK.le
    _ = (K * a ^ d) * Real.log (n : ℝ) ^ d := by rw [mul_pow]; ring
    _ ≤ (K * a ^ d) * ((K * a ^ d)⁻¹ * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left he hcoeff.le
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hcoeff.ne', one_mul]

/-- A fixed power of the binary length `Nat.size n + 1` is at most a constant times any positive
real power of `n + 1`, uniformly in `n`. -/
theorem exists_size_add_one_pow_le_mul_rpow (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, ((Nat.size n + 1 : ℕ) : ℝ) ^ d ≤ K * ((n : ℝ) + 1) ^ ε := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (eventually_mul_log_add_pow_le_rpow (b := 2) one_lt_two 0 2 d one_pos hε)
  set B : ℕ := (Finset.range M).sup fun n => (Nat.size n + 1) ^ d
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  refine ⟨B + 1, by linarith, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ ε :=
    Real.one_le_rpow (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hε.le
  by_cases hn : n < M
  · have hle : ((Nat.size n + 1 : ℕ) : ℝ) ^ d ≤ B := by
      exact_mod_cast Finset.le_sup (f := fun n => (Nat.size n + 1) ^ d) (Finset.mem_range.mpr hn)
    nlinarith
  · have h := hM n (not_lt.mp hn)
    simp only [Nat.add_zero, one_mul, Nat.cast_ofNat] at h
    have hsize : ((Nat.size n + 1 : ℕ) : ℝ) ≤ (Nat.log 2 n : ℝ) + 2 := by
      have : Nat.size n ≤ Nat.log 2 n + 1 :=
        Nat.size_le.mpr (Nat.lt_pow_succ_log_self one_lt_two n)
      have : (Nat.size n : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by exact_mod_cast this
      push_cast
      linarith
    have hp : ((Nat.size n + 1 : ℕ) : ℝ) ^ d ≤ ((Nat.log 2 n : ℝ) + 2) ^ d := by gcongr
    have hn' : (n : ℝ) ^ ε ≤ ((n : ℝ) + 1) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) hε.le
    nlinarith

end Nat
