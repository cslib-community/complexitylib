/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The sublinear exponent of the interpolation counting algorithm

The rational-interpolation route of OpenAI's *The Exponential Time Hypothesis is False*,
Proposition 6.4, uses the scale `n (log log n)² / √log n`. Shifting the logarithm's argument
by sixteen gives a real-valued scale defined at every natural input. This module proves that
the scale is sublinear. It does not construct a counting algorithm or certify its running time.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.interpolationScale`: the shifted interpolation exponent.

## Main results

* `Cslib.Complexity.SubexponentialSAT.isLittleO_interpolationScale`: the exponent is `o(n)`.
* `Cslib.Complexity.SubexponentialSAT.eventually_mul_interpolationScale_le`: every fixed
  multiple is eventually bounded by any positive linear exponent.
* `Cslib.Complexity.SubexponentialSAT.interpolationScale_zero`,
  `Cslib.Complexity.SubexponentialSAT.interpolationScale_pos`,
  `Cslib.Complexity.SubexponentialSAT.one_lt_log_add_sixteen`,
  `Cslib.Complexity.SubexponentialSAT.one_lt_log_log_add_sixteen`: zero value and strict positivity
  of the shifted logarithms and interpolation scale.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH],
  Proposition 6.4, pp. 43–44.
-/

@[expose] public section

namespace Cslib.Complexity.SubexponentialSAT

open Filter Asymptotics
open scoped Topology

/-- The interpolation exponent with a positive logarithm argument at every natural input. -/
noncomputable def interpolationScale (n : ℕ) : ℝ :=
  n * Real.log (Real.log ((n : ℝ) + 16)) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16))

private theorem tendsto_ratio :
    Tendsto (fun n : ℕ =>
      Real.log (Real.log ((n : ℝ) + 16)) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp <|
      tendsto_atTop_add_const_right atTop (16 : ℝ) tendsto_natCast_atTop_atTop
  have h := (isLittleO_log_rpow_rpow_atTop
    (s := (1 / 2 : ℝ)) 2 (by norm_num)).tendsto_div_nhds_zero
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, Function.comp_def] using h.comp hlog

/-- The interpolation exponent grows more slowly than the number of variables. -/
theorem isLittleO_interpolationScale :
    interpolationScale =o[atTop] fun n : ℕ => (n : ℝ) := by
  unfold interpolationScale
  have hr : (fun n : ℕ =>
      Real.log (Real.log ((n : ℝ) + 16)) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16)))
      =o[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr tendsto_ratio
  simpa only [interpolationScale, mul_one, mul_div_assoc] using
    (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO hr

/-- Every fixed multiple of the exponent is eventually at most any positive linear exponent. -/
theorem eventually_mul_interpolationScale_le (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, A * interpolationScale n ≤ ε * n := by
  have ht : Tendsto (fun n : ℕ => A *
      (Real.log (Real.log ((n : ℝ) + 16)) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_ratio
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  have h := mul_le_mul_of_nonneg_right hn.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [interpolationScale, mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using h

/-- The interpolation scale is nonnegative at every natural input. -/
theorem interpolationScale_nonneg (n : ℕ) : 0 ≤ interpolationScale n := by
  unfold interpolationScale
  positivity

/-- At zero variables, the shifted interpolation scale vanishes. -/
@[simp]
theorem interpolationScale_zero : interpolationScale 0 = 0 := by
  simp only [interpolationScale, CharP.cast_eq_zero, zero_mul, zero_div]

private theorem exp_one_lt_log_add_sixteen (n : ℕ) :
    Real.exp 1 < Real.log ((n : ℝ) + 16) := by
  have h16 : (16 : ℝ) ≤ (n : ℝ) + 16 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlog16 : 4 * Real.log 2 ≤ Real.log ((n : ℝ) + 16) := by
    have hpow : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    exact hpow ▸ Real.log_le_log (by norm_num) h16
  linarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]

/-- For every natural `n`, the shifted logarithm `log (n + 16)` exceeds `1`. -/
theorem one_lt_log_add_sixteen (n : ℕ) : 1 < Real.log ((n : ℝ) + 16) := by
  linarith [Real.exp_one_gt_d9, exp_one_lt_log_add_sixteen n]

/-- For every natural `n`, `0 < log (n + 16)`. -/
theorem log_add_sixteen_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 16) :=
  zero_lt_one.trans (one_lt_log_add_sixteen n)

/-- For every natural `n`, the shifted iterated logarithm `log (log (n + 16))` exceeds `1`
(since `16 = 2 ^ 4` and `4 * log 2 > e`). -/
theorem one_lt_log_log_add_sixteen (n : ℕ) :
    1 < Real.log (Real.log ((n : ℝ) + 16)) := by
  have hlog := Real.log_lt_log (Real.exp_pos 1) (exp_one_lt_log_add_sixteen n)
  rwa [Real.log_exp] at hlog

/-- For every natural `n`, `0 < log (log (n + 16))`. -/
theorem log_log_add_sixteen_pos (n : ℕ) : 0 < Real.log (Real.log ((n : ℝ) + 16)) :=
  zero_lt_one.trans (one_lt_log_log_add_sixteen n)

/-- The interpolation scale is strictly positive for `1 ≤ n`. -/
theorem interpolationScale_pos {n : ℕ} (hn : 1 ≤ n) : 0 < interpolationScale n := by
  unfold interpolationScale
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hll : 0 < Real.log (Real.log ((n : ℝ) + 16)) := log_log_add_sixteen_pos n
  have hl : 0 < Real.sqrt (Real.log ((n : ℝ) + 16)) := Real.sqrt_pos.mpr (log_add_sixteen_pos n)
  positivity

/-- For any multiplier `A` and any `ε > 0`, `2 ^ (A * interpolationScale n)` is globally bounded
by a constant multiple of `2 ^ (ε * n)`. -/
theorem exists_two_pow_mul_interpolationScale_le (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, (2 : ℝ) ^ (A * interpolationScale n) ≤ K * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_mul_interpolationScale_le A hε)
  let K : ℝ := 1 + ∑ m ∈ Finset.range N₀, (2 : ℝ) ^ (A * interpolationScale m)
  have hsum_nonneg : 0 ≤ ∑ m ∈ Finset.range N₀, (2 : ℝ) ^ (A * interpolationScale m) :=
    Finset.sum_nonneg fun m _ => by positivity
  have hK1 : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK1, fun n => ?_⟩
  have h2ε : (1 : ℝ) ≤ (2 : ℝ) ^ (ε * n) := Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hn : n < N₀
  · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hn
    have hle_sum : (2 : ℝ) ^ (A * interpolationScale n) ≤
        ∑ m ∈ Finset.range N₀, (2 : ℝ) ^ (A * interpolationScale m) :=
      Finset.single_le_sum (f := fun m => (2 : ℝ) ^ (A * interpolationScale m))
        (fun m _ => by positivity) hmem
    have hle_K : (2 : ℝ) ^ (A * interpolationScale n) ≤ K := by dsimp [K]; linarith
    exact hle_K.trans (le_mul_of_one_le_right (by positivity) h2ε)
  · have hle : A * interpolationScale n ≤ ε * n := hN₀ n (not_lt.mp hn)
    have hrpow : (2 : ℝ) ^ (A * interpolationScale n) ≤ (2 : ℝ) ^ (ε * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    exact hrpow.trans (le_mul_of_one_le_left (by positivity) hK1)

end Cslib.Complexity.SubexponentialSAT
