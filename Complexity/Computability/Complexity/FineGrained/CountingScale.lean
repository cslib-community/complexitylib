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

end Cslib.Complexity.SubexponentialSAT
