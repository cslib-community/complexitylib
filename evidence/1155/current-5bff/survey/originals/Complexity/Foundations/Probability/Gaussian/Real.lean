/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Real.lean`)

public import Complexity.Init
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Intervals and tails of real Gaussian distributions

Three estimates for the real Gaussian distribution `gaussianReal μ v`:

* **Peak density.** The density is largest at the mean, where it is `1 / √(2πv)`
  (`gaussianPDFReal_le`), so a nondegenerate Gaussian gives each set at most `1 / √(2πv)` times
  its Lebesgue measure (`gaussianReal_le_ofReal_mul_volume`).
* **Anderson's inequality on the line.** Among the intervals of a given length, the one centered
  at the mean has the largest mass (`gaussianReal_Icc_le`). For an interval `[c - w, c + w]` with
  `c ≥ μ`, the two intervals share `[c - w, μ + w]`, and translation by `2 w` carries the rest
  `[μ - w, c - w]` of the centered interval onto the rest `[μ + w, c + w]` of the shifted one,
  without increasing the density there.
* **Chebyshev's inequality.** The deviation from the mean is at least `c` with probability at
  most `v / c ^ 2` (`gaussianReal_meas_ge_le`).

## Main results

* `ProbabilityTheory.gaussianPDFReal_le`: the Gaussian density is at most `1 / √(2πv)`.
* `ProbabilityTheory.gaussianReal_le_ofReal_mul_volume`: the Gaussian measure of a set is at most
  `1 / √(2πv)` times its Lebesgue measure.
* `ProbabilityTheory.gaussianReal_Icc_le`: Anderson's inequality on the line.
* `ProbabilityTheory.gaussianReal_meas_ge_le`: Chebyshev's inequality for a Gaussian.
-/

@[expose] public section

open MeasureTheory Real Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- The Gaussian density is at most its value `1 / √(2πv)` at the mean. -/
theorem gaussianPDFReal_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (√(2 * π * v))⁻¹ := by
  rw [gaussianPDFReal]
  refine mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

/-- A nondegenerate Gaussian gives each set at most the peak density `1 / √(2πv)` times its
Lebesgue measure. -/
theorem gaussianReal_le_ofReal_mul_volume (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s ≤ ENNReal.ofReal (√(2 * π * v))⁻¹ * volume s := by
  rw [gaussianReal_apply μ hv, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (gaussianPDFReal_le μ v x)

/-- If translating by `2 w` does not increase `f` to the right of `-w`, then the interval of
radius `w` around `c ≥ 0` carries at most the mass of the centered one: the two intervals share
`[c - w, w]`, and the translation carries `[-w, c - w]` onto `[w, c + w]`. -/
private theorem intervalIntegral_shift_le {f : ℝ → ℝ} (hf : Continuous f) {c w : ℝ}
    (hc : 0 ≤ c) (hmono : ∀ x, -w ≤ x → f (x + 2 * w) ≤ f x) :
    ∫ x in (c - w)..(c + w), f x ≤ ∫ x in (-w)..w, f x := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (c - w) w) (hf.intervalIntegrable w (c + w))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-w) (c - w)) (hf.intervalIntegrable (c - w) w)
  have h3 : ∫ x in w..(c + w), f x = ∫ x in (-w)..(c - w), f (x + 2 * w) := by
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  have h4 : ∫ x in (-w)..(c - w), f (x + 2 * w) ≤ ∫ x in (-w)..(c - w), f x :=
    intervalIntegral.integral_mono_on (by linarith)
      ((hf.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
      (hf.intervalIntegrable _ _) fun x hx => hmono x hx.1
  linarith

/-- The centered Gaussian density does not increase under translation by `2 w` to the right of
`-w`. -/
private theorem gaussianPDFReal_add_two_mul_le (v : ℝ≥0) {w x : ℝ} (hw : 0 ≤ w)
    (hx : -w ≤ x) : gaussianPDFReal 0 v (x + 2 * w) ≤ gaussianPDFReal 0 v x := by
  simp only [gaussianPDFReal_def, sub_zero]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- Anderson's inequality on the line for a centered Gaussian. -/
private theorem gaussianReal_zero_Icc_le (v : ℝ≥0) (c w : ℝ) :
    gaussianReal 0 v (Icc (c - w) (c + w)) ≤ gaussianReal 0 v (Icc (-w) w) := by
  rcases lt_or_ge w 0 with hw | hw
  · rw [Icc_eq_empty (by linarith), measure_empty]
    exact bot_le
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var, Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ Icc (-w) w from
      ⟨by linarith, hw⟩)]
    exact prob_le_one
  rw [gaussianReal_apply_eq_integral _ hv, gaussianReal_apply_eq_integral _ hv,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcont : Continuous (gaussianPDFReal 0 v) := by
    rw [gaussianPDFReal_def]
    fun_prop
  have hmono : ∀ x, -w ≤ x → gaussianPDFReal 0 v (x + 2 * w) ≤ gaussianPDFReal 0 v x :=
    fun x hx => gaussianPDFReal_add_two_mul_le v hw hx
  rcases le_total 0 c with hc | hc
  · exact intervalIntegral_shift_le hcont hc hmono
  -- Reflect through the mean, using that the density is even.
  have hrefl : ∫ x in (c - w)..(c + w), gaussianPDFReal 0 v x =
      ∫ x in (-c - w)..(-c + w), gaussianPDFReal 0 v x := by
    calc ∫ x in (c - w)..(c + w), gaussianPDFReal 0 v x
        = ∫ x in (c - w)..(c + w), gaussianPDFReal 0 v (-x) := by
          simp [gaussianPDFReal_def]
      _ = _ := by
          rw [intervalIntegral.integral_comp_neg]
          congr 1 <;> ring
  rw [hrefl]
  exact intervalIntegral_shift_le hcont (by linarith) hmono

/-- **Anderson's inequality on the line.** A Gaussian gives an interval of radius `w` the most
mass when it is centered at the mean. -/
theorem gaussianReal_Icc_le (μ : ℝ) (v : ℝ≥0) (c w : ℝ) :
    gaussianReal μ v (Icc (c - w) (c + w)) ≤ gaussianReal μ v (Icc (μ - w) (μ + w)) := by
  have h : gaussianReal μ v = (gaussianReal 0 v).map (· + μ) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [h, Measure.map_apply (measurable_add_const μ) measurableSet_Icc,
    Measure.map_apply (measurable_add_const μ) measurableSet_Icc, preimage_add_const_Icc,
    preimage_add_const_Icc]
  convert gaussianReal_zero_Icc_le v (c - μ) w using 3 <;> ring

/-- **Chebyshev's inequality for a Gaussian.** A Gaussian deviates from its mean by at least
`c > 0` with probability at most `v / c ^ 2`. -/
theorem gaussianReal_meas_ge_le (μ : ℝ) (v : ℝ≥0) {c : ℝ} (hc : 0 < c) :
    gaussianReal μ v {x | c ≤ |x - μ|} ≤ ENNReal.ofReal (v / c ^ 2) := by
  simpa [integral_id_gaussianReal, variance_id_gaussianReal] using
    meas_ge_le_variance_div_sq (μ := gaussianReal μ v) (memLp_id_gaussianReal 2) hc

end ProbabilityTheory
