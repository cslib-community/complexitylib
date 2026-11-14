/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Real.lean`)

public import CslibFrontier.Foundations.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Real

/-!
# The cumulative distribution function of a real Gaussian

A nondegenerate real Gaussian has no atoms and charges every set of positive Lebesgue measure, so
its cdf is continuous and strictly increasing, and it satisfies the probability integral
transform `P[Φ x ≤ α] = α` for `α ∈ [0, 1]` (see `CslibFrontier.Foundations.Probability.CDF`). The
cdf `Φ` of a centered real Gaussian is symmetric: `Φ (-x) = 1 - Φ x` (`cdf_gaussianReal_neg`),
so `Φ 0 = 1 / 2`.

## Main results

* `ProbabilityTheory.continuous_cdf_gaussianReal`, `ProbabilityTheory.strictMono_cdf_gaussianReal`:
  regularity of a Gaussian cdf.
* `ProbabilityTheory.measureReal_setOf_cdf_gaussianReal_le`: the probability integral transform
  for a Gaussian.
* `ProbabilityTheory.cdf_gaussianReal_neg`, `ProbabilityTheory.cdf_gaussianReal_zero_zero`: the
  symmetry of a centered Gaussian cdf, and `Φ 0 = 1 / 2`.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

/-- The cdf of a nondegenerate real Gaussian is continuous. -/
theorem continuous_cdf_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Continuous (cdf (gaussianReal μ v)) :=
  have := nullSingletonClass_gaussianReal (μ := μ) hv
  continuous_cdf

/-- The cdf of a nondegenerate real Gaussian is strictly increasing. -/
theorem strictMono_cdf_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    StrictMono (cdf (gaussianReal μ v)) :=
  strictMono_cdf (gaussianReal_absolutelyContinuous' μ hv)

/-- **The probability integral transform** for a nondegenerate real Gaussian with cdf `Φ`:
`Φ x ≤ α` has probability `α` for `α ∈ [0, 1]`. -/
theorem measureReal_setOf_cdf_gaussianReal_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ}
    (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (gaussianReal μ v).real {x | cdf (gaussianReal μ v) x ≤ α} = α :=
  have := nullSingletonClass_gaussianReal (μ := μ) hv
  measureReal_setOf_cdf_le h0 h1

/-- The cdf `Φ` of a nondegenerate centered real Gaussian is symmetric: `Φ (-x) = 1 - Φ x`. -/
theorem cdf_gaussianReal_neg {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    cdf (gaussianReal 0 v) (-x) = 1 - cdf (gaussianReal 0 v) x := by
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  have hpre : (fun y : ℝ => -y) ⁻¹' Iic (-x) = Ici x := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_le_neg_iff]
  rw [cdf_eq_real, cdf_eq_real, ← gaussianReal_zero_map_neg,
    map_measureReal_apply measurable_neg measurableSet_Iic, gaussianReal_zero_map_neg, hpre,
    ← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio, measureReal_congr Iio_ae_eq_Iic]

/-- The cdf of a nondegenerate centered real Gaussian is `1 / 2` at `0`. -/
theorem cdf_gaussianReal_zero_zero {v : ℝ≥0} (hv : v ≠ 0) :
    cdf (gaussianReal 0 v) 0 = 2⁻¹ := by
  have h := cdf_gaussianReal_neg hv 0
  rw [neg_zero] at h
  linarith

end ProbabilityTheory
