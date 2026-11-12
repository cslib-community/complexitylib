/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Measure representation of a `PMF` without discrete singletons

Expresses `PMF.toMeasure` as a countable sum of weighted Dirac measures and computes its Lebesgue
integral `∫⁻ y, f y ∂p.toMeasure = ∑' y, p y * f y` without requiring `[MeasurableSingletonClass α]`
or `[Countable α]` (compare Mathlib's `PMF.integral_eq_tsum`, which requires
`MeasurableSingletonClass`).

## Main results

* `PMF.toMeasure_eq_sum`: `p.toMeasure = Measure.sum fun y => p y • Measure.dirac y`.
* `PMF.lintegral_toMeasure`: `∫⁻ y, f y ∂p.toMeasure = ∑' y, p y * f y` for any measurable
  `f : α → ℝ≥0∞`.
-/

public section

namespace PMF

open MeasureTheory
open scoped ENNReal

/-- Every `PMF` induces the sum of weighted Dirac measures on any measurable space. -/
theorem toMeasure_eq_sum {α : Type*} [MeasurableSpace α] (p : PMF α) :
    p.toMeasure = Measure.sum fun y : α => p y • Measure.dirac y := by
  classical
  refine Measure.ext fun s hs => ?_
  rw [p.toMeasure_apply hs, Measure.sum_apply _ hs]
  refine tsum_congr fun y => ?_
  rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs, Set.indicator_apply]
  split_ifs with hy
  · simp [hy]
  · simp [hy]

/-- Lebesgue integration against `p.toMeasure` equals `∑' y, p y * f y` on any measurable space,
without requiring `MeasurableSingletonClass` or `Countable`. -/
theorem lintegral_toMeasure {α : Type*} [MeasurableSpace α] (p : PMF α) {f : α → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ y, f y ∂p.toMeasure = ∑' y, p y * f y := by
  rw [p.toMeasure_eq_sum, lintegral_sum_measure]
  refine tsum_congr fun y => ?_
  rw [lintegral_smul_measure, lintegral_dirac' y hf, smul_eq_mul]

end PMF
