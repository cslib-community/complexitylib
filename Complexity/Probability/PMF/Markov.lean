/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import Complexity.Probability.PMF

/-!
# Markov's inequality for discrete distributions

For a discrete distribution `p` and an extended nonnegative score `f`, the probability that `f` is
at least `t`, scaled by `t`, is at most the expectation `∑' i, p i * f i`. The statement needs no
measurable structure. Mathlib's `MeasureTheory.mul_meas_ge_le_lintegral` is the measure-theoretic
form, and `Fintype.mul_dens_filter_le_expect` the uniform finite form.

## Main results

* `Cslib.Probability.PMF.mul_toOuterMeasure_le_tsum`: `t · Pr[t ≤ f] ≤ E[f]`.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {ι : Type*}

/-- **Markov's inequality** for a probability mass function and an extended nonnegative score:
`t · Pr[t ≤ f] ≤ E[f]`. -/
theorem mul_toOuterMeasure_le_tsum (p : PMF ι) (f : ι → ℝ≥0∞) (t : ℝ≥0∞) :
    t * p.toOuterMeasure {i | t ≤ f i} ≤ ∑' i, p i * f i := by
  rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun i => ?_
  by_cases hi : t ≤ f i
  · rw [Set.indicator_of_mem (by exact hi), mul_comm]
    gcongr
  · rw [Set.indicator_of_notMem (by exact hi), mul_zero]
    positivity

end Cslib.Probability.PMF
