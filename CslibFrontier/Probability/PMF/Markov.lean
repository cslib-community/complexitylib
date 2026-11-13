/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF

/-!
# Markov's inequality for discrete distributions

For a discrete distribution `p` and an extended nonnegative score `f`, the probability that `f` is
at least `t`, scaled by `t`, is at most the expectation `∑' i, p i * f i`. The statement needs no
measurable structure. Mathlib's `MeasureTheory.mul_meas_ge_le_lintegral` is the measure-theoretic
form, and `Fintype.mul_dens_filter_le_expect` the uniform finite form.

## Main results

* `Cslib.Probability.PMF.mul_toOuterMeasure_le_tsum`: `t · Pr[t ≤ f] ≤ E[f]`.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_le_tsum_div`: `Pr[t ≤ f] ≤ E[f] / t` for a real
  score with values in `[0, 1]`.
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

/-- **Markov's inequality** for a real score with values in `[0, 1]`:
`Pr[t ≤ f] ≤ E[f] / t`. -/
theorem toOuterMeasure_toReal_le_tsum_div (p : PMF ι) {f : ι → ℝ} (hf₀ : ∀ i, 0 ≤ f i)
    (hf₁ : ∀ i, f i ≤ 1) {t : ℝ} (ht : 0 < t) :
    (p.toOuterMeasure {i | t ≤ f i}).toReal ≤ (∑' i, (p i).toReal * f i) / t := by
  have hmarkov := mul_toOuterMeasure_le_tsum p (fun i => ENNReal.ofReal (f i)) (ENNReal.ofReal t)
  have hset : {i | ENNReal.ofReal t ≤ ENNReal.ofReal (f i)} = {i | t ≤ f i} := by
    ext i
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (hf₀ i)]
  rw [hset] at hmarkov
  have hne : (∑' i, p i * ENNReal.ofReal (f i)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∑' i, p i * ENNReal.ofReal (f i)
        ≤ ∑' i, p i :=
          tsum_le_tsum fun i => mul_le_of_le_one_right' (ENNReal.ofReal_le_one.mpr (hf₁ i))
      _ = 1 := p.tsum_coe
  have hreal := ENNReal.toReal_mono hne hmarkov
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
    ENNReal.tsum_toReal_eq fun i => ENNReal.mul_ne_top (p.apply_ne_top i) ENNReal.ofReal_ne_top]
    at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf₀ _)] at hreal
  rw [le_div_iff₀ ht, mul_comm]
  exact hreal

end Cslib.Probability.PMF
