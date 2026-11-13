/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Moments/SubGaussian.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.SubGaussian
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate

/-!
# The Azuma–Hoeffding inequality under a product measure

Let `Y i : (∀ j, α j) → ℝ`, for `i` in a finite linear order, be functions of independent
coordinates `v ∼ Measure.pi μ` such that

* `Y i` does not depend on the coordinates `j > i`;
* averaging `Y i` over coordinate `i` gives `0`;
* as coordinate `i` varies, `Y i` ranges in an interval of length `c i`, whose position may
  depend on the other coordinates.

Then `∑ i, Y i` has a sub-Gaussian moment generating function with parameter
`∑ i, (c i / 2) ^ 2` (`ProbabilityTheory.hasSubgaussianMGF_sum_pi`), so it is at least `ε ≥ 0`
with probability at most `exp (-2 ε² / ∑ i, c i ^ 2)` (`ProbabilityTheory.measure_sum_ge_le_pi`).
This is the Azuma–Hoeffding inequality [Hoeffding1963; Azuma1967] for the martingale differences
`Y i` of the natural filtration of the coordinates.

Mathlib states the inequality for conditionally sub-Gaussian increments
(`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`). That form needs conditional
expectation kernels on a standard Borel space, and Mathlib has no conditional form of Hoeffding's
lemma to supply its hypotheses. Here the conditioning is explicit. The proof integrates out one
coordinate at a time (`MeasureTheory.integral_integral_update`) and applies Hoeffding's lemma
(`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) for each fixed value of
the other coordinates, so the coordinate spaces `α j` are arbitrary measurable spaces.

`ProbabilityTheory.HasSubgaussianMGF.measure_sqrt_lt_le` is the sub-Gaussian tail bound at
confidence `δ`: a random variable with parameter `c` exceeds `√(2 c ln (1 / δ))` with
probability at most `δ`.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.measure_sqrt_lt_le`: the tail bound at confidence `δ`.
* `ProbabilityTheory.hasSubgaussianMGF_sum_pi`: a sum of bounded martingale differences of
  independent coordinates is sub-Gaussian.
* `ProbabilityTheory.measure_sum_ge_le_pi`: the Azuma–Hoeffding inequality.

## References

* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
* [K. Azuma, *Weighted sums of certain dependent random variables*][Azuma1967]
-/

public section

open MeasureTheory Real Finset
open scoped NNReal

namespace ProbabilityTheory

section Tail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
  {c : ℝ≥0}

/-- **Sub-Gaussian tail bound at confidence `δ`.** A random variable with a sub-Gaussian moment
generating function with parameter `c` exceeds `√(2 c ln (1 / δ))` with probability at most `δ`. -/
theorem HasSubgaussianMGF.measure_sqrt_lt_le (h : HasSubgaussianMGF X c μ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | √(2 * c * log (1 / δ)) < X ω} ≤ δ := by
  have hL : 0 ≤ log (1 / δ) := log_nonneg (by rw [le_div_iff₀ hδ]; simpa using hδ1)
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : μ {ω | 0 < X ω} = 0 :=
      measure_mono_null (fun ω (hω : 0 < X ω) => by simp [hω.ne'])
        (ae_iff.1 h.ae_eq_zero_of_hasSubgaussianMGF_zero)
    simpa [measureReal_def, h0] using hδ.le
  · have hc' : (0 : ℝ) < c := by positivity
    calc μ.real {ω | √(2 * c * log (1 / δ)) < X ω}
        ≤ μ.real {ω | √(2 * c * log (1 / δ)) ≤ X ω} :=
          measureReal_mono (Set.ofPred_subset_ofPred.2 fun _ hω => hω.le)
      _ ≤ exp (-√(2 * c * log (1 / δ)) ^ 2 / (2 * c)) := h.measure_ge_le (sqrt_nonneg _)
      _ = δ := by
        rw [sq_sqrt (by positivity), one_div, log_inv,
          show -(2 * (c : ℝ) * -log δ) / (2 * c) = log δ by field_simp, exp_log hδ]

end Tail

section Pi

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (μ i)]
  {Y : ι → (∀ i, α i) → ℝ} {c : ι → ℝ≥0}

omit [Fintype ι] [LinearOrder ι] in
/-- A function with mean `0` over coordinate `i` that ranges over an interval of length `c` as
coordinate `i` varies is bounded by `c` in absolute value. -/
private theorem abs_le_of_integral_update_eq_zero {Y : (∀ i, α i) → ℝ} {i : ι} {c : ℝ≥0}
    (hY : Measurable Y) (hmean : ∀ v, ∫ z, Y (Function.update v i z) ∂μ i = 0)
    (hrange : ∀ v, ∃ a : ℝ, ∀ z, Y (Function.update v i z) ∈ Set.Icc a (a + c))
    (v : ∀ i, α i) : |Y v| ≤ c := by
  obtain ⟨a, ha⟩ := hrange v
  have hint : Integrable (fun z => Y (Function.update v i z)) (μ i) :=
    Integrable.of_mem_Icc a (a + c) (hY.comp (measurable_update v)).aemeasurable
      (Filter.Eventually.of_forall ha)
  have h1 : a ≤ 0 := by
    simpa [hmean v] using integral_mono (integrable_const a) hint fun z => (ha z).1
  have h2 : 0 ≤ a + c := by
    simpa [hmean v] using integral_mono hint (integrable_const (a + c)) fun z => (ha z).2
  have hv := ha (v i)
  rw [Function.update_eq_self] at hv
  rw [abs_le]
  constructor <;> linarith [hv.1, hv.2]

/-- **Azuma–Hoeffding under a product measure, sub-Gaussian form.** Let `Y i` not depend on the
coordinates after `i`, have mean `0` over coordinate `i`, and range over an interval of length
`c i` as coordinate `i` varies. Then `∑ i, Y i` has a sub-Gaussian moment generating function
with parameter `∑ i, (c i / 2) ^ 2` under `Measure.pi μ`. -/
theorem hasSubgaussianMGF_sum_pi (hY : ∀ i, Measurable (Y i))
    (hadapted : ∀ i j, i < j → ∀ v z, Y i (Function.update v j z) = Y i v)
    (hmean : ∀ i v, ∫ z, Y i (Function.update v i z) ∂μ i = 0)
    (hrange : ∀ i v, ∃ a : ℝ, ∀ z, Y i (Function.update v i z) ∈ Set.Icc a (a + c i)) :
    HasSubgaussianMGF (fun v => ∑ i, Y i v) (∑ i, (c i / 2) ^ 2) (Measure.pi μ) := by
  have habs : ∀ i v, |Y i v| ≤ c i := fun i =>
    abs_le_of_integral_update_eq_zero (hY i) (hmean i) (hrange i)
  have hint : ∀ (s : Finset ι) (t : ℝ),
      Integrable (fun v => exp (t * ∑ i ∈ s, Y i v)) (Measure.pi μ) := fun s t =>
    Integrable.of_bound
      (measurable_const.mul (Finset.measurable_sum s fun i _ => hY i)).exp.aestronglyMeasurable
      (exp (|t| * ∑ i ∈ s, (c i : ℝ))) (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_exp, exp_le_exp]
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          ((abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => habs i v)) (abs_nonneg t))
  have key : ∀ (s : Finset ι) (t : ℝ), ∫ v, exp (t * ∑ i ∈ s, Y i v) ∂Measure.pi μ ≤
      exp ((∑ i ∈ s, ((c i : ℝ) / 2) ^ 2) * t ^ 2 / 2) := by
    intro s t
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert j s hlt ih =>
      have hj : j ∉ s := fun h => lt_irrefl j (hlt j h)
      have hP : ∀ v z, ∑ i ∈ s, Y i (Function.update v j z) = ∑ i ∈ s, Y i v :=
        fun v z => Finset.sum_congr rfl fun i hi => hadapted i j (hlt i hi) v z
      have hstep : ∀ v, ∫ z, exp (t * Y j (Function.update v j z)) ∂μ j ≤
          exp (((c j : ℝ) / 2) ^ 2 * t ^ 2 / 2) := by
        intro v
        obtain ⟨a, ha⟩ := hrange j v
        have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
          ((hY j).comp (measurable_update v)).aemeasurable (Filter.Eventually.of_forall ha)
          (hmean j v)
        simpa [mgf] using hsub.mgf_le t
      calc ∫ v, exp (t * ∑ i ∈ insert j s, Y i v) ∂Measure.pi μ
          = ∫ v, ∫ z, exp (t * ∑ i ∈ insert j s, Y i (Function.update v j z)) ∂μ j
              ∂Measure.pi μ := (integral_integral_update μ (hint (insert j s) t) j).symm
        _ = ∫ v, exp (t * ∑ i ∈ s, Y i v) *
              ∫ z, exp (t * Y j (Function.update v j z)) ∂μ j ∂Measure.pi μ := by
            congr 1 with v
            rw [← integral_const_mul]
            congr 1 with z
            rw [Finset.sum_insert hj, hP, mul_add, exp_add]
            exact mul_comm _ _
        _ ≤ ∫ v, exp (t * ∑ i ∈ s, Y i v) * exp (((c j : ℝ) / 2) ^ 2 * t ^ 2 / 2)
              ∂Measure.pi μ :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun v =>
                mul_nonneg (exp_pos _).le (integral_nonneg fun _ => (exp_pos _).le))
              ((hint s t).mul_const _)
              (Filter.Eventually.of_forall fun v =>
                mul_le_mul_of_nonneg_left (hstep v) (exp_pos _).le)
        _ = (∫ v, exp (t * ∑ i ∈ s, Y i v) ∂Measure.pi μ) *
              exp (((c j : ℝ) / 2) ^ 2 * t ^ 2 / 2) := integral_mul_const _ _
        _ ≤ exp ((∑ i ∈ s, ((c i : ℝ) / 2) ^ 2) * t ^ 2 / 2) *
              exp (((c j : ℝ) / 2) ^ 2 * t ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right ih (exp_pos _).le
        _ = exp ((∑ i ∈ insert j s, ((c i : ℝ) / 2) ^ 2) * t ^ 2 / 2) := by
            rw [← exp_add, Finset.sum_insert hj]
            ring_nf
  refine ⟨hint univ, fun t => ?_⟩
  simpa [mgf] using key univ t

/-- **The Azuma–Hoeffding inequality under a product measure.** Let `Y i` not depend on the
coordinates after `i`, have mean `0` over coordinate `i`, and range over an interval of length
`c i` as coordinate `i` varies. Then `∑ i, Y i ≥ ε` with probability at most
`exp (-2 ε² / ∑ i, c i ^ 2)` under `Measure.pi μ`, for every `ε ≥ 0`. -/
theorem measure_sum_ge_le_pi (hY : ∀ i, Measurable (Y i))
    (hadapted : ∀ i j, i < j → ∀ v z, Y i (Function.update v j z) = Y i v)
    (hmean : ∀ i v, ∫ z, Y i (Function.update v i z) ∂μ i = 0)
    (hrange : ∀ i v, ∃ a : ℝ, ∀ z, Y i (Function.update v i z) ∈ Set.Icc a (a + c i))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real {v | ε ≤ ∑ i, Y i v} ≤ exp (-2 * ε ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  refine ((hasSubgaussianMGF_sum_pi hY hadapted hmean hrange).measure_ge_le hε).trans_eq ?_
  congr 1
  push_cast
  simp only [div_pow, ← Finset.sum_div]
  ring

end Pi

end ProbabilityTheory
