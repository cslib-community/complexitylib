/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/InformationTheory/KullbackLeibler/Pinsker.lean`)

public import Complexity.Init
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Pinsker's inequality

For probability measures `μ` and `ν` and a measurable event `s`,
`2 (μ s - ν s)² ≤ klDiv μ ν`, the Kullback–Leibler divergence in nats
(`Cslib.Probability.ofReal_two_mul_sq_measureReal_sub_le_klDiv`). The proof is the variational
one: Gibbs' inequality for an exponentially tilted measure (Mathlib's
`integral_llr_tilted_right`) and Hoeffding's lemma for the indicator of the event. A Hahn
decomposition then gives the form with Mathlib's total variation distance,
`tvDist μ ν ^ 2 / 2 ≤ klDiv μ ν` (`Cslib.Probability.ofReal_tvDist_sq_div_two_le_klDiv`).
The finite-distribution forms, in terms of statistical distance, are in `Probability/Divergence`.

## Main results

* `Cslib.Probability.ofReal_two_mul_sq_measureReal_sub_le_klDiv`: Pinsker for an event.
* `Cslib.Probability.ofReal_tvDist_sq_div_two_le_klDiv`: Pinsker with Mathlib's `tvDist`.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Lemma 11.6.1.
-/

@[expose] public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory InformationTheory

variable {α : Type*}

/-- **Pinsker's inequality** for a single event: `2 (μ s - ν s)² ≤ klDiv μ ν`, the divergence in
nats, for probability measures and a measurable event `s`. The statement holds unconditionally
since `klDiv μ ν = ∞` when `μ` is not absolutely continuous with respect to `ν` or the
log-likelihood ratio is not integrable. -/
theorem ofReal_two_mul_sq_measureReal_sub_le_klDiv {mα : MeasurableSpace α}
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) ≤ klDiv μ ν := by
  by_cases hac : μ ≪ ν
  swap; · simp [klDiv_of_not_ac hac]
  by_cases hint : Integrable (llr μ ν) μ
  swap; · simp [klDiv_of_not_integrable hint]
  rw [klDiv_of_ac_of_integrable hac hint]
  apply ENNReal.ofReal_le_ofReal
  simp only [probReal_univ, add_sub_cancel_right]
  set δ := μ.real s - ν.real s
  set t := 4 * δ
  let X : α → ℝ := s.indicator fun _ => 1
  have hX : Measurable X := measurable_const.indicator hs
  have hXmem (x : α) : X x ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ s <;> simp [X, hx]
  have hexp : Integrable (fun x => Real.exp (t * X x)) ν :=
    Integrable.of_bound (by fun_prop) (Real.exp |t|) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      calc t * X x ≤ |t * X x| := le_abs_self _
        _ = |t| * X x := by rw [abs_mul, abs_of_nonneg (hXmem x).1]
        _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hXmem x).2 (abs_nonneg t)
        _ = |t| := mul_one _)
  have hfμ : Integrable (fun x => t * X x) μ := ((integrable_const 1).indicator hs).const_mul t
  -- Gibbs' inequality for the tilted measure `ν.tilted (t * X)`.
  have hgibbs : 0 ≤ ∫ x, llr μ (ν.tilted fun x => t * X x) x ∂μ := by
    have := isProbabilityMeasure_tilted hexp
    have h := integral_llr_add_sub_measure_univ_nonneg
      (hac.trans (absolutelyContinuous_tilted hexp))
      (integrable_llr_tilted_right hac hfμ hint hexp)
    simpa only [probReal_univ, add_sub_cancel_right] using h
  rw [integral_llr_tilted_right hac hfμ hexp hint] at hgibbs
  -- Hoeffding's lemma for the indicator of `s` under `ν`.
  have hmean : ∫ x, X x ∂ν = ν.real s := by
    rw [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one]
  have hhoeffding : ∫ x, Real.exp (t * X x) ∂ν ≤ Real.exp (t * ν.real s + t ^ 2 / 8) := by
    have h := (hasSubgaussianMGF_of_mem_Icc (μ := ν) hX.aemeasurable (ae_of_all _ hXmem)).mgf_le t
    rw [hmean, show (fun x => X x - ν.real s) = fun x => X x + -ν.real s from
      funext fun _ => sub_eq_add_neg _ _, mgf_add_const] at h
    rw [mgf] at h
    calc ∫ x, Real.exp (t * X x) ∂ν
        = ((∫ x, Real.exp (t * X x) ∂ν) * Real.exp (t * -ν.real s)) *
            Real.exp (t * ν.real s) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 * t ^ 2 / 2) * Real.exp (t * ν.real s) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = Real.exp (t * ν.real s + t ^ 2 / 8) := by
          rw [← Real.exp_add, sub_zero, nnnorm_one]
          congr 1
          push_cast
          ring
  have hlog : Real.log (∫ x, Real.exp (t * X x) ∂ν) ≤ t * ν.real s + t ^ 2 / 8 :=
    (Real.log_le_iff_le_exp (integral_exp_pos hexp)).mpr hhoeffding
  have hint_f : ∫ x, t * X x ∂μ = t * μ.real s := by
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one]
  rw [hint_f] at hgibbs
  nlinarith [sq_nonneg δ]

/-- **Pinsker's inequality** with Mathlib's total variation distance `tvDist`, which takes values
in `[0, 2]` for probability measures: `tvDist μ ν ^ 2 / 2 ≤ klDiv μ ν`, the divergence in nats. It
follows from the event form applied to a Hahn decomposition. -/
theorem ofReal_tvDist_sq_div_two_le_klDiv {mα : MeasurableSpace α}
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (tvDist μ ν ^ 2 / 2) ≤ klDiv μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h := ofReal_two_mul_sq_measureReal_sub_le_klDiv (μ := μ) (ν := ν) hs.measurableSet.compl
  rw [hs.tvDist_eq, probReal_compl_eq_one_sub hs.measurableSet,
    probReal_compl_eq_one_sub (μ := ν) hs.measurableSet]
  rw [probReal_compl_eq_one_sub hs.measurableSet,
    probReal_compl_eq_one_sub (μ := ν) hs.measurableSet] at h
  convert h using 2
  ring

end Cslib.Probability
