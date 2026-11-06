/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# Confidence-dependent testing lower bounds

A test with both error probabilities at most `η` requires Kullback--Leibler
divergence at least `log (1 / (4 * η))`. The proof uses the variational
change-of-measure inequality, and also applies after any randomized Markov
kernel. Divergences use natural logarithms.

## Main results

* `log_inv_four_error_le_klDiv`: the two-error testing inequality.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace Cslib.Probability

private theorem mul_log_inv_le_half {η : ℝ} (hη : 0 < η) :
    η * Real.log (1 / η) ≤ 1 / 2 := by
  let r := Real.sqrt η
  have hr : 0 < r := Real.sqrt_pos.mpr hη
  have hr2 : r ^ 2 = η := Real.sq_sqrt hη.le
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * η by positivity)
  have heq : η * r⁻¹ = r := by rw [← hr2]; field_simp
  have hlogs : Real.log (1 / η) = -2 * Real.log r := by
    rw [one_div, Real.log_inv]
    dsimp only [r]
    rw [Real.log_sqrt hη.le]
    ring
  rw [hlogs]
  nlinarith [sq_nonneg (r - 1 / 2)]

/-- If an event accepts the first law with probability at least `1 - η` and
accepts the second with probability at most `η`, its KL divergence is at least
`log (1 / (4η))`. No absolute-continuity assumption is required. -/
theorem log_inv_four_error_le_klDiv {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {E : Set Ω} (hE : MeasurableSet E) {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1)
    (hP : 1 - η ≤ P.real E) (hQ : Q.real E ≤ η) :
    ENNReal.ofReal (Real.log (1 / (4 * η))) ≤ klDiv P Q := by
  by_cases hac : P ≪ Q
  swap
  · simp [klDiv_of_not_ac hac]
  by_cases hint : Integrable (llr P Q) P
  swap
  · simp [klDiv_of_not_integrable hint]
  rw [klDiv_of_ac_of_integrable hac hint]
  apply ENNReal.ofReal_le_ofReal
  simp only [probReal_univ, add_sub_cancel_right]
  let t := Real.log (1 / η)
  let I : Ω → ℝ := E.indicator (fun _ => 1)
  have hI : Measurable I := measurable_const.indicator hE
  have hIP : Integrable I P := (integrable_const 1).indicator hE
  have hIQ : Integrable I Q := (integrable_const 1).indicator hE
  have hmeanP : ∫ z, I z ∂P = P.real E := by
    simp only [I, integral_indicator_const _ hE, smul_eq_mul, mul_one]
  have hmeanQ : ∫ z, I z ∂Q = Q.real E := by
    simp only [I, integral_indicator_const _ hE, smul_eq_mul, mul_one]
  have ht : 0 ≤ t := Real.log_nonneg ((le_div_iff₀ hη).mpr (by linarith))
  have hexp : (fun z => Real.exp (t * I z)) =
      (fun z => 1 + (Real.exp t - 1) * I z) := by
    funext z
    by_cases hz : z ∈ E <;> simp [I, hz]
  have heint : Integrable (fun z => Real.exp (t * I z)) Q := by
    rw [hexp]
    exact (integrable_const 1).add (hIQ.const_mul _)
  have hZ : (∫ z, Real.exp (t * I z) ∂Q) ≤ 2 := by
    rw [hexp, integral_add (integrable_const _) (hIQ.const_mul _),
      integral_const_mul, hmeanQ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have he : Real.exp t = 1 / η := Real.exp_log (one_div_pos.mpr hη)
    rw [he]
    have hn : 0 ≤ 1 / η - 1 := by exact sub_nonneg.mpr ((le_div_iff₀ hη).mpr (by linarith))
    have := mul_le_mul_of_nonneg_left hQ hn
    have hc : (1 / η - 1) * η = 1 - η := by field_simp
    linarith
  have hgibbs : 0 ≤ ∫ z, llr P (Q.tilted (fun z => t * I z)) z ∂P := by
    have := isProbabilityMeasure_tilted heint
    have h := integral_llr_add_sub_measure_univ_nonneg
      (hac.trans (absolutelyContinuous_tilted heint))
      (integrable_llr_tilted_right hac (hIP.const_mul _) hint heint)
    simpa only [probReal_univ, add_sub_cancel_right] using h
  rw [integral_llr_tilted_right hac (hIP.const_mul _) heint hint,
    integral_const_mul, hmeanP] at hgibbs
  have hlogZ : Real.log (∫ z, Real.exp (t * I z) ∂Q) ≤ Real.log 2 :=
    Real.log_le_log (integral_exp_pos heint) hZ
  have hlow := mul_le_mul_of_nonneg_left hP ht
  have hhalf := mul_log_inv_le_half hη
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hidentity : Real.log (1 / (4 * η)) = t - 2 * Real.log 2 := by
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hη.ne']
    dsimp only [t]
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  rw [hidentity]
  dsimp only [t] at *
  nlinarith

/-- Every randomized estimator accurate at two separated targets requires
logarithmic KL divergence between its input-data laws. The estimator is an
arbitrary Markov kernel into the real numbers. -/
theorem estimation_separation_le_klDiv {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (auditor : Kernel Ω ℝ) [IsMarkovKernel auditor]
    {θplus θminus δ η : ℝ} (hη : 0 < η) (hηone : η ≤ 1)
    (hsep : 2 * δ ≤ |θplus - θminus|)
    (hplus : 1 - η ≤ (auditor ∘ₘ P).real {y | |y - θplus| < δ})
    (hminus : 1 - η ≤ (auditor ∘ₘ Q).real {y | |y - θminus| < δ}) :
    ENNReal.ofReal (Real.log (1 / (4 * η))) ≤ klDiv P Q := by
  have hE (θ : ℝ) : MeasurableSet {y : ℝ | |y - θ| < δ} := by
    apply measurableSet_lt _ measurable_const
    simpa only [Real.norm_eq_abs, id_eq] using (measurable_id.sub_const θ).norm
  have hdis : {y : ℝ | |y - θplus| < δ} ⊆ {y : ℝ | |y - θminus| < δ}ᶜ := by
    intro y hy hz
    have htri := abs_sub_le θplus y θminus
    rw [abs_sub_comm θplus y] at htri
    exact (not_lt.mpr hsep) (by
      change |y - θplus| < δ at hy
      change |y - θminus| < δ at hz
      linarith)
  have hQ : (auditor ∘ₘ Q).real {y | |y - θplus| < δ} ≤ η := by
    have h := measureReal_mono hdis (μ := auditor ∘ₘ Q)
    rw [probReal_compl_eq_one_sub (hE θminus)] at h
    linarith
  exact (log_inv_four_error_le_klDiv (auditor ∘ₘ P) (auditor ∘ₘ Q)
    (hE θplus) hη hηone hplus hQ).trans (klDiv_comp_right_le P Q auditor)

end Cslib.Probability
