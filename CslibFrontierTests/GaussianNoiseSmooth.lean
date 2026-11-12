/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import CslibFrontier.Foundations.Probability.Gaussian.NoiseSmooth

/-! # Tests for the smoothness of the Gaussian noise operator

`U_{1/2}` and `U_{-1/2}` of the discontinuous indicator of a halfspace are smooth, hence
differentiable and continuous at every point (Proposition 11.16). The hypothesis `|ρ| < 1` is
needed: `U_1` is the identity, and the indicator itself is not continuous. The kernel form of
`U_ρ` with `f = 1` shows that the Mehler kernel integrates to `1`, and `U_{1/2}` of the indicator
of a point, a `γ`-null set, vanishes at every point. The general lemmas are checked on the moment
generating function of a Gaussian and on the product of two Gaussian densities. -/

namespace CslibFrontierTests.GaussianNoiseSmooth

open MeasureTheory ProbabilityTheory Real
open scoped ContDiff

/-- The indicator of the halfspace `{x | x₀ ≤ 0}`. -/
noncomputable abbrev halfspace : (Fin 2 → ℝ) → ℝ := {x : Fin 2 → ℝ | x 0 ≤ 0}.indicator 1

/-- The halfspace indicator is integrable under the standard Gaussian measure. -/
theorem integrable_halfspace :
    Integrable halfspace (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
  (integrable_const 1).indicator (measurableSet_le (by fun_prop) measurable_const)

/-- `U_{1/2}` of the halfspace indicator is `C^∞`. -/
example : ContDiff ℝ ∞ (gaussianNoiseOp (1 / 2) halfspace) :=
  contDiff_gaussianNoiseOp (by norm_num [abs_of_pos]) integrable_halfspace

/-- Negative correlations smooth too: `U_{-1/2}` of the halfspace indicator is differentiable at
the origin, where the indicator jumps. -/
example : DifferentiableAt ℝ (gaussianNoiseOp (-1 / 2) halfspace) 0 :=
  ((contDiff_gaussianNoiseOp (by norm_num [abs_of_neg]) integrable_halfspace).differentiable
    (by simp)).differentiableAt

/-- `U_{1/2}` of the halfspace indicator is continuous. -/
example : Continuous (gaussianNoiseOp (1 / 2) halfspace) :=
  (contDiff_gaussianNoiseOp (by norm_num [abs_of_pos]) integrable_halfspace).continuous

/-- The hypothesis `|ρ| < 1` is needed: `U_1` is the identity and the halfspace indicator is not
continuous, as `{x | x₀ ≤ 0}` would otherwise be clopen in the connected space `ℝ²`. -/
example : ¬ ContDiff ℝ ∞ (gaussianNoiseOp 1 halfspace) := by
  intro h
  rw [gaussianNoiseOp_one] at h
  have hopen : IsOpen {x : Fin 2 → ℝ | x 0 ≤ 0} := by
    have : {x : Fin 2 → ℝ | x 0 ≤ 0} = halfspace ⁻¹' Set.Ioi (1 / 2) := by
      ext x
      by_cases hx : x 0 ≤ 0 <;> norm_num [halfspace, Set.indicator, hx]
    rw [this]
    exact isOpen_Ioi.preimage h.continuous
  rcases isClopen_iff.1 ⟨isClosed_le (by fun_prop) continuous_const, hopen⟩ with h0 | h1
  · exact (Set.eq_empty_iff_forall_notMem.1 h0) 0 (by simp)
  · have : (fun _ => 1 : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | x 0 ≤ 0} := h1 ▸ Set.mem_univ _
    norm_num at this

/-- The kernel form with `f = 1`: the Mehler kernel, the density of the noisy point, integrates
to `1`. -/
example (z : Fin 2 → ℝ) :
    ∫ y, (∏ i, gaussianPDFReal ((1 / 2) * z i) (1 - (1 / 2 : ℝ) ^ 2).toNNReal (y i) /
      gaussianPDFReal 0 1 (y i)) ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) = 1 := by
  have h := gaussianNoiseOp_eq_integral_prod_div_mul (ρ := 1 / 2) (by norm_num [abs_of_pos])
    (f := fun _ => 1) aestronglyMeasurable_const z
  simpa using h.symm

/-- For `|ρ| < 1`, `U_ρ f` depends only on the `γ`-class of `f` at every point: `U_{1/2}` of the
indicator of the origin, which is `0` off a `γ`-null set, is `0` everywhere. -/
example : gaussianNoiseOp (1 / 2) (({0} : Set (Fin 2 → ℝ)).indicator 1) = 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [gaussianNoiseOp_congr_ae_of_abs_lt_one (f' := 0) (by norm_num [abs_of_pos])]
  · funext z
    simp [gaussianNoiseOp]
  · refine ae_iff.2 (measure_mono_null (fun x hx => ?_) (measure_singleton 0))
    by_contra h
    exact hx (Set.indicator_of_notMem h _)

/-- `contDiff_integral_exp_smul`: the moment generating function `t ↦ E[exp (t X)]` of a standard
Gaussian `X` is `C^∞`. -/
example : ContDiff ℝ ∞ fun t : ℝ => ∫ x, rexp (t * x) ∂gaussianReal 0 1 := by
  have h := contDiff_integral_exp_smul (μ := gaussianReal 0 1)
    (φ := fun x : ℝ => x • ContinuousLinearMap.id ℝ ℝ) (g := fun _ => (1 : ℝ))
    (continuous_id.smul continuous_const).aestronglyMeasurable aestronglyMeasurable_const
    fun c => by
      simpa [norm_smul] using integrable_exp_mul_abs (X := id)
        (integrable_exp_mul_gaussianReal c) (integrable_exp_mul_gaussianReal (-c))
  simpa [mul_comm] using h

/-- `lintegral_fintype_prod_eq_prod`: the product of two standard Gaussian densities integrates to
`1` against Lebesgue measure on `ℝ²`. -/
example : ∫⁻ x : Fin 2 → ℝ, ∏ i, ENNReal.ofReal (gaussianPDFReal 0 1 (x i))
    ∂Measure.pi (fun _ => volume) = 1 := by
  rw [lintegral_fintype_prod_eq_prod fun _ => (measurable_gaussianPDFReal 0 1).ennreal_ofReal]
  simp [lintegral_gaussianPDFReal_eq_one 0 one_ne_zero]

/-- `Measure.pi_withDensity`: the standard Gaussian measure on `ℝ²` has the product density with
respect to Lebesgue measure. -/
example : Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) =
    (Measure.pi fun _ => volume).withDensity fun x => ∏ i, gaussianPDF 0 1 (x i) := by
  have : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← gaussianReal_of_var_ne_zero 0 one_ne_zero]
    infer_instance
  simp_rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact Measure.pi_withDensity fun _ => measurable_gaussianPDF 0 1

end CslibFrontierTests.GaussianNoiseSmooth
