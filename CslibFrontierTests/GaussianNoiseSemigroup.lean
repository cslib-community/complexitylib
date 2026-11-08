/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import CslibFrontier.Foundations.Probability.Gaussian.NoiseSemigroup

/-! # Tests for the Gaussian noise semigroup

The semigroup law on a monomial, evaluated with Fact 11.13 (`U_{1/2} U_{1/2} (x₀ x₁)` is
`z₀ z₁ / 16`, matching the direct computation in `CslibFrontierTests/GaussianNoiseOperator.lean`),
its degenerate cases `ρ₂ = 0` and `ρ₁ = -1`, and `L¹` continuity at
`ρ = 1` for a coordinate and for the discontinuous indicator of a halfspace. -/

namespace ComplexityTests.GaussianNoiseSemigroup

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- A monomial in independent standard Gaussians is integrable. -/
theorem integrable_prod {ι : Type*} [Fintype ι] :
    Integrable (fun x : ι → ℝ => ∏ i, x i) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  Integrable.finset_prod_pi (f := fun _ t => t) _ fun _ _ => IsGaussian.integrable_id

/-- The semigroup law at `ρ₁ = ρ₂ = 1/2` on `x₀ x₁`, evaluated with Fact 11.13: `z₀ z₁ / 16`. -/
example : gaussianNoiseOp (1 / 2) (gaussianNoiseOp (1 / 2) fun x : Fin 2 → ℝ => ∏ i, x i)
    =ᵐ[Measure.pi fun _ : Fin 2 => gaussianReal 0 1] fun z => 1 / 16 * ∏ i, z i := by
  have h : |(1 / 2 : ℝ)| ≤ 1 := by norm_num [abs_of_pos]
  filter_upwards [gaussianNoiseOp_gaussianNoiseOp h h integrable_prod] with z hz
  rw [hz, gaussianNoiseOp_prod, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- With `ρ₂ = 0` the semigroup law says `U_ρ` fixes the constant `E[f]`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : (Fin 3 → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi fun _ : Fin 3 => gaussianReal 0 1)) :
    gaussianNoiseOp ρ (gaussianNoiseOp 0 f)
      =ᵐ[Measure.pi fun _ : Fin 3 => gaussianReal 0 1] gaussianNoiseOp 0 f := by
  have h := gaussianNoiseOp_gaussianNoiseOp (ρ₂ := 0) hρ (by norm_num) hf
  rwa [mul_zero] at h

/-- With `ρ₁ = -1` there is no noise: `U_{-1}` reflects, and the law still holds. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : (Fin 3 → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi fun _ : Fin 3 => gaussianReal 0 1)) :
    gaussianNoiseOp (-1) (gaussianNoiseOp ρ f)
      =ᵐ[Measure.pi fun _ : Fin 3 => gaussianReal 0 1] gaussianNoiseOp (-ρ) f := by
  have h := gaussianNoiseOp_gaussianNoiseOp (ρ₁ := -1) (by norm_num) hρ hf
  rwa [neg_one_mul] at h

/-- `U_ρ x₀ → x₀` in `L¹` as `ρ → 1⁻`. -/
example : Tendsto (fun ρ => eLpNorm (gaussianNoiseOp ρ (fun x : Fin 2 → ℝ => x 0) - fun x => x 0)
    1 (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)) (𝓝[<] 1) (𝓝 0) :=
  tendsto_eLpNorm_gaussianNoiseOp_sub (memLp_one_iff_integrable.1
    ((memLp_id_gaussianReal' 1 ENNReal.one_ne_top).comp_measurePreserving
      (measurePreserving_eval _ 0)))

/-- `L¹` continuity at `ρ = 1` also holds for the discontinuous indicator of a halfspace. -/
example : Tendsto (fun ρ =>
      eLpNorm (gaussianNoiseOp ρ ({x : Fin 2 → ℝ | x 0 ≤ 0}.indicator 1) -
        {x : Fin 2 → ℝ | x 0 ≤ 0}.indicator 1) 1 (Measure.pi fun _ : Fin 2 => gaussianReal 0 1))
    (𝓝[<] 1) (𝓝 0) :=
  tendsto_eLpNorm_gaussianNoiseOp_sub
    ((integrable_const 1).indicator (measurableSet_le (by fun_prop) measurable_const))

end ComplexityTests.GaussianNoiseSemigroup
