/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import Complexity.Foundations.Probability.Gaussian.NoiseOperator

/-! # Tests for the Gaussian noise operator

The noise operator on coordinates and scaled linear functions, its value at `ρ = 1`, the noise
stabilities of a constant and of a coordinate through `Stab_ρ[f] = ⟨f, U_ρ f⟩`, an instance of
self-adjointness, almost-everywhere additivity on a sum of coordinates, preservation of the mean,
and instances of the `L²` and `L∞` contraction. -/

namespace ComplexityTests.GaussianNoiseOperator

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A coordinate of independent standard Gaussians is square integrable. -/
theorem memLp_two_eval {ι : Type*} [Fintype ι] (i : ι) :
    MemLp (fun x : ι → ℝ => x i) 2 (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ i)

/-- A coordinate of independent standard Gaussians is integrable. -/
theorem integrable_eval {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun x : ι → ℝ => x i) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  simpa using integrable_dotProduct_pi_gaussianReal (Pi.single i (1 : ℝ))

/-- The noise operator scales a coordinate by `ρ`. -/
theorem gaussianNoiseOp_eval {ι : Type*} [Fintype ι] (ρ : ℝ) (i : ι) (z : ι → ℝ) :
    gaussianNoiseOp ρ (fun x => x i) z = ρ * z i := by
  classical
  simpa using gaussianNoiseOp_dotProduct ρ (Pi.single i 1) z

/-- The noise operator scales a scaled linear function by `ρ`. -/
example (ρ : ℝ) (a z : Fin 3 → ℝ) :
    gaussianNoiseOp ρ (fun x => 2 * (a ⬝ᵥ x)) z = 2 * ρ * (a ⬝ᵥ z) := by
  rw [gaussianNoiseOp_const_mul, gaussianNoiseOp_dotProduct, mul_assoc]

/-- At `ρ = 0` a linear function averages to `0`. -/
example (a z : Fin 3 → ℝ) : gaussianNoiseOp 0 (fun x => a ⬝ᵥ x) z = 0 := by
  rw [gaussianNoiseOp_dotProduct, zero_mul]

/-- `U_1` is the identity. -/
example (f : (Fin 2 → ℝ) → ℝ) (z : Fin 2 → ℝ) : gaussianNoiseOp 1 f z = f z := by
  rw [gaussianNoiseOp_one]

/-- The noise stability of a constant `c` is `c ^ 2`, computed as `⟨c, U_ρ c⟩`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (c : ℝ) :
    gaussianNoiseStability ρ (fun _ : Fin 4 → ℝ => c) = c ^ 2 := by
  rw [gaussianNoiseStability_eq_integral_mul_gaussianNoiseOp hρ (memLp_const c)]
  simp only [gaussianNoiseOp_const, integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The noise stability of a coordinate is `ρ`, computed as `⟨f, U_ρ f⟩` with the linear case of
Fact 11.13. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    gaussianNoiseStability ρ (fun x : Fin 2 → ℝ => x 0) = ρ := by
  have hsq : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have h := variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 1) aemeasurable_id
      integral_id_gaussianReal
    simpa [variance_id_gaussianReal] using h.symm
  simp only [gaussianNoiseStability_eq_integral_mul_gaussianNoiseOp hρ (memLp_two_eval (0 : Fin 2)),
    gaussianNoiseOp_eval]
  have h := integral_comp_eval (μ := fun _ : Fin 2 => gaussianReal 0 1) (i := 0)
    (f := fun t => t * (ρ * t)) (by fun_prop)
  rw [h]
  simp only [mul_left_comm _ ρ, ← sq, integral_const_mul, hsq, mul_one]

/-- Self-adjointness for two coordinates: `⟨x₀, U_ρ x₁⟩ = ⟨U_ρ x₀, x₁⟩`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ∫ z, z 0 * gaussianNoiseOp ρ (fun x => x 1) z
        ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) =
      ∫ z, gaussianNoiseOp ρ (fun x => x 0) z * z 1
        ∂Measure.pi fun _ : Fin 2 => gaussianReal 0 1 :=
  integral_mul_gaussianNoiseOp_comm hρ (memLp_two_eval (0 : Fin 2)) (memLp_two_eval (1 : Fin 2))

/-- Almost-everywhere additivity: `U_ρ (x₀ + x₁) = ρ (z₀ + z₁)` almost everywhere. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    gaussianNoiseOp ρ (fun x : Fin 2 → ℝ => x 0 + x 1)
      =ᵐ[Measure.pi fun _ : Fin 2 => gaussianReal 0 1] fun z => ρ * (z 0 + z 1) := by
  filter_upwards [gaussianNoiseOp_add hρ (integrable_eval (0 : Fin 2))
    (integrable_eval (1 : Fin 2))] with z hz
  rw [hz, gaussianNoiseOp_eval, gaussianNoiseOp_eval]
  ring

/-- The noise operator preserves the mean of a linear function. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (a : Fin 3 → ℝ) :
    ∫ z, gaussianNoiseOp ρ (fun x => a ⬝ᵥ x) z ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 1) =
      ∫ z, a ⬝ᵥ z ∂Measure.pi fun _ : Fin 3 => gaussianReal 0 1 :=
  integral_gaussianNoiseOp hρ (integrable_dotProduct_pi_gaussianReal a)

/-- The noise operator does not increase the `L²` norm. -/
example (f : (Fin 2 → ℝ) → ℝ)
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)) :
    eLpNorm (gaussianNoiseOp (1 / 2) f) 2 (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) ≤
      eLpNorm f 2 (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
  eLpNorm_gaussianNoiseOp_le (by norm_num [abs_of_pos]) one_le_two hf

/-- The noise operator maps bounded functions to bounded functions. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (f : (Fin 2 → ℝ) → ℝ)
    (hf : MemLp f ∞ (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)) :
    MemLp (gaussianNoiseOp ρ f) ∞ (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
  hf.gaussianNoiseOp hρ le_top

end ComplexityTests.GaussianNoiseOperator
