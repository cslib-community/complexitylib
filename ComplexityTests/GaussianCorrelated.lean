/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import Complexity.Foundations.Probability.Gaussian.Correlated

/-! # Tests for correlated Gaussians and Gaussian noise stability

The halfspace stability `1 - (2 / π) arccos ρ` at `ρ = 1`, `0`, `1 / 2` and `-1`, Example 11.19
at `ρ = 0`, a concrete instance of Fact 11.7 in the plane, the degenerate pairs at `ρ = ±1`, the
stability of a constant, and a nonvacuity check of the uniqueness theorem for Definition 11.6. -/

namespace ComplexityTests.GaussianCorrelated

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

local notation "e" i => (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin 2))

/-- `arccos (1 / 2) = π / 3`. -/
theorem arccos_one_half : arccos (1 / 2) = π / 3 := by
  rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]

/-- The sign function is perfectly stable at `ρ = 1`. -/
example : gaussianNoiseStability 1 (fun z : Fin 1 → ℝ => if 0 < z 0 then (1 : ℝ) else -1) = 1 := by
  have h := gaussianNoiseStability_ite_pos_dotProduct (ι := Fin 1) (ρ := 1) (by norm_num)
    (a := Pi.single 0 1) (Pi.single_ne_zero_iff.2 one_ne_zero)
  simp only [single_dotProduct, one_mul, arccos_one, mul_zero, sub_zero] at h
  exact h

/-- At `ρ = 0` the halfspace stability is `(E h) ^ 2 = 0`. -/
example (a : Fin 3 → ℝ) (ha : a ≠ 0) :
    gaussianNoiseStability 0 (fun z => if 0 < a ⬝ᵥ z then (1 : ℝ) else -1) = 0 := by
  rw [gaussianNoiseStability_ite_pos_dotProduct (by norm_num) ha, arccos_zero]
  field_simp
  ring

/-- At `ρ = 1 / 2` the closed halfspace has stability `1 - (2 / π) (π / 3) = 1 / 3`. -/
example (a : Fin 3 → ℝ) (ha : a ≠ 0) :
    gaussianNoiseStability (1 / 2) (fun z => if 0 ≤ a ⬝ᵥ z then (1 : ℝ) else -1) = 1 / 3 := by
  rw [gaussianNoiseStability_ite_nonneg_dotProduct (by norm_num [abs_of_pos]) ha,
    arccos_one_half]
  field_simp
  ring

/-- At `ρ = -1` the halfspace stability is `-1`: the two points lie on opposite sides. -/
example (a : Fin 2 → ℝ) (ha : a ≠ 0) :
    gaussianNoiseStability (-1) (fun z => if 0 < a ⬝ᵥ z then (1 : ℝ) else -1) = -1 := by
  rw [gaussianNoiseStability_ite_pos_dotProduct (by norm_num) ha, arccos_neg_one]
  field_simp
  ring

/-- Example 11.19 at `ρ = 0`: two independent standard Gaussians are both nonpositive with
probability `1 / 4`. -/
example : gaussianNoiseStability 0 (fun z : Fin 2 → ℝ => (Iic (0 : ℝ)).indicator 1 (z 1)) =
    1 / 4 := by
  rw [gaussianNoiseStability_indicator_Iic_eval (by norm_num), arccos_zero]
  field_simp
  ring

/-- Fact 11.7 for the unit vectors `e₀` and `(e₀ + e₁) / √2` of the plane, at correlation
`1 / √2`. -/
example : (stdGaussian (EuclideanSpace ℝ (Fin 2))).map
      (fun x => (⟪e 0, x⟫, ⟪(√2)⁻¹ • ((e 0) + (e 1)), x⟫)) = correlatedGaussian (√2)⁻¹ := by
  have hn : ‖(e 0) + (e 1)‖ = √2 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    norm_num
  have h := stdGaussian_map_inner_prod_eq_correlatedGaussian (u := e 0)
    (v := (√2)⁻¹ • ((e 0) + (e 1))) (by simp)
    (by rw [norm_smul, hn, norm_inv, norm_of_nonneg (sqrt_nonneg 2),
      inv_mul_cancel₀ (by positivity)])
  rw [h, real_inner_smul_right, inner_add_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left]
  simp only [Fin.isValue, map_one, one_mul, PiLp.single_eq_same, ne_eq, zero_ne_one,
    not_false_eq_true, PiLp.single_eq_of_ne, add_zero, mul_one]

/-- At `ρ = 1` the pair is `(g, g)`. -/
example : correlatedGaussian 1 = (gaussianReal 0 1).map fun x => (x, x) := by
  rw [correlatedGaussian]
  simp only [one_pow, sub_self, sqrt_zero, zero_mul, add_zero, one_mul]
  rw [show (fun g : ℝ × ℝ => (g.1, g.1)) = (fun x : ℝ => (x, x)) ∘ Prod.fst from rfl,
    ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul]

/-- At `ρ = -1` the pair is `(g, -g)`. -/
example : correlatedGaussian (-1) = (gaussianReal 0 1).map fun x => (x, -x) := by
  rw [correlatedGaussian]
  simp only [even_two, Even.neg_pow, one_pow, sub_self, sqrt_zero, zero_mul, add_zero,
    neg_one_mul]
  rw [show (fun g : ℝ × ℝ => (g.1, -g.1)) = (fun x : ℝ => (x, -x)) ∘ Prod.fst from rfl,
    ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul]

/-- The noise stability of a constant is its square. -/
example (ρ c : ℝ) : gaussianNoiseStability ρ (fun _ : Fin 3 → ℝ => c) = c ^ 2 := by
  rw [gaussianNoiseStability, integral_const, probReal_univ, one_smul, sq]

/-- The uniqueness theorem recognizes `correlatedGaussian ρ` itself (a nonvacuity check). -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) : correlatedGaussian ρ = correlatedGaussian ρ :=
  eq_correlatedGaussian hρ
    (by rw [← integral_map (φ := Prod.fst) (f := fun x : ℝ => x) (by fun_prop) (by fun_prop),
      correlatedGaussian_map_fst, integral_id_gaussianReal])
    (by rw [← integral_map (φ := Prod.snd) (f := fun x : ℝ => x) (by fun_prop) (by fun_prop),
      correlatedGaussian_map_snd hρ, integral_id_gaussianReal])
    (by
      rw [← integral_map (φ := Prod.fst) (f := fun x : ℝ => x ^ 2) (by fun_prop)
        (by fun_prop), correlatedGaussian_map_fst]
      have := variance_fun_id_gaussianReal (μ := 0) (v := 1)
      rw [variance_of_integral_eq_zero (by fun_prop) integral_id_gaussianReal] at this
      exact_mod_cast this)
    (by
      rw [← integral_map (φ := Prod.snd) (f := fun x : ℝ => x ^ 2) (by fun_prop)
        (by fun_prop), correlatedGaussian_map_snd hρ]
      have := variance_fun_id_gaussianReal (μ := 0) (v := 1)
      rw [variance_of_integral_eq_zero (by fun_prop) integral_id_gaussianReal] at this
      exact_mod_cast this)
    (integral_correlatedGaussian_fst_mul_snd hρ)

end ComplexityTests.GaussianCorrelated
