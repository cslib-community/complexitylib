/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.NoiseOperator

/-! # Tests for the Gaussian noise operator

The noise operator on coordinates and scaled linear functions, its value at `ρ = 1`, the noise
stabilities of a constant and of a coordinate through `Stab_ρ[f] = ⟨f, U_ρ f⟩`, an instance of
self-adjointness, almost-everywhere additivity on a sum of coordinates, preservation of the mean,
instances of the `L²` and `L∞` contraction, and Fact 11.13 on monomials and multilinear
polynomials, including the form `U_ρ f z = f (ρ z)` and a composite `U_{1/2} U_{1/2}`. -/

namespace CslibFrontierTests.GaussianNoiseOperator

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
  simpa using gaussianNoiseOp_prod ρ {i} z

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

/-- Fact 11.13 on a monomial: `U_ρ (x₀ x₂) = ρ² z₀ z₂`. -/
example (ρ : ℝ) (z : Fin 3 → ℝ) :
    gaussianNoiseOp ρ (fun x => x 0 * x 2) z = ρ ^ 2 * (z 0 * z 2) := by
  have h := gaussianNoiseOp_prod ρ {0, 2} z
  simp only [Finset.mem_singleton, Fin.reduceEq, not_false_eq_true, Finset.prod_insert,
    Finset.prod_singleton, Finset.card_insert_of_notMem, Finset.card_singleton,
    Nat.reduceAdd] at h
  exact h

/-- `U_0` of a non-constant monomial is its mean `0`. -/
example (z : Fin 2 → ℝ) : gaussianNoiseOp 0 (fun x => ∏ i, x i) z = 0 := by
  rw [gaussianNoiseOp_prod, Finset.card_univ, Fintype.card_fin, zero_pow two_ne_zero, zero_mul]

/-- Fact 11.13 in the book's form: for a multilinear polynomial `f`, `U_ρ f z = f (ρ z)`. -/
example {ι : Type*} [Fintype ι] (ρ : ℝ) (c : Finset ι → ℝ) (z : ι → ℝ) :
    gaussianNoiseOp ρ (fun x => ∑ S, c S * ∏ i ∈ S, x i) z =
      (fun x => ∑ S, c S * ∏ i ∈ S, x i) (ρ • z) := by
  rw [gaussianNoiseOp_sum_mul_prod]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, mul_assoc]

/-- Fact 11.13 on a concrete polynomial: `U_ρ (3 + 2 x₀ x₁ - x₂) = 3 + 2 ρ² z₀ z₁ - ρ z₂`. -/
example (ρ : ℝ) (z : Fin 3 → ℝ) :
    gaussianNoiseOp ρ (fun x => 3 + 2 * (x 0 * x 1) - x 2) z =
      3 + 2 * ρ ^ 2 * (z 0 * z 1) - ρ * z 2 := by
  have h := gaussianNoiseOp_sum_mul_prod ρ Finset.univ ![3, 2, -1]
    ![∅, {0, 1}, {2}] z
  simp only [Fin.sum_univ_three, Matrix.cons_val, Finset.prod_empty, Finset.card_empty,
    Finset.mem_singleton, Fin.reduceEq, not_false_eq_true, Finset.prod_insert,
    Finset.prod_singleton, Finset.card_insert_of_notMem, Finset.card_singleton,
    Nat.reduceAdd] at h
  convert h using 1
  · congr 1 with x : 1
    ring
  · ring

/-- Fact 11.13 applied twice: `U_{1/2} U_{1/2} (x₀ x₁) = z₀ z₁ / 16` everywhere, the value the
semigroup law gives almost everywhere (`CslibFrontierTests/GaussianNoiseSemigroup.lean`). -/
example (z : Fin 2 → ℝ) :
    gaussianNoiseOp (1 / 2) (gaussianNoiseOp (1 / 2) fun x : Fin 2 → ℝ => ∏ i, x i) z =
      1 / 16 * ∏ i, z i := by
  have h : gaussianNoiseOp (1 / 2) (fun x : Fin 2 → ℝ => ∏ i, x i) =
      fun x => 1 / 4 * ∏ i, x i := by
    funext x
    rw [gaussianNoiseOp_prod, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [h, gaussianNoiseOp_const_mul, gaussianNoiseOp_prod, Finset.card_univ, Fintype.card_fin]
  ring

end CslibFrontierTests.GaussianNoiseOperator
