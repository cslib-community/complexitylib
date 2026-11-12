/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import CslibFrontier.Foundations.Probability.Gaussian.Hermite
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import CslibFrontier.Foundations.RingTheory.Polynomial.Hermite

/-! # Tests for Hermite polynomials in Gaussian space

The Appell property and three-term recurrence at small degrees, Stein's lemma on `x ↦ x` (the
variance), `h_2 x = (x² - 1) / √2` with its eigenvalue `ρ²` and unit norm, orthogonality of `h_1`
and `h_3`, `E[x³ H_3] = 6`, Proposition 11.31 at `h_1` and `h_2`, and in two dimensions the
eigenvalue `ρ³` of `h_{(1, 2)}`, orthogonality of distinct multi-indices, the correlation
`E[h_α z h_α z'] = ρ ^ |α|` and the monomial case `h_S z = ∏ i ∈ S, zᵢ` recovering Fact 11.13. -/

namespace CslibFrontierTests.GaussianHermite

open MeasureTheory ProbabilityTheory Polynomial Real

/-- `(hermite 2)' = 2 hermite 1`. -/
example : derivative (hermite 2) = 2 * hermite 1 := by
  rw [derivative_hermite_succ]
  norm_num

/-- `hermite 3 = X hermite 2 - 2 hermite 1`. -/
example : hermite 3 = X * hermite 2 - 2 * hermite 1 := by
  rw [hermite_succ_succ]
  norm_num

/-- Stein's lemma on `p = X` gives the variance: `E[x²] = 1`. -/
example : ∫ x, x * x ∂gaussianReal 0 1 = 1 := by
  have h := integral_sub_mul_eval_gaussianReal (μ := 0) (v := 1) X
  simp only [sub_zero, eval_X, derivative_X, eval_one, integral_const, probReal_univ,
    smul_eq_mul, NNReal.coe_one, mul_one] at h
  exact h

/-- `U_ρ h_2 = ρ² h_2` in one dimension: `E_g[(y² - 1) / √2] = ρ² (x² - 1) / √2` for the noisy
point `y = ρ x + √(1 - ρ²) g`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (x : ℝ) :
    ∫ g, ((ρ * x + √(1 - ρ ^ 2) * g) ^ 2 - 1) / √2 ∂gaussianReal 0 1 =
      ρ ^ 2 * ((x ^ 2 - 1) / √2) := by
  simpa only [normalizedHermite_two] using integral_normalizedHermite_gaussianNoise hρ 2 x

/-- `‖h_2‖ = 1`: `E[(x² - 1)²] = 2`. -/
example : ∫ x, ((x ^ 2 - 1) / √2) ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := integral_normalizedHermite_mul_normalizedHermite 2 2
  rw [ite_eq_left rfl] at h
  simpa only [normalizedHermite_two, ← sq] using h

/-- `⟨h_1, h_3⟩ = 0`. -/
example : ∫ x, normalizedHermite 1 x * normalizedHermite 3 x ∂gaussianReal 0 1 = 0 := by
  rw [integral_normalizedHermite_mul_normalizedHermite]
  norm_num

/-- Integration by parts against `H_3`: `E[x³ H_3 x]` is the mean of the third derivative of
`x³`, which is `6`. -/
example : ∫ x, (X ^ 3 : ℝ[X]).eval x * aeval x (hermite 3) ∂gaussianReal 0 1 = 6 := by
  rw [integral_eval_mul_aeval_hermite]
  norm_num [Function.iterate_succ_apply, derivative_X_pow]

/-- Proposition 11.31 for `h_2`: `E[h_2 z h_2 z'] = ρ²` for `ρ`-correlated `(z, z')`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ∫ p, normalizedHermite 2 p.1 * normalizedHermite 2 p.2 ∂correlatedGaussian ρ = ρ ^ 2 := by
  rw [integral_correlatedGaussian_normalizedHermite hρ, ite_eq_left rfl]

/-- Proposition 11.31: `h_1` and `h_2` are uncorrelated under `ρ`-correlated `(z, z')`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ∫ p, normalizedHermite 1 p.1 * normalizedHermite 2 p.2 ∂correlatedGaussian ρ = 0 := by
  rw [integral_correlatedGaussian_normalizedHermite hρ]
  norm_num

/-- `⟨H_3, H_3⟩ = 3! = 6`. -/
example : ∫ x, aeval x (hermite 3) * aeval x (hermite 3) ∂gaussianReal 0 1 = 6 := by
  rw [integral_aeval_hermite_mul_aeval_hermite, ite_eq_left rfl]
  norm_num [Nat.factorial]

/-- In two dimensions, `U_ρ h_{(1, 2)} = ρ³ h_{(1, 2)}`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (z : Fin 2 → ℝ) :
    gaussianNoiseOp ρ (multiHermite ![1, 2]) z = ρ ^ 3 * multiHermite ![1, 2] z := by
  rw [gaussianNoiseOp_multiHermite hρ]
  norm_num [Fin.sum_univ_two]

/-- Distinct multi-indices are orthogonal: `⟨h_{(1, 0)}, h_{(0, 1)}⟩ = 0`. -/
example : ∫ z, multiHermite ![1, 0] z * multiHermite ![0, 1] z
    ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) = 0 := by
  rw [integral_multiHermite_mul_multiHermite, ite_eq_right]
  decide

/-- For `ρ`-correlated `(z, z')`, `E[h_{(1, 2)} z h_{(1, 2)} z'] = ρ³`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ∫ p, multiHermite ![1, 2] p.1 * multiHermite ![1, 2] p.2 ∂correlatedGaussianPi (Fin 2) ρ =
      ρ ^ 3 := by
  rw [integral_correlatedGaussianPi_multiHermite hρ, ite_eq_left rfl]
  norm_num [Fin.sum_univ_two]

/-- For an indicator multi-index the eigenvalue identity is Fact 11.13 on the monomial
`∏ i ∈ S, xᵢ`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (S : Finset (Fin 3)) (z : Fin 3 → ℝ) :
    gaussianNoiseOp ρ (fun x => ∏ i ∈ S, x i) z = ρ ^ S.card * ∏ i ∈ S, z i := by
  have h := gaussianNoiseOp_multiHermite hρ (fun i => if i ∈ S then 1 else 0) z
  simp only [multiHermite_indicator, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Nat.cast_id] at h
  convert h using 2
  exact funext fun x => (multiHermite_indicator S x).symm

end CslibFrontierTests.GaussianHermite
