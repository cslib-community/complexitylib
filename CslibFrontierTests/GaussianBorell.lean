/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Foundations.Probability.Gaussian.Borell
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import CslibFrontier.Foundations.Probability.Gaussian.Real

/-! # Tests for the reductions of Borell's Isoperimetric Theorem

The full reduction instantiated in dimension `3` from a hypothetical one-dimensional
Two-Function Borell inequality, the converse direction through one more coordinate, and
non-vacuity checks: the predicate holds outright at `ρ = 0` and `ρ = 1`, so the reductions give
unconditional two-set inequalities there, and parallel halfspaces attain the two-set bound. -/

public section

namespace CslibFrontierTests.GaussianBorell

open MeasureTheory ProbabilityTheory Real Set

/-- The standard Gaussian measure on `ℝ^3`. -/
noncomputable abbrev γ3 : Measure (Fin 3 → ℝ) := Measure.pi fun _ : Fin 3 => gaussianReal 0 1

section Hypothetical

variable {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (h1 : TwoFunctionBorellInequality ρ (Fin 1))
include hρ0 hρ1 h1

-- The Two-Set Borell inequality in dimension `3`.
example (A B : Set (Fin 3 → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (correlatedGaussianPi (Fin 3) ρ).real (A ×ˢ B) ≤ gaussianQuadrant ρ (γ3.real A) (γ3.real B) :=
  twoSetBorellInequality_iff.1
    (h1.twoSetBorellInequality_of_fin_one (abs_le.2 ⟨by linarith, hρ1⟩) (Fin 3)) A B hA hB

-- Borell's Isoperimetric Theorem in dimension `3`, for `[0, 1]`-valued functions.
example (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) (hf01 : ∀ z, f z ∈ Icc 0 1) :
    gaussianNoiseStability ρ f ≤ gaussianQuadrant ρ (∫ z, f z ∂γ3) (∫ z, f z ∂γ3) :=
  h1.gaussianNoiseStability_le_of_fin_one hρ0 hρ1 hf hf01

-- Borell's Isoperimetric Theorem for sets of volume `1 / 2` in dimension `3`.
example (A : Set (Fin 3 → ℝ)) (hA : MeasurableSet A) (hvol : γ3.real A = 1 / 2) :
    gaussianNoiseStability ρ (A.indicator 1) ≤ 1 / 2 - arccos ρ / (2 * π) := by
  have h3 := h1.of_fin_one (abs_le.2 ⟨by linarith, hρ1⟩) (Fin 3)
  refine h3.gaussianNoiseStability_le_of_integral_eq_half hρ0 hρ1 (measurable_one.indicator hA)
    (fun z => ?_) (by rw [integral_indicator_one hA, hvol])
  by_cases hz : z ∈ A <;> simp [hz]

end Hypothetical

-- The tensorized inequality through its unfolding, as `module` clients see it: in dimension
-- `3`, for `f z = Φ(z₀)` and `g z = 1 / 2`.
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (h1 : TwoFunctionBorellInequality ρ (Fin 1)) :
    ∫ p, gaussianQuadrant ρ (cdf (gaussianReal 0 1) (p.1 0)) (1 / 2)
        ∂correlatedGaussianPi (Fin 3) ρ ≤
      gaussianQuadrant ρ (∫ z, cdf (gaussianReal 0 1) (z 0) ∂γ3) (1 / 2) := by
  have h := twoFunctionBorellInequality_iff.1 (h1.of_fin_one hρ (Fin 3))
    (fun z => cdf (gaussianReal 0 1) (z 0)) (fun _ => 1 / 2)
    ((measurable_cdf _).comp (measurable_pi_apply 0)) measurable_const
    (fun z => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩) fun _ => ⟨by norm_num, by norm_num⟩
  rwa [integral_const, probReal_univ, one_smul] at h

-- Exercise 11.26 (b), unfolded: the Two-Set inequality in dimension `3 = 2 + 1` bounds
-- `E[Λ_ρ(f z, g z')]` in dimension `2`.
example {ρ : ℝ} (h : TwoSetBorellInequality ρ (Fin 2 ⊕ Unit)) (f g : (Fin 2 → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf01 : ∀ z, f z ∈ Icc 0 1)
    (hg01 : ∀ z, g z ∈ Icc 0 1) :
    ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussianPi (Fin 2) ρ ≤
      gaussianQuadrant ρ (∫ z, f z ∂Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
        (∫ z, g z ∂Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
  twoFunctionBorellInequality_iff.1 h.twoFunctionBorellInequality f g hf hg hf01 hg01

-- Non-vacuity: the predicate holds at `ρ = 0` and `ρ = 1`, so the Two-Set inequality holds
-- unconditionally there; at `ρ = 0` it is `P[z ∈ A] P[z' ∈ B] ≤ Λ_0(vol A, vol B)`.
example (A B : Set (Fin 3 → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (correlatedGaussianPi (Fin 3) 0).real (A ×ˢ B) ≤
      gaussianQuadrant 0 (γ3.real A) (γ3.real B) :=
  twoSetBorellInequality_iff.1
    ((twoFunctionBorellInequality_zero _).twoSetBorellInequality (by norm_num)) A B hA hB

example (A B : Set (Fin 3 → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (correlatedGaussianPi (Fin 3) 1).real (A ×ˢ B) ≤
      gaussianQuadrant 1 (γ3.real A) (γ3.real B) :=
  twoSetBorellInequality_iff.1
    ((twoFunctionBorellInequality_one _).twoSetBorellInequality (by norm_num)) A B hA hB

-- The equality cases: parallel halfspaces `z₀ + z₁ ≤ 1` and `z₀ + z₁ ≤ -2` attain the
-- Two-Set bound, so it cannot be improved.
example (ρ : ℝ) :
    (correlatedGaussianPi (Fin 3) ρ).real
        ({z | ![1, 1, 0] ⬝ᵥ z ≤ 1} ×ˢ {z | ![1, 1, 0] ⬝ᵥ z ≤ -2}) =
      gaussianQuadrant ρ (γ3.real {z | ![1, 1, 0] ⬝ᵥ z ≤ 1})
        (γ3.real {z | ![1, 1, 0] ⬝ᵥ z ≤ -2}) :=
  measureReal_correlatedGaussianPi_setOf_dotProduct_le_prod ρ (by simp) 1 (-2)

-- The Two-Set inequality, through its unfolding, at `ρ = 1`: identical Gaussians land in two
-- sets with probability at most the smaller volume.
example (A B : Set (Fin 3 → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (correlatedGaussianPi (Fin 3) 1).real (A ×ˢ B) ≤ min (γ3.real A) (γ3.real B) := by
  have h := twoSetBorellInequality_iff.1
    ((twoFunctionBorellInequality_one (Fin 3)).twoSetBorellInequality (by norm_num)) A B hA hB
  rwa [gaussianQuadrant_one measureReal_nonneg measureReal_le_one measureReal_nonneg] at h

-- The other equality case: `f z = Φ(z₀ - 1)` and `g z = Φ(z₀ + 3)`.
example (ρ : ℝ) :
    ∫ p, gaussianQuadrant ρ (cdf (gaussianReal 0 1) (![1, 0, 0] ⬝ᵥ p.1 + -1))
        (cdf (gaussianReal 0 1) (![1, 0, 0] ⬝ᵥ p.2 + 3)) ∂correlatedGaussianPi (Fin 3) ρ =
      gaussianQuadrant ρ (∫ z, cdf (gaussianReal 0 1) (![1, 0, 0] ⬝ᵥ z + -1) ∂γ3)
        (∫ z, cdf (gaussianReal 0 1) (![1, 0, 0] ⬝ᵥ z + 3) ∂γ3) :=
  integral_gaussianQuadrant_cdf_dotProduct_add ρ _ _ _

/-- `arccos (1 / 2) = π / 3`. -/
theorem arccos_one_half : arccos (1 / 2) = π / 3 := by
  rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]

/-- The predicate fails for negative `ρ`: at `ρ = -1 / 2` on the line, the half-lines
`A = {z ≤ 0}` and `B = {z ≥ 0}` have `P[z ∈ A, z' ∈ B] = 1 / 3`, more than
`Λ_ρ(1 / 2, 1 / 2) = 1 / 6`. -/
theorem not_twoSetBorellInequality_neg_half : ¬ TwoSetBorellInequality (-(1 / 2)) (Fin 1) := by
  intro h
  set A : Set (Fin 1 → ℝ) := {z | z 0 ≤ 0}
  set B : Set (Fin 1 → ℝ) := {z | 0 ≤ z 0}
  have hA : MeasurableSet A := measurableSet_le (measurable_pi_apply 0) measurable_const
  have hB : MeasurableSet B := measurableSet_le measurable_const (measurable_pi_apply 0)
  have he : Measurable fun z : Fin 1 → ℝ => z 0 := measurable_pi_apply 0
  have hΦ : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
    rw [cdf_gaussianReal_zero_zero one_ne_zero, one_div]
  have hvolA : (Measure.pi fun _ : Fin 1 => gaussianReal 0 1).real A = 1 / 2 := by
    rw [show A = (fun z : Fin 1 → ℝ => z 0) ⁻¹' Iic 0 from rfl,
      ← map_measureReal_apply he measurableSet_Iic, (measurePreserving_eval _ 0).map_eq,
      ← cdf_eq_real, hΦ]
  have hvolB : (Measure.pi fun _ : Fin 1 => gaussianReal 0 1).real B = 1 / 2 := by
    have hneg : (fun x : ℝ => -x) ⁻¹' Ici 0 = Iic 0 := by
      ext x
      simp only [mem_preimage, mem_Ici, mem_Iic, Left.nonneg_neg_iff]
    rw [show B = (fun z : Fin 1 → ℝ => z 0) ⁻¹' Ici 0 from rfl,
      ← map_measureReal_apply he measurableSet_Ici, (measurePreserving_eval _ 0).map_eq,
      ← gaussianReal_zero_map_neg, map_measureReal_apply measurable_neg measurableSet_Ici, hneg,
      ← cdf_eq_real, hΦ]
  have hQ : MeasurableSet {q : ℝ × ℝ | q.1 ≤ 0 ∧ 0 ≤ q.2} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  have hneg : (fun p : ℝ × ℝ => (p.1, -p.2)) ⁻¹' {q : ℝ × ℝ | q.1 ≤ 0 ∧ 0 ≤ q.2} =
      {p | p.1 ≤ 0 ∧ p.2 ≤ 0} := by
    ext p
    simp only [mem_preimage, mem_ofPred_eq, Left.nonneg_neg_iff]
  have hP : (correlatedGaussianPi (Fin 1) (-(1 / 2))).real (A ×ˢ B) = 1 / 3 := by
    rw [show A ×ˢ B = (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (p.1 0, p.2 0)) ⁻¹'
        {q : ℝ × ℝ | q.1 ≤ 0 ∧ 0 ≤ q.2} from rfl,
      ← map_measureReal_apply (by fun_prop) hQ, correlatedGaussianPi_map_eval,
      ← correlatedGaussian_map_neg_snd, map_measureReal_apply (by fun_prop) hQ, hneg,
      ← gaussianQuadrant_cdf_cdf, hΦ, gaussianQuadrant_half_half (by norm_num [abs_of_pos]),
      arccos_one_half]
    field_simp
    ring
  have hΛ : gaussianQuadrant (-(1 / 2)) (1 / 2) (1 / 2) = 1 / 6 := by
    rw [gaussianQuadrant_half_half (by norm_num [abs_of_pos]), arccos_neg, arccos_one_half]
    field_simp
    ring
  have := twoSetBorellInequality_iff.1 h A B hA hB
  rw [hP, hvolA, hvolB, hΛ] at this
  norm_num at this

end CslibFrontierTests.GaussianBorell
