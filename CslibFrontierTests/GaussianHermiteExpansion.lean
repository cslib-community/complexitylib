/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import CslibFrontier.Foundations.Probability.Gaussian.HermiteExpansion
import CslibFrontier.Foundations.Probability.Gaussian.PolynomialDense

/-! # Tests for Hermite expansions in Gaussian space

Polynomial approximation of a non-polynomial function (Theorem 11.22) and `L²` membership of a
concrete polynomial; the multivariate and one-dimensional Hermite bases on basis vectors;
Parseval's formula computing `E[(z₀ z₁)²] = 1` and `E[x⁴] = 3`, and Plancherel's formula computing
`E[x² h₂] = √2`; the coefficients of a multilinear polynomial (Remark 11.35); the mean
`f̂(0) = 1 / 2` of a halfspace indicator, from Sheppard's formula at `ρ = 1`; the degree-ordered
expansion of a halfspace indicator and the exact degree-`k` truncation of `z₀ z₁`; uniqueness of
the expansion of `U_ρ f`, Proposition 11.37 on `h_α`, and the noise stability
`Stab_ρ[h_α] = ρ ^ |α|` recomputed from the Hermite expansion, agreeing with Proposition 11.33. -/

namespace CslibFrontierTests.GaussianHermiteExpansion

open MeasureTheory ProbabilityTheory

/-- The indicator of the halfspace `0 < z 0` lies in `L²(γ²)`. -/
theorem memLp_halfspace :
    MemLp (fun z : Fin 2 → ℝ => if 0 < z 0 then (1 : ℝ) else 0) 2
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
  refine memLp_of_bounded (a := 0) (b := 1) (ae_of_all _ fun z => ?_) ?_ 2
  · split_ifs <;> norm_num
  · exact (Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply 0))
      measurable_const measurable_const).aestronglyMeasurable

/-- Theorem 11.22 for `p = 2` on a non-polynomial function: the indicator of the halfspace
`0 < z 0` is within `1 / 10` of a polynomial in `L²(γ²)`. -/
example : ∃ p : MvPolynomial (Fin 2) ℝ,
    eLpNorm ((fun z : Fin 2 → ℝ => if 0 < z 0 then (1 : ℝ) else 0) -
      fun z => MvPolynomial.eval z p) 2 (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) <
      1 / 10 :=
  exists_eLpNorm_sub_eval_lt_pi_gaussianReal memLp_halfspace (by norm_num)

/-- A concrete polynomial lies in `L²(γ²)`. -/
example : MemLp (fun z : Fin 2 → ℝ => z 0 ^ 3 * z 1 - 2) 2
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
  convert memLp_eval_pi_gaussianReal (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 -
    MvPolynomial.C 2 : MvPolynomial (Fin 2) ℝ) using 2 with z
  simp

/-- The Hermite basis has coordinates `δ_{αβ}` at the basis vector `h_α`. -/
example (α β : Fin 2 → ℕ) :
    (hermiteBasis (Fin 2)).repr (hermiteBasis (Fin 2) α) β = if α = β then 1 else 0 := by
  rw [hermiteBasis_apply, hermiteBasis_repr, hermiteCoeff_multiHermite]

/-- In the one-dimensional Hermite basis (Proposition 11.30), `x ↦ x = h_1` has coordinates
`δ_{1j}`. -/
example : normalizedHermiteBasis.repr ((memLp_normalizedHermite 1).toLp (normalizedHermite 1)) =
    lp.single 2 1 1 := by
  rw [← normalizedHermiteBasis_apply, HilbertBasis.repr_self]

/-- `z₀ z₁` is the Hermite polynomial `h_{(1, 1)}`. -/
theorem mul_eq_multiHermite (z : Fin 2 → ℝ) : z 0 * z 1 = multiHermite (fun _ => 1) z := by
  have h := multiHermite_indicator Finset.univ z
  simp only [Finset.mem_univ, ite_true, Fin.prod_univ_two] at h
  exact h.symm

/-- **Parseval's formula** computes `E[(z₀ z₁)²] = 1`: the only nonzero Hermite coefficient of
`z₀ z₁` is `1`, at the multi-index `(1, 1)`. -/
example : ∫ z, (z 0 * z 1) ^ 2 ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) = 1 := by
  simp only [mul_eq_multiHermite]
  rw [integral_sq_eq_tsum_hermiteCoeff_sq (memLp_multiHermite _)]
  simp only [hermiteCoeff_multiHermite, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  exact tsum_ite_eq' _ _

/-- `x ^ 2 = h_0 + √2 h_2` in one coordinate. -/
theorem sq_eq_multiHermite (z : Fin 1 → ℝ) :
    z 0 ^ 2 = multiHermite 0 z + √2 * multiHermite (fun _ => 2) z := by
  simp only [multiHermite_def, Fin.prod_univ_one, Pi.zero_apply, normalizedHermite_zero,
    normalizedHermite_two]
  field_simp
  ring

/-- `x ^ 2` lies in `L²(γ¹)`, as a polynomial. -/
theorem memLp_sq :
    MemLp (fun z : Fin 1 → ℝ => z 0 ^ 2) 2 (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) := by
  convert memLp_eval_pi_gaussianReal (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) ℝ) using 2 with z
  simp

/-- The Hermite coefficients of `x ^ 2` are `1` at `0` and `√2` at `2`, by linearity. -/
theorem hermiteCoeff_sq (β : Fin 1 → ℕ) : hermiteCoeff (fun z : Fin 1 → ℝ => z 0 ^ 2) β =
    (if 0 = β then 1 else 0) + √2 * if (fun _ => 2) = β then 1 else 0 := by
  simp only [sq_eq_multiHermite]
  rw [hermiteCoeff_add (memLp_multiHermite 0) ((memLp_multiHermite _).const_mul _),
    hermiteCoeff_const_mul, hermiteCoeff_multiHermite, hermiteCoeff_multiHermite]

/-- **Parseval's formula** on a function outside the basis: `E[x ^ 4] = 1 + 2 = 3`. -/
example : ∫ z, (z 0 ^ 2) ^ 2 ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) = 3 := by
  have h02 : (0 : Fin 1 → ℕ) ≠ fun _ => 2 := fun h => by simpa using congrFun h 0
  rw [integral_sq_eq_tsum_hermiteCoeff_sq memLp_sq, tsum_eq_sum (s := {0, fun _ => 2})]
  · rw [Finset.sum_pair h02]
    simp only [hermiteCoeff_sq, ite_true, h02, h02.symm, ite_false]
    norm_num
  · intro β hβ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hβ
    simp [hermiteCoeff_sq, Ne.symm hβ.1, Ne.symm hβ.2]

/-- **Plancherel's formula** for two different functions: `E[x² h₂] = √2`, the coefficient of
`h_2` in `x²`. -/
example : ∫ z, z 0 ^ 2 * multiHermite (fun _ => 2) z
    ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) = √2 := by
  have h := hasSum_hermiteCoeff_mul_hermiteCoeff memLp_sq (memLp_multiHermite fun _ => 2)
  simp only [hermiteCoeff_multiHermite, mul_ite, mul_one, mul_zero] at h
  refine h.unique ?_
  convert hasSum_ite_eq (fun _ : Fin 1 => 2) (√2) using 2 with β
  by_cases hβ : (fun _ : Fin 1 => 2) = β
  · subst hβ
    have h02 : (0 : Fin 1 → ℕ) ≠ fun _ => 2 := fun h => by simpa using congrFun h 0
    simp [hermiteCoeff_sq, h02]
  · simp [hβ, Ne.symm hβ]

/-- **The Hermite expansion of a multilinear polynomial** (Remark 11.35): the coefficient of
`h_{\{2\}}` in `z₀ z₁ + 3 z₂` is `3`. -/
example : hermiteCoeff (fun z : Fin 3 → ℝ =>
      ∑ S ∈ ({{0, 1}, {2}} : Finset (Finset (Fin 3))), (if S = {2} then 3 else 1) * ∏ i ∈ S, z i)
      (fun i => if i ∈ ({2} : Finset (Fin 3)) then 1 else 0) = 3 := by
  rw [hermiteCoeff_sum_mul_prod, ite_eq_left (by decide), ite_eq_left rfl]

/-- The mean of the indicator of the halfspace `z 0 ≤ 0` is `f̂(0) = 1 / 2`: at `ρ = 1`, its noise
stability `E[f²] = E[f]` is `1 / 2` by Sheppard's formula. -/
example :
    hermiteCoeff (fun z : Fin 2 → ℝ => (Set.Iic (0 : ℝ)).indicator (1 : ℝ → ℝ) (z 0)) 0 =
      1 / 2 := by
  have hf : MemLp (fun z : Fin 2 → ℝ => (Set.Iic (0 : ℝ)).indicator (1 : ℝ → ℝ) (z 0)) 2
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
    refine memLp_of_bounded (a := 0) (b := 1) (ae_of_all _ fun z => ?_) ?_ 2
    · simp only [Set.indicator, Pi.one_apply]
      split_ifs <;> norm_num
    · exact ((measurable_one.indicator measurableSet_Iic).comp
        (measurable_pi_apply 0)).aestronglyMeasurable
  have h := gaussianNoiseStability_indicator_Iic_eval (ι := Fin 2) (ρ := 1) (by norm_num) 0
  rw [gaussianNoiseStability_eq_integral_mul_gaussianNoiseOp (by norm_num) hf,
    gaussianNoiseOp_one, Real.arccos_one] at h
  rw [hermiteCoeff_zero]
  convert h using 1
  · congr 1 with z
    simp only [Set.indicator, Pi.one_apply]
    split_ifs <;> norm_num
  · norm_num

/-- The degree-ordered Hermite expansion of the halfspace indicator: the `L²` error of its
truncation to degree `k` tends to `0`. -/
example : Filter.Tendsto (fun k : ℕ =>
    ‖∑ α ∈ (Fintype.piFinset fun _ : Fin 2 => Finset.range (k + 1)).filter
        (fun α => ∑ i, α i ≤ k),
        hermiteCoeff (fun z : Fin 2 → ℝ => if 0 < z 0 then (1 : ℝ) else 0) α •
          (memLp_multiHermite α).toLp (multiHermite α) - memLp_halfspace.toLp _‖)
    Filter.atTop (nhds 0) :=
  tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_sum_degree_le_hermiteCoeff_smul memLp_halfspace)

/-- For `k ≥ 2`, the degree-`k` truncation of the Hermite expansion of `z₀ z₁ = h_{(1, 1)}` is
`h_{(1, 1)}` itself. -/
example (k : ℕ) (hk : 2 ≤ k) :
    ∑ α ∈ (Fintype.piFinset fun _ : Fin 2 => Finset.range (k + 1)).filter (fun α => ∑ i, α i ≤ k),
      hermiteCoeff (multiHermite fun _ => 1) α • (memLp_multiHermite α).toLp (multiHermite α) =
      (memLp_multiHermite fun _ : Fin 2 => 1).toLp (multiHermite fun _ => 1) := by
  simp only [hermiteCoeff_multiHermite, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Fin.sum_univ_two]
  split_ifs with h
  · rfl
  · exact absurd ⟨fun _ => by omega, by omega⟩ h

/-- Uniqueness of Hermite expansions recovers Proposition 11.37 from the expansion of `U_ρ f`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : (Fin 2 → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)) :
    hermiteCoeff (gaussianNoiseOp ρ f) = fun α => ρ ^ (∑ i, α i) * hermiteCoeff f α :=
  hermiteCoeff_eq_of_hasSum (hf.gaussianNoiseOp hρ one_le_two)
    (hasSum_hermiteCoeff_gaussianNoiseOp_smul hρ hf)

/-- **Proposition 11.37** on `h_α`: `(U_ρ h_α)^(α) = ρ ^ |α|`. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (α : Fin 3 → ℕ) :
    hermiteCoeff (gaussianNoiseOp ρ (multiHermite α)) α = ρ ^ (∑ i, α i) := by
  rw [hermiteCoeff_gaussianNoiseOp hρ (memLp_multiHermite α), hermiteCoeff_multiHermite,
    ite_eq_left rfl, mul_one]

/-- **Proposition 11.37** gives `Stab_ρ[h_α] = ρ ^ |α|`, as does Proposition 11.33. -/
example {ρ : ℝ} (hρ : |ρ| ≤ 1) (α : Fin 3 → ℕ) :
    gaussianNoiseStability ρ (multiHermite α) = ρ ^ (∑ i, α i) := by
  rw [gaussianNoiseStability_eq_tsum hρ (memLp_multiHermite α)]
  have h (β : Fin 3 → ℕ) : ρ ^ (∑ i, β i) * hermiteCoeff (multiHermite α) β ^ 2 =
      if β = α then ρ ^ (∑ i, α i) else 0 := by
    rw [hermiteCoeff_multiHermite]
    by_cases hβ : β = α
    · subst hβ
      rw [ite_eq_left rfl, ite_eq_left rfl, one_pow, mul_one]
    · rw [ite_eq_right (Ne.symm hβ), ite_eq_right hβ, sq, mul_zero, mul_zero]
  simp only [h]
  exact tsum_ite_eq _ _

end CslibFrontierTests.GaussianHermiteExpansion
