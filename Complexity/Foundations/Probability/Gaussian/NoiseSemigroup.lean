/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `NoiseSemigroup.lean`)

public import Complexity.Foundations.Probability.Gaussian.NoiseOperator
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The Gaussian noise semigroup

The Gaussian noise operators `U_ρ` form a semigroup, the *Ornstein–Uhlenbeck semigroup*
[O'Donnell, Remark 11.14][ODonnell2014]: `U_ρ₁ U_ρ₂ f = U_{ρ₁ ρ₂} f` almost everywhere for
`f ∈ L¹(γⁿ)` and `ρ₁, ρ₂ ∈ [-1, 1]` (`gaussianNoiseOp_gaussianNoiseOp`, Exercise 11.4). Indeed
`ρ₂ √(1 - ρ₁²) g + √(1 - ρ₂²) h` is distributed as `√(1 - ρ₁² ρ₂²) g'` for independent standard
Gaussian vectors `g`, `h`, `g'`. As `ρ → 1⁻`, `U_ρ f → f` in `L¹(γⁿ)`
(`tendsto_eLpNorm_gaussianNoiseOp_sub`, Proposition 11.17): by dominated convergence for bounded
continuous `f`, and in general by density of these functions in `L¹(γⁿ)` and the contraction
bound of Proposition 11.15.

## Main results

* `ProbabilityTheory.gaussianNoiseOp_gaussianNoiseOp`: the semigroup law (Exercise 11.4).
* `ProbabilityTheory.tendsto_eLpNorm_gaussianNoiseOp_sub`: `U_ρ f → f` in `L¹(γⁿ)` as `ρ → 1⁻`
  (Proposition 11.17).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The combined noise `ρ₂ √(1 - ρ₁²) g + √(1 - ρ₂²) h` is `√(1 - ρ₁² ρ₂²) (α g + √(1 - α²) h)`
for some `|α| ≤ 1`: write `(ρ₂ √(1 - ρ₁²), √(1 - ρ₂²))` in polar form `r (cos θ, sin θ)` with
`r = √(1 - ρ₁² ρ₂²)` and `θ ∈ [0, π]`, and take `α = cos θ`. -/
private theorem exists_noise_split {ρ₁ ρ₂ : ℝ} (hρ₁ : |ρ₁| ≤ 1) (hρ₂ : |ρ₂| ≤ 1) :
    ∃ α : ℝ, |α| ≤ 1 ∧ √(1 - (ρ₁ * ρ₂) ^ 2) * α = ρ₂ * √(1 - ρ₁ ^ 2) ∧
      √(1 - (ρ₁ * ρ₂) ^ 2) * √(1 - α ^ 2) = √(1 - ρ₂ ^ 2) := by
  have h₁ : 0 ≤ 1 - ρ₁ ^ 2 := sub_nonneg.2 ((sq_le_one_iff_abs_le_one ρ₁).2 hρ₁)
  have h₂ : 0 ≤ 1 - ρ₂ ^ 2 := sub_nonneg.2 ((sq_le_one_iff_abs_le_one ρ₂).2 hρ₂)
  set w : ℂ := ⟨ρ₂ * √(1 - ρ₁ ^ 2), √(1 - ρ₂ ^ 2)⟩
  have hw : √(1 - (ρ₁ * ρ₂) ^ 2) = ‖w‖ := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, mul_pow, mul_pow, sq_sqrt h₁, sq_sqrt h₂]
    ring_nf
  have hθ : 0 ≤ w.arg := Complex.arg_nonneg_iff.2 (sqrt_nonneg _)
  refine ⟨cos w.arg, abs_cos_le_one _, by rw [hw, Complex.norm_mul_cos_arg], ?_⟩
  rw [← sin_eq_sqrt_one_sub_cos_sq hθ (Complex.arg_le_pi w), hw, Complex.norm_mul_sin_arg]

/-- **The semigroup law** [O'Donnell, Exercise 11.4][ODonnell2014] (see Remark 11.14): for
`ρ₁, ρ₂ ∈ [-1, 1]` and `f ∈ L¹(γⁿ)`, `U_ρ₁ U_ρ₂ f = U_{ρ₁ ρ₂} f` almost everywhere. For `z` off a
null set, `U_ρ₁ U_ρ₂ f z` averages `f (ρ₁ ρ₂ z + ρ₂ √(1 - ρ₁²) g + √(1 - ρ₂²) h)` over independent
standard Gaussian vectors `g` and `h`, and the combined noise is distributed as
`√(1 - ρ₁² ρ₂²) g'`. -/
theorem gaussianNoiseOp_gaussianNoiseOp {ρ₁ ρ₂ : ℝ} (hρ₁ : |ρ₁| ≤ 1) (hρ₂ : |ρ₂| ≤ 1)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    gaussianNoiseOp ρ₁ (gaussianNoiseOp ρ₂ f) =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1]
      gaussianNoiseOp (ρ₁ * ρ₂) f := by
  set γ := Measure.pi fun _ : ι => gaussianReal 0 1
  obtain ⟨α, hα, e₁, e₂⟩ := exists_noise_split hρ₁ hρ₂
  set σ := √(1 - (ρ₁ * ρ₂) ^ 2)
  have hρ : |ρ₁ * ρ₂| ≤ 1 :=
    (abs_mul ρ₁ ρ₂).trans_le ((mul_le_of_le_one_left (abs_nonneg _) hρ₁).trans hρ₂)
  have hA := measurePreserving_gaussianNoise (ι := ι) hα
  have hP := measurePreserving_gaussianNoise (ι := ι) hρ
  have hT := hP.comp ((MeasurePreserving.id γ).prod hA)
  filter_upwards [(hT.integrable_comp_of_integrable hf).prod_right_ae,
    (hP.integrable_comp_of_integrable hf).prod_right_ae] with z hz hz'
  have hmap := integral_map (μ := γ.prod γ) hA.aemeasurable
    (f := fun y => f fun i => ρ₁ * ρ₂ * z i + σ * y i)
    (by rw [hA.map_eq]; exact hz'.aestronglyMeasurable)
  rw [hA.map_eq] at hmap
  calc gaussianNoiseOp ρ₁ (gaussianNoiseOp ρ₂ f) z
      = ∫ g, ∫ h, f (fun i => ρ₁ * ρ₂ * z i + σ * (α * g i + √(1 - α ^ 2) * h i)) ∂γ ∂γ := by
        refine integral_congr_ae (ae_of_all _ fun g => integral_congr_ae (ae_of_all _ fun h => ?_))
        refine congrArg f (funext fun i => ?_)
        linear_combination (-g i) * e₁ - h i * e₂
    _ = ∫ q, f (fun i => ρ₁ * ρ₂ * z i + σ * (α * q.1 i + √(1 - α ^ 2) * q.2 i)) ∂γ.prod γ :=
        (integral_prod _ hz).symm
    _ = gaussianNoiseOp (ρ₁ * ρ₂) f z := hmap.symm

/-- `U_ρ g → g` in `L¹(γⁿ)` as `ρ → 1⁻`, for bounded continuous `g`, by dominated convergence. -/
private theorem tendsto_eLpNorm_gaussianNoiseOp_sub_of_bcf (g : (ι → ℝ) →ᵇ ℝ) :
    Tendsto (fun ρ => eLpNorm (gaussianNoiseOp ρ g - ⇑g) 1
      (Measure.pi fun _ : ι => gaussianReal 0 1)) (𝓝[<] 1) (𝓝 0) := by
  set γ := Measure.pi fun _ : ι => gaussianReal 0 1
  have hρ : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), |ρ| ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with ρ h
    exact abs_le.2 ⟨h.1.le, h.2.le⟩
  have hg := g.continuous.aestronglyMeasurable (μ := γ)
  have hc (z y : ι → ℝ) : Continuous fun ρ : ℝ => g fun i => ρ * z i + √(1 - ρ ^ 2) * y i :=
    g.continuous.comp (by fun_prop)
  -- pointwise convergence `U_ρ g z → g z`, by dominated convergence in `g`
  have hpt (z : ι → ℝ) : Tendsto (fun ρ => gaussianNoiseOp ρ g z) (𝓝[<] 1) (𝓝 (g z)) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := 𝓝[<] (1 : ℝ))
      (F := fun ρ y => g fun i => ρ * z i + √(1 - ρ ^ 2) * y i) (f := fun _ => g z) (fun _ => ‖g‖)
      (.of_forall fun ρ => (g.continuous.comp (by fun_prop)).aestronglyMeasurable)
      (.of_forall fun ρ => ae_of_all _ fun y => g.norm_coe_le_norm _) (integrable_const _)
      (ae_of_all _ fun y => by simpa using ((hc z y).tendsto 1).mono_left nhdsWithin_le_nhds)
    simp only [integral_const, probReal_univ, one_smul] at h
    exact h
  have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := γ)
    (F := fun ρ z => ‖gaussianNoiseOp ρ g z - g z‖ₑ) (f := 0) (fun _ => 2 * ‖g‖ₑ)
    (hρ.mono fun ρ h => ((hg.gaussianNoiseOp h).sub hg).aemeasurable.enorm)
    (.of_forall fun ρ => ae_of_all _ fun z => ?_) (by simp [lintegral_const, ENNReal.mul_eq_top])
    (ae_of_all _ fun z => by simpa using ((hpt z).sub_const (g z)).enorm)
  · simp only [Pi.zero_apply, lintegral_zero] at h
    refine h.congr' (hρ.mono fun ρ h => ?_)
    exact (eLpNorm_one_eq_lintegral_enorm ((hg.gaussianNoiseOp h).sub hg)).symm
  · refine (enorm_sub_le).trans ?_
    rw [two_mul]
    gcongr
    · exact enorm_le_iff_norm_le.2 <| (norm_integral_le_of_norm_le_const (C := ‖g‖)
        (ae_of_all _ fun y => g.norm_coe_le_norm _)).trans (by simp)
    · exact enorm_le_iff_norm_le.2 (g.norm_coe_le_norm z)

/-- **Continuity of the noise operator at `ρ = 1`** [O'Donnell, Proposition 11.17][ODonnell2014]
(Exercise 11.6(a)): for `f ∈ L¹(γⁿ)`, `‖U_ρ f - f‖₁ → 0` as `ρ → 1⁻`. -/
theorem tendsto_eLpNorm_gaussianNoiseOp_sub {f : (ι → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    Tendsto (fun ρ => eLpNorm (gaussianNoiseOp ρ f - f) 1
      (Measure.pi fun _ : ι => gaussianReal 0 1)) (𝓝[<] 1) (𝓝 0) := by
  set γ := Measure.pi fun _ : ι => gaussianReal 0 1
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne'
  obtain ⟨g, hfg, -⟩ :=
    (memLp_one_iff_integrable.2 hf).exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top hε3
  have hgi : Integrable g γ := g.integrable γ
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (tendsto_eLpNorm_gaussianNoiseOp_sub_of_bcf g) _
      (pos_iff_ne_zero.2 hε3),
    Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with ρ hρg hρ
  have hρ : |ρ| ≤ 1 := abs_le.2 ⟨hρ.1.le, hρ.2.le⟩
  have hadd := gaussianNoiseOp_add hρ (hf.sub hgi) hgi
  simp only [Pi.sub_apply, sub_add_cancel] at hadd
  have hsplit : gaussianNoiseOp ρ f - f =ᵐ[γ]
      gaussianNoiseOp ρ (f - ⇑g) + (gaussianNoiseOp ρ g - ⇑g) + (⇑g - f) := by
    filter_upwards [hadd] with z hz
    simp only [Pi.add_apply, Pi.sub_apply, hz]
    ring
  rw [eLpNorm_congr_ae hsplit]
  calc eLpNorm (gaussianNoiseOp ρ (f - ⇑g) + (gaussianNoiseOp ρ g - ⇑g) + (⇑g - f)) 1 γ
      ≤ eLpNorm (gaussianNoiseOp ρ (f - ⇑g)) 1 γ + eLpNorm (gaussianNoiseOp ρ g - ⇑g) 1 γ +
          eLpNorm (⇑g - f) 1 γ := by
        refine (eLpNorm_add_le le_rfl).trans ?_
        gcongr
        exact eLpNorm_add_le le_rfl
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (eLpNorm_gaussianNoiseOp_le hρ le_rfl (hf.sub hgi).1).trans hfg
        · rw [eLpNorm_sub_comm]
          exact hfg
    _ = ε := ENNReal.add_thirds ε

end ProbabilityTheory
