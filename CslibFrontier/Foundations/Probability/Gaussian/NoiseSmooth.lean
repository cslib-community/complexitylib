/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `NoiseSmooth.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.NoiseOperator
import CslibFrontier.Foundations.Analysis.Calculus.ParametricIntegralExp
import CslibFrontier.Foundations.MeasureTheory.Constructions.PiWithDensity
import CslibFrontier.Foundations.Probability.Gaussian.Real

/-!
# Smoothness of the Gaussian noise operator

For `|ρ| < 1` the noise operator smooths: `U_ρ f` is `C^∞` for every `f ∈ L¹(γⁿ)`
[O'Donnell, Proposition 11.16][ODonnell2014] (`contDiff_gaussianNoiseOp`). Here `U_ρ f` is the
pointwise integral `gaussianNoiseOp ρ f` of Definition 11.12, and it depends only on the
`γⁿ`-class of `f` at every point (`gaussianNoiseOp_congr_ae_of_abs_lt_one`): so `U_ρ f` is a
canonical smooth function attached to the `L¹` class of `f`.

The proof moves the dependence on `z` from `f` to a kernel. The noisy point `ρ z + √(1 - ρ²) g`
has the law of independent Gaussians of means `ρ zᵢ` and variance `1 - ρ²`, whose density with
respect to `γ` on each coordinate is a ratio of Gaussian densities
(`gaussianReal_eq_withDensity_div`); so `U_ρ f z` is the integral of `f` against the product of
these ratios, the Mehler kernel (`gaussianNoiseOp_eq_integral_prod_div_mul`). Expanding the
squares, the kernel is `exp (-c ‖z‖₂²)` times `exp ((ρ / (1 - ρ²)) ⟨y, z⟩)` times a function of `y`
alone that decays like `exp (-c ‖y‖₂²)`, with `c = ρ² / (2 (1 - ρ²))`. Hence `U_ρ f` is a Gaussian
times a Laplace transform with all exponential moments, which is smooth
(`contDiff_integral_exp_smul`). This route replaces the hint of Exercise 11.5, which rescales
`U_ρ f` to a convolution of `f` with a Gaussian: Mathlib's smoothness theorems for convolutions
need one factor to have compact support, and neither `f` nor the Gaussian does.

## Main results

* `ProbabilityTheory.gaussianNoiseOp_eq_integral_prod_div_mul`: `U_ρ f z` as an integral of `f`
  against the Mehler kernel, the density of the noisy point (kernel form).
* `ProbabilityTheory.gaussianNoiseOp_congr_ae_of_abs_lt_one`: for `|ρ| < 1`, `U_ρ f` depends only
  on the `γⁿ`-class of `f`, everywhere.
* `ProbabilityTheory.contDiff_gaussianNoiseOp`: `U_ρ f` is smooth for `|ρ| < 1`
  (Proposition 11.16).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real
open scoped NNReal ContDiff

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The noisy coordinate `ρ zᵢ + √(1 - ρ²) g` of a standard Gaussian `g` is a Gaussian of mean
`ρ zᵢ` and variance `1 - ρ²`. -/
private theorem gaussianReal_map_noisy (a : ℝ) {ρ : ℝ} (hρ : |ρ| < 1) :
    (gaussianReal 0 1).map (fun t => a + √(1 - ρ ^ 2) * t) =
      gaussianReal a (1 - ρ ^ 2).toNNReal := by
  have hv : 0 ≤ 1 - ρ ^ 2 := sub_nonneg.2 ((sq_le_one_iff_abs_le_one ρ).2 hρ.le)
  rw [show (fun t => a + √(1 - ρ ^ 2) * t) = (fun s => a + s) ∘ fun t => √(1 - ρ ^ 2) * t
      from rfl, ← Measure.map_map (measurable_const_add a) (measurable_const_mul _),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  congr 1
  · ring
  · ext
    simp [Real.sq_sqrt hv, Real.coe_toNNReal _ hv]

/-- The law of the noisy point `ρ z + √(1 - ρ²) g` has density
`∏ i, φ_{ρ zᵢ, 1 - ρ²} (yᵢ) / φ_{0,1} (yᵢ)` with respect to `γⁿ`. -/
private theorem pi_gaussianReal_map_noisy {ρ : ℝ} (hρ : |ρ| < 1) (z : ι → ℝ) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun g i => ρ * z i + √(1 - ρ ^ 2) * g i) =
      (Measure.pi fun _ : ι => gaussianReal 0 1).withDensity fun y => ∏ i, ENNReal.ofReal
        (gaussianPDFReal (ρ * z i) (1 - ρ ^ 2).toNNReal (y i) / gaussianPDFReal 0 1 (y i)) := by
  set v := (1 - ρ ^ 2).toNNReal
  have hv : v ≠ 0 := by
    simp only [v, ne_eq, Real.toNNReal_eq_zero, not_le, sub_pos]
    exact (sq_lt_one_iff_abs_lt_one ρ).2 hρ
  set k : ι → ℝ → ENNReal :=
    fun i t => ENNReal.ofReal (gaussianPDFReal (ρ * z i) v t / gaussianPDFReal 0 1 t)
  have hk (i : ι) : Measurable (k i) := by fun_prop
  have hmap : (Measure.pi fun _ : ι => gaussianReal 0 1).map
      (fun g i => ρ * z i + √(1 - ρ ^ 2) * g i) =
      (Measure.pi fun _ : ι => gaussianReal 0 1).withDensity fun y => ∏ i, k i (y i) := by
    refine (Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
      (f := fun i t => ρ * z i + √(1 - ρ ^ 2) * t) fun i => by fun_prop).trans ?_
    rw [← Measure.pi_withDensity hk]
    congr 1
    funext i
    rw [gaussianReal_map_noisy _ hρ, gaussianReal_eq_withDensity_div _ hv]
  exact hmap

/-- **The noise operator as an integral against the Mehler kernel**: for `|ρ| < 1`, `U_ρ f z` is
the integral of `f` against the density `∏ i, φ_{ρ zᵢ, 1 - ρ²} (yᵢ) / φ_{0,1} (yᵢ)` of the noisy
point `ρ z + √(1 - ρ²) g` with respect to `γⁿ`. -/
theorem gaussianNoiseOp_eq_integral_prod_div_mul {ρ : ℝ} (hρ : |ρ| < 1) {f : (ι → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1)) (z : ι → ℝ) :
    gaussianNoiseOp ρ f z = ∫ y, (∏ i, gaussianPDFReal (ρ * z i) (1 - ρ ^ 2).toNNReal (y i) /
      gaussianPDFReal 0 1 (y i)) * f y ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have hD : Measurable fun y : ι → ℝ => ∏ i, ENNReal.ofReal
      (gaussianPDFReal (ρ * z i) (1 - ρ ^ 2).toNNReal (y i) / gaussianPDFReal 0 1 (y i)) := by
    fun_prop
  have hfm := hf.mono_ac (pi_gaussianReal_map_noisy hρ z ▸ withDensity_absolutelyContinuous _ _)
  have hT : Measurable fun (g : ι → ℝ) (i : ι) => ρ * z i + √(1 - ρ ^ 2) * g i := by fun_prop
  rw [gaussianNoiseOp, ← integral_map hT.aemeasurable hfm, pi_gaussianReal_map_noisy hρ z,
    integral_withDensity_eq_integral_toReal_smul hD
      (ae_of_all _ fun y => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal ?_
  exact div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

/-- **For `|ρ| < 1`, `U_ρ f` depends only on the `γⁿ`-class of `f`, at every point**: if
`f =ᵐ[γⁿ] f'` then `gaussianNoiseOp ρ f = gaussianNoiseOp ρ f'` as functions, because the law of
the noisy point is absolutely continuous with respect to `γⁿ`. With `contDiff_gaussianNoiseOp`,
`U_ρ f` is a canonical smooth function attached to the `L¹` class of `f`. For `|ρ| ≤ 1` the
identity holds `γⁿ`-almost everywhere (`gaussianNoiseOp_congr_ae`). -/
theorem gaussianNoiseOp_congr_ae_of_abs_lt_one {ρ : ℝ} (hρ : |ρ| < 1) {f f' : (ι → ℝ) → ℝ}
    (h : f =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] f') :
    gaussianNoiseOp ρ f = gaussianNoiseOp ρ f' := by
  funext z
  refine integral_congr_ae (QuasiMeasurePreserving.ae_eq_comp ⟨by fun_prop, ?_⟩ h)
  rw [pi_gaussianReal_map_noisy hρ z]
  exact withDensity_absolutelyContinuous _ _

/-- The density ratio of one noisy coordinate, expanded: with `v = 1 - ρ²` and `c = ρ² / (2 v)`,
`φ_{ρ a, v} (t) / φ_{0,1} (t) = v^{-1/2} exp (-c a²) exp ((ρ / v) t a) exp (-c t²)`. -/
private theorem gaussianPDFReal_div_eq {ρ : ℝ} (hρ : |ρ| < 1) (a t : ℝ) :
    gaussianPDFReal (ρ * a) (1 - ρ ^ 2).toNNReal t / gaussianPDFReal 0 1 t =
      (√(1 - ρ ^ 2))⁻¹ * (rexp (-(ρ ^ 2 / (2 * (1 - ρ ^ 2)) * a ^ 2)) *
        (rexp (ρ / (1 - ρ ^ 2) * (t * a)) * rexp (-(ρ ^ 2 / (2 * (1 - ρ ^ 2)) * t ^ 2)))) := by
  have hv : 0 < 1 - ρ ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one ρ).2 hρ)
  have hexp : rexp (-(t - ρ * a) ^ 2 / (2 * (1 - ρ ^ 2))) = rexp (-t ^ 2 / 2) *
      (rexp (-(ρ ^ 2 / (2 * (1 - ρ ^ 2)) * a ^ 2)) *
        (rexp (ρ / (1 - ρ ^ 2) * (t * a)) * rexp (-(ρ ^ 2 / (2 * (1 - ρ ^ 2)) * t ^ 2)))) := by
    simp only [← exp_add]
    congr 1
    field_simp
    ring
  simp only [gaussianPDFReal, Real.coe_toNNReal _ hv.le, NNReal.coe_one, mul_one, sub_zero, hexp]
  rw [Real.sqrt_mul (by positivity) (1 - ρ ^ 2)]
  field_simp

/-- The linear functional `z ↦ (ρ / (1 - ρ²)) ⟨y, z⟩` in the exponent of the Mehler kernel. -/
private noncomputable def noiseDual (ρ : ℝ) (y : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  (ρ / (1 - ρ ^ 2)) • ∑ i, y i • ContinuousLinearMap.proj i

/-- `noiseDual ρ y z = (ρ / (1 - ρ²)) ∑ i, yᵢ zᵢ`. -/
private theorem noiseDual_apply (ρ : ℝ) (y z : ι → ℝ) :
    noiseDual ρ y z = ρ / (1 - ρ ^ 2) * ∑ i, y i * z i := by
  simp [noiseDual]

/-- `noiseDual ρ y` depends continuously on `y`. -/
private theorem continuous_noiseDual (ρ : ℝ) : Continuous (noiseDual (ι := ι) ρ) := by
  unfold noiseDual
  fun_prop

/-- The operator norm of `noiseDual ρ y` is at most `|ρ / (1 - ρ²)| ∑ i, |yᵢ|`. -/
private theorem norm_noiseDual_le (ρ : ℝ) (y : ι → ℝ) :
    ‖noiseDual ρ y‖ ≤ |ρ / (1 - ρ ^ 2)| * ∑ i, |y i| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [noiseDual_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, Finset.sum_mul]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  gcongr
  simpa using norm_le_pi_norm w i

/-- **The Mehler kernel factorizes**: with `v = 1 - ρ²` and `c = ρ² / (2 v)`, the density of the
noisy point is `exp (-c ‖z‖₂²) exp ((ρ / v) ⟨y, z⟩) v^{-n/2} exp (-c ‖y‖₂²)`. -/
private theorem prod_gaussianPDFReal_div_eq {ρ : ℝ} (hρ : |ρ| < 1) (z y : ι → ℝ) :
    ∏ i, gaussianPDFReal (ρ * z i) (1 - ρ ^ 2).toNNReal (y i) / gaussianPDFReal 0 1 (y i) =
      rexp (∑ i, -(ρ ^ 2 / (2 * (1 - ρ ^ 2)) * z i ^ 2)) * (rexp (noiseDual ρ y z) *
        ((√(1 - ρ ^ 2))⁻¹ ^ Fintype.card ι *
          rexp (∑ i, -(ρ ^ 2 / (2 * (1 - ρ ^ 2)) * y i ^ 2)))) := by
  simp only [gaussianPDFReal_div_eq hρ, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← exp_sum, noiseDual_apply, Finset.mul_sum]
  ring

/-- The `y`-factor of the Mehler kernel times `f` has all exponential moments along
`noiseDual ρ`: its Gaussian decay `exp (-c ‖y‖₂²)` beats `exp (C ‖noiseDual ρ y‖)`. -/
private theorem integrable_exp_mul_norm_noiseDual {ρ : ℝ} (hρ : |ρ| < 1) (hρ0 : ρ ≠ 0)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1)) (C : ℝ) :
    Integrable (fun y : ι → ℝ => rexp (C * ‖noiseDual ρ y‖) * ‖(√(1 - ρ ^ 2))⁻¹ ^ Fintype.card ι *
      rexp (∑ i, -(ρ ^ 2 / (2 * (1 - ρ ^ 2)) * y i ^ 2)) * f y‖)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hv : 0 < 1 - ρ ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one ρ).2 hρ)
  set c := ρ ^ 2 / (2 * (1 - ρ ^ 2))
  have hc : 0 < c := by positivity
  set B := |C| * |ρ / (1 - ρ ^ 2)|
  set a := (√(1 - ρ ^ 2))⁻¹ ^ Fintype.card ι
  have ha : 0 ≤ a := by positivity
  refine (hf.norm.const_mul (a * rexp (Fintype.card ι * (B ^ 2 / (4 * c))))).mono' ?_
    (ae_of_all _ fun y => ?_)
  · have hcont : Continuous fun y : ι → ℝ => a * rexp (∑ i, -(c * y i ^ 2)) := by fun_prop
    exact (continuous_exp.comp (continuous_const.mul
      (continuous_noiseDual (ι := ι) ρ).norm)).aestronglyMeasurable.mul
      (hcont.aestronglyMeasurable.mul hf.1).norm
  have hexp : C * ‖noiseDual ρ y‖ + ∑ i, -(c * y i ^ 2) ≤ Fintype.card ι * (B ^ 2 / (4 * c)) := by
    have h1 : C * ‖noiseDual ρ y‖ ≤ B * ∑ i, |y i| := by
      calc C * ‖noiseDual ρ y‖ ≤ |C| * ‖noiseDual ρ y‖ := by
            gcongr
            exact le_abs_self C
        _ ≤ B * ∑ i, |y i| := by
            rw [mul_assoc]
            gcongr
            exact norm_noiseDual_le ρ y
    have h2 (t : ℝ) : B * |t| + -(c * t ^ 2) ≤ B ^ 2 / (4 * c) := by
      have hsq : (B - 2 * c * |t|) ^ 2 = B ^ 2 - 4 * c * (B * |t|) + 4 * c ^ 2 * t ^ 2 := by
        rw [← sq_abs t]
        ring
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (B - 2 * c * |t|)]
    calc C * ‖noiseDual ρ y‖ + ∑ i, -(c * y i ^ 2)
        ≤ ∑ i, (B * |y i| + -(c * y i ^ 2)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          linarith
      _ ≤ ∑ _i : ι, B ^ 2 / (4 * c) := Finset.sum_le_sum fun i _ => h2 (y i)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [norm_mul, norm_of_nonneg (exp_nonneg _), norm_norm, norm_mul, norm_mul,
    norm_of_nonneg ha, norm_of_nonneg (exp_nonneg _)]
  calc rexp (C * ‖noiseDual ρ y‖) * (a * rexp (∑ i, -(c * y i ^ 2)) * ‖f y‖)
      = a * rexp (C * ‖noiseDual ρ y‖ + ∑ i, -(c * y i ^ 2)) * ‖f y‖ := by
        rw [exp_add]
        ring
    _ ≤ a * rexp (Fintype.card ι * (B ^ 2 / (4 * c))) * ‖f y‖ := by gcongr

/-- **The Gaussian noise operator smooths** [O'Donnell, Proposition 11.16][ODonnell2014]: for
`f ∈ L¹(γⁿ)` and `-1 < ρ < 1`, `U_ρ f` is `C^∞`. This is the pointwise integral
`gaussianNoiseOp ρ f` of Definition 11.12, which is the same function for every representative of
the `γⁿ`-class of `f` (`gaussianNoiseOp_congr_ae_of_abs_lt_one`). -/
theorem contDiff_gaussianNoiseOp {ρ : ℝ} (hρ : |ρ| < 1) {f : (ι → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ContDiff ℝ ∞ (gaussianNoiseOp ρ f) := by
  rcases eq_or_ne ρ 0 with rfl | hρ0
  · rw [show gaussianNoiseOp 0 f = fun _ => _ from funext (gaussianNoiseOp_zero f)]
    exact contDiff_const
  set c := ρ ^ 2 / (2 * (1 - ρ ^ 2))
  set h : (ι → ℝ) → ℝ := fun y =>
    (√(1 - ρ ^ 2))⁻¹ ^ Fintype.card ι * rexp (∑ i, -(c * y i ^ 2)) * f y
  have hh : AEStronglyMeasurable h (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    have hcont : Continuous fun y : ι → ℝ =>
        (√(1 - ρ ^ 2))⁻¹ ^ Fintype.card ι * rexp (∑ i, -(c * y i ^ 2)) := by fun_prop
    exact hcont.aestronglyMeasurable.mul hf.1
  have key : gaussianNoiseOp ρ f = fun z => rexp (∑ i, -(c * z i ^ 2)) *
      ∫ y, rexp (noiseDual ρ y z) • h y ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
    funext z
    rw [gaussianNoiseOp_eq_integral_prod_div_mul hρ hf.1, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [prod_gaussianPDFReal_div_eq hρ, smul_eq_mul]
    ring
  rw [key]
  have hA : ContDiff ℝ ∞ fun z : ι → ℝ => rexp (∑ i, -(c * z i ^ 2)) := by fun_prop
  exact hA.mul (contDiff_integral_exp_smul
      (continuous_noiseDual ρ).aestronglyMeasurable hh
      (integrable_exp_mul_norm_noiseDual hρ hρ0 hf))

end ProbabilityTheory
