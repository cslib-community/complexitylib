/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `NoiseOperator.lean`)

public import Complexity.Foundations.Probability.Gaussian.Correlated
import Complexity.Foundations.Probability.Gaussian.Multivariate

/-!
# The Gaussian noise operator

For `ρ ∈ [-1, 1]` the *Gaussian noise operator* `U_ρ` averages a function `f` on `ι → ℝ` over
the `ρ`-correlated neighbourhood of a point: `U_ρ f z = E[f (ρ z + √(1 - ρ²) g)]` for a standard
Gaussian vector `g` [O'Donnell, Definition 11.12][ODonnell2014] (`gaussianNoiseOp`). Throughout,
`γⁿ` is the standard Gaussian measure `Measure.pi fun _ : ι => gaussianReal 0 1`. Up to equality
`γⁿ`-almost everywhere, `U_ρ` is additive on integrable functions and depends only on the
`γⁿ`-class of `f` (`gaussianNoiseOp_add`, `gaussianNoiseOp_congr_ae`).

Integrals over `ρ`-correlated vectors `(z, z')` split as iterated integrals over `z` and the
independent noise `g` (`integral_correlatedGaussianPi`). Hence for `f`, `g ∈ L²(γⁿ)` the
correlation `E[f z g z']` is `⟨f, U_ρ g⟩` (`integral_mul_gaussianNoiseOp`); in particular the
Gaussian noise stability is `Stab_ρ[f] = ⟨f, U_ρ f⟩` (Definition 11.18), and `U_ρ` is
self-adjoint since `(z', z)` has the law of `(z, z')`. The operator preserves the mean, fixes the
constants, is the identity at `ρ = 1` and the expectation at `ρ = 0`, and is a contraction on
every `Lᵖ(γⁿ)`, `1 ≤ p ≤ ∞` (Proposition 11.15). It multiplies linear functions by `ρ`
(the linear case of Fact 11.13).

## Main definitions

* `ProbabilityTheory.gaussianNoiseOp`: the Gaussian noise operator `U_ρ`.

## Main results

* `ProbabilityTheory.measurePreserving_gaussianNoise`: `ρ z + √(1 - ρ²) g` is a standard Gaussian
  vector for `|ρ| ≤ 1`.
* `ProbabilityTheory.integral_correlatedGaussianPi`: integrals over correlated vectors.
* `ProbabilityTheory.integral_mul_gaussianNoiseOp`,
  `ProbabilityTheory.gaussianNoiseStability_eq_integral_mul_gaussianNoiseOp`,
  `ProbabilityTheory.integral_mul_gaussianNoiseOp_comm`: `E[f z g z'] = ⟨f, U_ρ g⟩`,
  `Stab_ρ[f] = ⟨f, U_ρ f⟩` and self-adjointness (Definition 11.18).
* `ProbabilityTheory.gaussianNoiseOp_const`, `ProbabilityTheory.gaussianNoiseOp_one`,
  `ProbabilityTheory.gaussianNoiseOp_zero`, `ProbabilityTheory.integral_gaussianNoiseOp`: basic
  values and preservation of the mean.
* `ProbabilityTheory.gaussianNoiseOp_const_mul`, `ProbabilityTheory.gaussianNoiseOp_add`,
  `ProbabilityTheory.gaussianNoiseOp_congr_ae`: linearity and almost-everywhere congruence.
* `ProbabilityTheory.eLpNorm_gaussianNoiseOp_le`, `MeasureTheory.MemLp.gaussianNoiseOp`: `U_ρ` is
  a contraction on `Lᵖ(γⁿ)` (Proposition 11.15).
* `ProbabilityTheory.gaussianNoiseOp_dotProduct`: `U_ρ` of a linear function (the linear case
  of Fact 11.13).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real
open scoped ENNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The **Gaussian noise operator** `U_ρ f z = E[f (ρ z + √(1 - ρ²) g)]`, for a standard
Gaussian vector `g` [O'Donnell, Definitions 11.9 and 11.12][ODonnell2014]. The book defines it
for `ρ ∈ [-1, 1]` and `f ∈ L¹(γⁿ)`; here `ρ` and `f` are arbitrary, and the Bochner integral is
`0` when `f (ρ z + √(1 - ρ²) ·)` is not integrable. -/
noncomputable def gaussianNoiseOp (ρ : ℝ) (f : (ι → ℝ) → ℝ) (z : ι → ℝ) : ℝ :=
  ∫ g, f (fun i => ρ * z i + √(1 - ρ ^ 2) * g i) ∂Measure.pi fun _ : ι => gaussianReal 0 1

/-- **Gaussian noise is standard Gaussian** [O'Donnell, Remark 11.11][ODonnell2014]: for
independent standard Gaussian vectors `z` and `g` and `|ρ| ≤ 1`, the noisy point
`ρ z + √(1 - ρ²) g` is a standard Gaussian vector. -/
theorem measurePreserving_gaussianNoise {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    MeasurePreserving
      (fun q : (ι → ℝ) × (ι → ℝ) => fun i => ρ * q.1 i + √(1 - ρ ^ 2) * q.2 i)
      ((Measure.pi fun _ : ι => gaussianReal 0 1).prod (Measure.pi fun _ : ι => gaussianReal 0 1))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h := correlatedGaussianPi_map_snd ι hρ
  rw [correlatedGaussianPi_eq_map, Measure.map_map measurable_snd (by fun_prop)] at h
  exact ⟨by fun_prop, h⟩

/-- The noisy point `ρ z + √(1 - ρ²) g`, as a function of `(z, g)`. -/
private noncomputable abbrev noisy (ρ : ℝ) (q : (ι → ℝ) × (ι → ℝ)) : ι → ℝ :=
  fun i => ρ * q.1 i + √(1 - ρ ^ 2) * q.2 i

/-- **Integrals over correlated vectors** [O'Donnell, Remark 11.11][ODonnell2014]: an integral
over `ρ`-correlated vectors `(z, z')` is an iterated integral over a standard Gaussian vector `z`
and independent noise `g`, with `z' = ρ z + √(1 - ρ²) g`. -/
theorem integral_correlatedGaussianPi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : ℝ} {F : (ι → ℝ) × (ι → ℝ) → E} (hF : Integrable F (correlatedGaussianPi ι ρ)) :
    ∫ p, F p ∂correlatedGaussianPi ι ρ =
      ∫ z, ∫ g, F (z, fun i => ρ * z i + √(1 - ρ ^ 2) * g i)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have hΦ : Measurable fun q : (ι → ℝ) × (ι → ℝ) => (q.1, noisy ρ q) := by fun_prop
  rw [correlatedGaussianPi_eq_map] at hF ⊢
  rw [integral_map hΦ.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod _ (hF.comp_measurable hΦ)

/-- **Correlation through the noise operator** [O'Donnell, Definition 11.18][ODonnell2014]: for
`f`, `g ∈ L²(γⁿ)` and `ρ`-correlated vectors `(z, z')`, `E[f z g z'] = ⟨f, U_ρ g⟩`. -/
theorem integral_mul_gaussianNoiseOp {ρ : ℝ} (hρ : |ρ| ≤ 1) {f g : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hg : MemLp g 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ z, f z * gaussianNoiseOp ρ g z ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      ∫ p, f p.1 * g p.2 ∂correlatedGaussianPi ι ρ := by
  have h1 : MemLp (fun p : (ι → ℝ) × (ι → ℝ) => f p.1) 2 (correlatedGaussianPi ι ρ) :=
    hf.comp_measurePreserving (measurePreserving_fst_correlatedGaussianPi ι ρ)
  have h2 : MemLp (fun p : (ι → ℝ) × (ι → ℝ) => g p.2) 2 (correlatedGaussianPi ι ρ) :=
    hg.comp_measurePreserving (measurePreserving_snd_correlatedGaussianPi ι hρ)
  rw [integral_correlatedGaussianPi (F := fun p => f p.1 * g p.2) (h1.integrable_mul h2)]
  exact integral_congr_ae (ae_of_all _ fun z => (integral_const_mul _ _).symm)

/-- **Noise stability as an inner product** [O'Donnell, Definition 11.18][ODonnell2014]: for
`f ∈ L²(γⁿ)` and `|ρ| ≤ 1`, `Stab_ρ[f] = ⟨f, U_ρ f⟩`. -/
theorem gaussianNoiseStability_eq_integral_mul_gaussianNoiseOp {ρ : ℝ} (hρ : |ρ| ≤ 1)
    {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    gaussianNoiseStability ρ f =
      ∫ z, f z * gaussianNoiseOp ρ f z ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  rw [gaussianNoiseStability, integral_mul_gaussianNoiseOp hρ hf hf]

/-- **The noise operator is self-adjoint** [O'Donnell, Definition 11.18][ODonnell2014]: for
`f`, `g ∈ L²(γⁿ)` and `|ρ| ≤ 1`, `⟨f, U_ρ g⟩ = ⟨U_ρ f, g⟩`, since `(z', z)` has the law of
`(z, z')`. -/
theorem integral_mul_gaussianNoiseOp_comm {ρ : ℝ} (hρ : |ρ| ≤ 1) {f g : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hg : MemLp g 2 (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ z, f z * gaussianNoiseOp ρ g z ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      ∫ z, gaussianNoiseOp ρ f z * g z ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have hsw : MeasurePreserving (MeasurableEquiv.prodComm (α := ι → ℝ) (β := ι → ℝ))
      (correlatedGaussianPi ι ρ) (correlatedGaussianPi ι ρ) :=
    ⟨MeasurableEquiv.measurable _, correlatedGaussianPi_map_swap ι hρ⟩
  simp only [mul_comm (gaussianNoiseOp ρ f _)]
  rw [integral_mul_gaussianNoiseOp hρ hf hg, integral_mul_gaussianNoiseOp hρ hg hf,
    ← hsw.integral_comp' (fun p => g p.1 * f p.2)]
  exact integral_congr_ae (ae_of_all _ fun p => mul_comm _ _)

/-- The noise operator fixes the constants. -/
@[simp] theorem gaussianNoiseOp_const (ρ c : ℝ) (z : ι → ℝ) :
    gaussianNoiseOp ρ (fun _ => c) z = c := by
  simp only [gaussianNoiseOp, integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- `U_1` is the identity [O'Donnell, §11.1, after Proposition 11.15][ODonnell2014]. -/
@[simp] theorem gaussianNoiseOp_one (f : (ι → ℝ) → ℝ) : gaussianNoiseOp 1 f = f := by
  funext z
  simp only [gaussianNoiseOp, one_pow, sub_self, sqrt_zero, zero_mul, add_zero, one_mul,
    integral_const, probReal_univ, smul_eq_mul]

/-- `U_0 f` is the constant function `E[f]`
[O'Donnell, §11.1, after Proposition 11.15][ODonnell2014]. -/
theorem gaussianNoiseOp_zero (f : (ι → ℝ) → ℝ) (z : ι → ℝ) :
    gaussianNoiseOp 0 f z = ∫ g, f g ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  simp only [gaussianNoiseOp, zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, sqrt_one, one_mul]

/-- The noise operator commutes with scaling. -/
theorem gaussianNoiseOp_const_mul (ρ c : ℝ) (f : (ι → ℝ) → ℝ) (z : ι → ℝ) :
    gaussianNoiseOp ρ (fun y => c * f y) z = c * gaussianNoiseOp ρ f z :=
  integral_const_mul _ _

/-- The noise operator is additive on integrable functions, almost everywhere. -/
theorem gaussianNoiseOp_add {ρ : ℝ} (hρ : |ρ| ≤ 1) {f g : (ι → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hg : Integrable g (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    gaussianNoiseOp ρ (fun y => f y + g y) =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1]
      fun z => gaussianNoiseOp ρ f z + gaussianNoiseOp ρ g z := by
  have hΦ := measurePreserving_gaussianNoise (ι := ι) hρ
  filter_upwards [(hΦ.integrable_comp_of_integrable hf).prod_right_ae,
    (hΦ.integrable_comp_of_integrable hg).prod_right_ae] with z hfz hgz
  exact integral_add hfz hgz

/-- The noise operator respects almost-everywhere equality. -/
theorem gaussianNoiseOp_congr_ae {ρ : ℝ} (hρ : |ρ| ≤ 1) {f f' : (ι → ℝ) → ℝ}
    (h : f =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] f') :
    gaussianNoiseOp ρ f =ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] gaussianNoiseOp ρ f' := by
  filter_upwards [Measure.ae_ae_of_ae_prod
    ((measurePreserving_gaussianNoise hρ).quasiMeasurePreserving.ae_eq_comp h)] with z hz
  exact integral_congr_ae hz

/-- The noise operator maps almost everywhere strongly measurable functions to such
functions. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.gaussianNoiseOp {ρ : ℝ} (hρ : |ρ| ≤ 1)
    {f : (ι → ℝ) → ℝ} (hf : AEStronglyMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    AEStronglyMeasurable (gaussianNoiseOp ρ f) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  (hf.comp_measurePreserving (measurePreserving_gaussianNoise hρ)).integral_prod_right'

/-- **The noise operator preserves the mean**: `E[U_ρ f] = E[f]` for integrable `f` and
`|ρ| ≤ 1`. -/
theorem integral_gaussianNoiseOp {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : (ι → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ z, gaussianNoiseOp ρ f z ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      ∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have hΦ := measurePreserving_gaussianNoise (ι := ι) hρ
  conv_rhs => rw [← hΦ.map_eq, integral_map hΦ.aemeasurable (by rw [hΦ.map_eq]; exact hf.1)]
  exact (integral_prod _ (hΦ.integrable_comp_of_integrable hf)).symm

/-- **The noise operator is a contraction** on `Lᵖ(γⁿ)` for `1 ≤ p ≤ ∞` and `|ρ| ≤ 1`
[O'Donnell, Proposition 11.15][ODonnell2014]: `‖U_ρ f‖_p ≤ ‖f‖_p`. For `p < ∞` this is Jensen's
inequality for `t ↦ |t| ^ p`, as `ρ z + √(1 - ρ²) g` is a standard Gaussian vector. -/
theorem eLpNorm_gaussianNoiseOp_le {ρ : ℝ} (hρ : |ρ| ≤ 1) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : (ι → ℝ) → ℝ} (hf : AEStronglyMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    eLpNorm (gaussianNoiseOp ρ f) p (Measure.pi fun _ : ι => gaussianReal 0 1) ≤
      eLpNorm f p (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  set γ := Measure.pi fun _ : ι => gaussianReal 0 1
  have hΦ := measurePreserving_gaussianNoise (ι := ι) hρ
  have hF : AEStronglyMeasurable (f ∘ noisy ρ) (γ.prod γ) := hf.comp_measurePreserving hΦ
  have hU := hf.gaussianNoiseOp hρ
  have hpt (z : ι → ℝ) : ‖gaussianNoiseOp ρ f z‖ₑ ≤ ∫⁻ y, ‖(f ∘ noisy ρ) (z, y)‖ₑ ∂γ :=
    enorm_integral_le_lintegral_enorm _
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLpNorm_exponent_top hU, eLpNorm_exponent_top hf]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    have hb := hΦ.quasiMeasurePreserving.ae (ae_le_eLpNormEssSup (f := f))
    filter_upwards [Measure.ae_ae_of_ae_prod hb] with z hz
    refine (hpt z).trans ((lintegral_mono_ae hz).trans ?_)
    rw [lintegral_const, measure_univ, mul_one]
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hptop hp
  have hq0 : 0 < p.toReal := zero_lt_one.trans_le hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hU,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf]
  gcongr ?_ ^ _
  calc ∫⁻ z, ‖gaussianNoiseOp ρ f z‖ₑ ^ p.toReal ∂γ
      ≤ ∫⁻ z, ∫⁻ y, ‖(f ∘ noisy ρ) (z, y)‖ₑ ^ p.toReal ∂γ ∂γ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hF.prodMk_left] with z hz
        calc ‖gaussianNoiseOp ρ f z‖ₑ ^ p.toReal
            ≤ (∫⁻ y, ‖(f ∘ noisy ρ) (z, y)‖ₑ ∂γ) ^ p.toReal := by gcongr; exact hpt z
          _ = eLpNorm' (fun y => (f ∘ noisy ρ) (z, y)) 1 γ ^ p.toReal := by
            rw [eLpNorm'_eq_lintegral_enorm]
            simp only [ENNReal.rpow_one, div_one]
          _ ≤ eLpNorm' (fun y => (f ∘ noisy ρ) (z, y)) p.toReal γ ^ p.toReal := by
            gcongr
            exact eLpNorm'_le_eLpNorm'_of_exponent_le one_pos hq γ hz
          _ = ∫⁻ y, ‖(f ∘ noisy ρ) (z, y)‖ₑ ^ p.toReal ∂γ :=
            (lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0).symm
    _ = ∫⁻ q, ‖(f ∘ noisy ρ) q‖ₑ ^ p.toReal ∂γ.prod γ :=
        (lintegral_prod _ (hF.enorm.pow_const _)).symm
    _ = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂γ := hΦ.lintegral_comp' (hf.enorm.pow_const _)

/-- The noise operator maps `Lᵖ(γⁿ)` to itself for `1 ≤ p ≤ ∞` and `|ρ| ≤ 1`. -/
theorem _root_.MeasureTheory.MemLp.gaussianNoiseOp {ρ : ℝ} (hρ : |ρ| ≤ 1) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : (ι → ℝ) → ℝ} (hf : MemLp f p (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    MemLp (gaussianNoiseOp ρ f) p (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  memLp_iff.2 ((eLpNorm_gaussianNoiseOp_le hρ hp hf.aestronglyMeasurable).trans_lt
    (memLp_iff.1 hf))

/-- **The noise operator on linear functions**, the linear case of
[O'Donnell, Fact 11.13][ODonnell2014] (Exercise 11.3): `U_ρ (a ⬝ᵥ ·) z = ρ (a ⬝ᵥ z)`, since the
noise has mean `0`. -/
theorem gaussianNoiseOp_dotProduct (ρ : ℝ) (a z : ι → ℝ) :
    gaussianNoiseOp ρ (fun x => a ⬝ᵥ x) z = ρ * (a ⬝ᵥ z) := by
  set γ := Measure.pi fun _ : ι => gaussianReal 0 1
  have hlaw := pi_gaussianReal_map_dotProduct a
  have hD : Measurable fun x : ι → ℝ => a ⬝ᵥ x := by fun_prop
  have hmean : ∫ x, a ⬝ᵥ x ∂γ = 0 := by
    have h := integral_map (μ := γ) hD.aemeasurable (f := id) aestronglyMeasurable_id
    rw [hlaw] at h
    simp only [id_eq, integral_id_gaussianReal] at h
    exact h.symm
  have hexp (g : ι → ℝ) : a ⬝ᵥ (fun i => ρ * z i + √(1 - ρ ^ 2) * g i) =
      ρ * (a ⬝ᵥ z) + √(1 - ρ ^ 2) * (a ⬝ᵥ g) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [gaussianNoiseOp, hexp]
  rw [integral_add (integrable_const _) ((integrable_dotProduct_pi_gaussianReal a).const_mul _),
    integral_const, integral_const_mul, hmean, probReal_univ, smul_eq_mul, one_mul, mul_zero,
    add_zero]

end ProbabilityTheory
