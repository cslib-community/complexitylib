/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, addition to `Mathlib/Probability/Distributions/Cauchy.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Probability.Distributions.Cauchy
import CslibFrontier.Foundations.MeasureTheory.Group.ConvolutionDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Independence.Basic

/-!
# Scaling and 1-stability of Cauchy distributions

This module proves linear scaling and convolution additivity for Mathlib's `cauchyMeasure` and
derives the 1-stability property of independent standard Cauchy coordinates: for any weight
vector `w : ι → ℝ`, the linear combination `a ↦ w ⬝ᵥ a` under
`Measure.pi fun _ : ι => cauchyMeasure 0 1` has distribution `cauchyMeasure 0 (∑ i, ‖w i‖₊)`.

The convolution of two Cauchy densities is computed via elementary partial fractions on `ℝ`
together with the fundamental theorem of calculus on `[-R, R]` as `R → ∞`, avoiding complex
contour integration.

## Main results

* `ProbabilityTheory.cauchyMeasure_map_const_mul`: scaling of a Cauchy distribution.
* `ProbabilityTheory.cauchyMeasure_map_add`: convolution of centered Cauchy distributions.
* `ProbabilityTheory.pi_cauchyMeasure_map_dotProduct`: 1-stability of independent standard Cauchy
  coordinates.
-/

public section

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-! ### Scaling -/

/-- Rescaling the argument of `cauchyPDFReal` transforms location and scale linearly. -/
private theorem cauchyPDFReal_inv_mul {x₀ : ℝ} {γ : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    |c⁻¹| * cauchyPDFReal x₀ γ (c⁻¹ * x) = cauchyPDFReal (c * x₀) (‖c‖₊ * γ) x := by
  simp only [cauchyPDFReal_def, NNReal.coe_mul, coe_nnnorm]
  have hc0 : 0 < |c| := abs_pos.2 hc
  rw [abs_inv]
  have hsq : (c⁻¹ * x - x₀) ^ 2 + (γ : ℝ) ^ 2 = ((x - c * x₀) ^ 2 + (|c| * γ) ^ 2) / c ^ 2 := by
    rw [mul_pow, sq_abs]
    field_simp [hc]
  rw [hsq, inv_div]
  calc |c|⁻¹ * (π⁻¹ * γ * (c ^ 2 / ((x - c * x₀) ^ 2 + (|c| * γ) ^ 2)))
      = π⁻¹ * (|c| * γ) * ((x - c * x₀) ^ 2 + (|c| * γ) ^ 2)⁻¹ * (c ^ 2 / |c| ^ 2) := by
          field_simp [hc0.ne']
    _ = π⁻¹ * (|c| * γ) * ((x - c * x₀) ^ 2 + (|c| * γ) ^ 2)⁻¹ := by
          rw [sq_abs, div_self (pow_ne_zero 2 hc), mul_one]

/-- The image of `cauchyMeasure x₀ γ` under scalar multiplication `(c * ·)` is
`cauchyMeasure (c * x₀) (‖c‖₊ * γ)`. -/
theorem cauchyMeasure_map_const_mul (x₀ : ℝ) (γ : ℝ≥0) (c : ℝ) :
    (cauchyMeasure x₀ γ).map (c * ·) = cauchyMeasure (c * x₀) (‖c‖₊ * γ) := by
  by_cases hγ : γ = 0
  · rw [hγ, cauchyMeasure_zero_scale, mul_zero, cauchyMeasure_zero_scale,
      Measure.map_dirac' (by fun_prop)]
  by_cases hc : c = 0
  · simp only [hc, zero_mul, nnnorm_zero, cauchyMeasure_zero_scale]
    rw [Measure.map_const, measure_univ, one_smul]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e c⁻¹ x := fun x => by
    suffices HasDerivAt (fun y : ℝ => c⁻¹ * y) (c⁻¹ * 1) x by
      simpa only [mul_one, e, Homeomorph.toMeasurableEquiv_coe,
        Homeomorph.mulLeft₀_symm_apply] using this
    exact HasDerivAt.const_mul c⁻¹ (hasDerivAt_id x)
  have hγ' : ‖c‖₊ * γ ≠ 0 := mul_ne_zero (nnnorm_ne_zero_iff.2 hc) hγ
  change (cauchyMeasure x₀ γ).map e.symm = cauchyMeasure (c * x₀) (‖c‖₊ * γ)
  ext s hs
  rw [cauchyMeasure_of_scale_ne_zero _ hγ, cauchyMeasure_of_scale_ne_zero _ hγ']
  change (volume.withDensity fun x => ENNReal.ofReal (cauchyPDFReal x₀ γ x)).map e.symm s =
    (volume.withDensity fun x => ENNReal.ofReal (cauchyPDFReal (c * x₀) (‖c‖₊ * γ) x)) s
  have heq := e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs he'
    (ae_of_all _ fun y => (cauchyPDF_pos x₀ hγ y).le) (integrable_cauchyPDFReal x₀)
  rw [heq, withDensity_apply' _ s, ← ofReal_integral_eq_lintegral_ofReal
    ((integrable_cauchyPDFReal _).restrict) (ae_of_all _ fun y => (cauchyPDF_pos _ hγ' y).le),
    ← integral_indicator hs, ← setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1
    refine setIntegral_congr_fun hs fun x hx => ?_
    simp only [Set.indicator_of_mem hx, e, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.mulLeft₀_symm_apply]
    exact cauchyPDFReal_inv_mul hc x
  · intro x hx
    exact Set.indicator_of_notMem hx _

/-! ### Convolution of centered Cauchy distributions -/

/-- `cauchyPDFReal 0 γ y` is bounded uniformly by `(π * γ)⁻¹`. -/
private theorem cauchyPDFReal_le {γ : ℝ≥0} (hγ : γ ≠ 0) (y : ℝ) :
    cauchyPDFReal 0 γ y ≤ (π * γ)⁻¹ := by
  have hγpos : (0 : ℝ) < γ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hγ)
  rw [cauchyPDFReal_def, sub_zero]
  have hinv : (y ^ 2 + (γ : ℝ) ^ 2)⁻¹ ≤ ((γ : ℝ) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith [sq_nonneg y])
  calc π⁻¹ * (γ : ℝ) * (y ^ 2 + (γ : ℝ) ^ 2)⁻¹
      ≤ π⁻¹ * (γ : ℝ) * ((γ : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (π * γ)⁻¹ := by field_simp [pi_ne_zero, hγpos.ne']

/-- The product of two centered Cauchy densities is integrable on `ℝ`. -/
private theorem integrable_cauchyPDFReal_mul {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) (x : ℝ) :
    Integrable (fun t : ℝ => cauchyPDFReal 0 a t * cauchyPDFReal 0 b (x - t)) := by
  refine Integrable.mono' ((integrable_cauchyPDFReal 0 (γ := a)).const_mul (π * ↑b)⁻¹)
    (by fun_prop) (ae_of_all _ fun t => ?_)
  have ha0 : 0 ≤ cauchyPDFReal 0 a t := (cauchyPDF_pos 0 ha t).le
  have hb0 : 0 ≤ cauchyPDFReal 0 b (x - t) := (cauchyPDF_pos 0 hb (x - t)).le
  rw [Real.norm_of_nonneg (mul_nonneg ha0 hb0), mul_comm]
  exact mul_le_mul_of_nonneg_right (cauchyPDFReal_le hb (x - t)) ha0

/-- Limit as `|t| → ∞` of `t / (t ^ 2 + a ^ 2)` is `0`. -/
private theorem tendsto_div_sq_add_atTop_atBot {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t / (t ^ 2 + a ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => t / (t ^ 2 + a ^ 2)) atBot (𝓝 0) := by
  have hrew : ∀ t : ℝ, t ≠ 0 → t / (t ^ 2 + a ^ 2) = t⁻¹ / (1 + a ^ 2 * (t⁻¹) ^ 2) := by
    intro t ht
    field_simp [ht]
  have htop : (fun t : ℝ => t / (t ^ 2 + a ^ 2)) =ᶠ[atTop]
      fun t => t⁻¹ / (1 + a ^ 2 * (t⁻¹) ^ 2) :=
    (eventually_gt_atTop (0 : ℝ)).mono fun t ht => hrew t ht.ne'
  have hbot : (fun t : ℝ => t / (t ^ 2 + a ^ 2)) =ᶠ[atBot]
      fun t => t⁻¹ / (1 + a ^ 2 * (t⁻¹) ^ 2) :=
    (eventually_lt_atBot (0 : ℝ)).mono fun t ht => hrew t ht.ne
  have hfun : Tendsto (fun u : ℝ => u / (1 + a ^ 2 * u ^ 2)) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun u : ℝ => u / (1 + a ^ 2 * u ^ 2)) 0 := by
      fun_prop (disch := norm_num)
    simpa using hcont.tendsto
  exact ⟨(hfun.comp tendsto_inv_atTop_zero).congr' htop.symm,
    (hfun.comp tendsto_inv_atBot_zero).congr' hbot.symm⟩

/-- Convolution identity in the repeated-root case `x = 0` and `a = b`. -/
private theorem integral_cauchyPDFReal_mul_self_zero {a : ℝ≥0} (ha : a ≠ 0) :
    ∫ t : ℝ, cauchyPDFReal 0 a t * cauchyPDFReal 0 a (0 - t) = cauchyPDFReal 0 (a + a) 0 := by
  have ha' : (0 : ℝ) < a := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ha)
  have hint := integrable_cauchyPDFReal_mul ha ha 0
  have htendL := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hmain : Integrable (fun t : ℝ => (2 * π * (a : ℝ))⁻¹ * cauchyPDFReal 0 a t) :=
    (integrable_cauchyPDFReal 0).const_mul _
  have htendM := intervalIntegral_tendsto_integral hmain tendsto_neg_atTop_atBot tendsto_id
  have hM : ∫ t : ℝ, (2 * π * (a : ℝ))⁻¹ * cauchyPDFReal 0 a t = cauchyPDFReal 0 (a + a) 0 := by
    rw [integral_const_mul, integral_cauchyPDFReal_eq_one 0 ha, mul_one, cauchyPDFReal_def]
    simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), NNReal.coe_add, zero_add]
    field_simp [pi_ne_zero, ha'.ne']
    ring
  rw [hM] at htendM
  have hsplit : ∀ R : ℝ,
      ∫ t in (-R)..R, cauchyPDFReal 0 a t * cauchyPDFReal 0 a (0 - t) =
        (∫ t in (-R)..R, (2 * π * (a : ℝ))⁻¹ * cauchyPDFReal 0 a t) +
          (2 * π ^ 2)⁻¹ * (R / (R ^ 2 + (a : ℝ) ^ 2) - (-R) / ((-R) ^ 2 + (a : ℝ) ^ 2)) := by
    intro R
    set g : ℝ → ℝ := fun t => (2 * π ^ 2)⁻¹ * (((a : ℝ) ^ 2 - t ^ 2) / (t ^ 2 + a ^ 2) ^ 2)
    have hderiv : ∀ t ∈ uIcc (-R) R,
        HasDerivAt (fun s : ℝ => (2 * π ^ 2)⁻¹ * (s / (s ^ 2 + (a : ℝ) ^ 2))) (g t) t := by
      intro t _
      have hden : t ^ 2 + (a : ℝ) ^ 2 ≠ 0 := by positivity
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2 + (a : ℝ) ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t).add_const ((a : ℝ) ^ 2)
      have hd := ((hasDerivAt_id t).div hsq hden).const_mul (2 * π ^ 2)⁻¹
      exact hd.congr_deriv (by dsimp only [g]; rw [id_eq]; field_simp [hden]; ring)
    have hg_int : IntervalIntegrable g volume (-R) R := by
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul ((continuous_const.sub (continuous_pow 2)).div
        (((continuous_pow 2).add continuous_const).pow 2) fun t => by positivity)
    have hm_int : IntervalIntegrable (fun t => (2 * π * (a : ℝ))⁻¹ * cauchyPDFReal 0 a t)
        volume (-R) R :=
      hmain.intervalIntegrable
    have hfun : (fun t : ℝ => cauchyPDFReal 0 a t * cauchyPDFReal 0 a (0 - t)) =
        fun t => (2 * π * (a : ℝ))⁻¹ * cauchyPDFReal 0 a t + g t := by
      funext t
      simp only [cauchyPDFReal_def, sub_zero, zero_sub, neg_sq, g]
      have hden : t ^ 2 + (a : ℝ) ^ 2 ≠ 0 := by positivity
      field_simp [pi_ne_zero, ha'.ne', hden]
      ring
    rw [hfun, intervalIntegral.integral_add hm_int hg_int,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hg_int, mul_sub]
  obtain ⟨htop, hbot⟩ := tendsto_div_sq_add_atTop_atBot ha'
  have hlimD : Tendsto (fun R : ℝ =>
      (2 * π ^ 2)⁻¹ * (R / (R ^ 2 + (a : ℝ) ^ 2) - (-R) / ((-R) ^ 2 + (a : ℝ) ^ 2)))
      atTop (𝓝 0) := by
    have hz : (2 * π ^ 2)⁻¹ * ((0 : ℝ) - 0) = 0 := by ring
    have hneg : Tendsto (fun R : ℝ => (-R) / ((-R) ^ 2 + (a : ℝ) ^ 2)) atTop (𝓝 0) :=
      hbot.comp tendsto_neg_atTop_atBot
    have hlim := (htop.sub hneg).const_mul (2 * π ^ 2)⁻¹
    simpa only [hz] using hlim
  have htendR : Tendsto (fun R : ℝ =>
      ∫ t in (-R)..R, cauchyPDFReal 0 a t * cauchyPDFReal 0 a (0 - t))
      atTop (𝓝 (cauchyPDFReal 0 (a + a) 0)) := by
    have := htendM.add hlimD
    rw [add_zero] at this
    exact this.congr fun R => (hsplit R).symm
  exact tendsto_nhds_unique htendL htendR

/-- Limit as `|t| → ∞` of `log (t ^ 2 + a ^ 2) - log ((t - x) ^ 2 + b ^ 2)` is `0`. -/
private theorem tendsto_log_sub_log_sq_atTop_atBot {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.log (t ^ 2 + a ^ 2) - Real.log ((t - x) ^ 2 + b ^ 2))
      atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => Real.log (t ^ 2 + a ^ 2) - Real.log ((t - x) ^ 2 + b ^ 2))
        atBot (𝓝 0) := by
  have hrew : ∀ t : ℝ, t ≠ 0 →
      Real.log (t ^ 2 + a ^ 2) - Real.log ((t - x) ^ 2 + b ^ 2) =
        Real.log ((1 + a ^ 2 * (t⁻¹) ^ 2) / ((1 - x * t⁻¹) ^ 2 + b ^ 2 * (t⁻¹) ^ 2)) := by
    intro t ht
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp [ht]
  have htop_eq : (fun t : ℝ => Real.log (t ^ 2 + a ^ 2) - Real.log ((t - x) ^ 2 + b ^ 2)) =ᶠ[atTop]
      fun t => Real.log ((1 + a ^ 2 * (t⁻¹) ^ 2) / ((1 - x * t⁻¹) ^ 2 + b ^ 2 * (t⁻¹) ^ 2)) :=
    (eventually_gt_atTop (0 : ℝ)).mono fun t ht => hrew t ht.ne'
  have hbot_eq : (fun t : ℝ => Real.log (t ^ 2 + a ^ 2) - Real.log ((t - x) ^ 2 + b ^ 2)) =ᶠ[atBot]
      fun t => Real.log ((1 + a ^ 2 * (t⁻¹) ^ 2) / ((1 - x * t⁻¹) ^ 2 + b ^ 2 * (t⁻¹) ^ 2)) :=
    (eventually_lt_atBot (0 : ℝ)).mono fun t ht => hrew t ht.ne
  have hfun : Tendsto (fun u : ℝ =>
      Real.log ((1 + a ^ 2 * u ^ 2) / ((1 - x * u) ^ 2 + b ^ 2 * u ^ 2))) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt
        (fun u : ℝ => Real.log ((1 + a ^ 2 * u ^ 2) / ((1 - x * u) ^ 2 + b ^ 2 * u ^ 2))) 0 := by
      refine ContinuousAt.log ?_ (by norm_num)
      fun_prop (disch := norm_num)
    simpa using hcont.tendsto
  exact ⟨(hfun.comp tendsto_inv_atTop_zero).congr' htop_eq.symm,
    (hfun.comp tendsto_inv_atBot_zero).congr' hbot_eq.symm⟩

/-- Convolution of two centered Cauchy densities equals the summed-scale Cauchy density. -/
private theorem integral_cauchyPDFReal_mul {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) (x : ℝ) :
    ∫ t : ℝ, cauchyPDFReal 0 a t * cauchyPDFReal 0 b (x - t) = cauchyPDFReal 0 (a + b) x := by
  by_cases hxa : x = 0 ∧ a = b
  · rw [hxa.1, hxa.2]
    exact integral_cauchyPDFReal_mul_self_zero hb
  have ha' : (0 : ℝ) < a := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ha)
  have hb' : (0 : ℝ) < b := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hb)
  have hdiff : x ≠ 0 ∨ (a : ℝ) ≠ b := by
    by_contra h
    push Not at h
    exact hxa ⟨h.1, NNReal.coe_injective h.2⟩
  have h1 : 0 < x ^ 2 + ((a : ℝ) + b) ^ 2 := by positivity
  have h2 : 0 < x ^ 2 + ((a : ℝ) - b) ^ 2 := by
    rcases hdiff with hx | hab
    · positivity
    · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero (sub_ne_zero.2 hab))
  set Δ : ℝ := (x ^ 2 + ((a : ℝ) + b) ^ 2) * (x ^ 2 + ((a : ℝ) - b) ^ 2)
  have hΔ : 0 < Δ := mul_pos h1 h2
  set B : ℝ := (x ^ 2 + (b : ℝ) ^ 2 - (a : ℝ) ^ 2) / Δ
  set D : ℝ := (x ^ 2 + (a : ℝ) ^ 2 - (b : ℝ) ^ 2) / Δ
  set A : ℝ := (2 * x) / Δ
  have hint := integrable_cauchyPDFReal_mul ha hb x
  have htendL := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hca : Integrable (fun t : ℝ => ((b : ℝ) * B / π) * cauchyPDFReal 0 a t) :=
    (integrable_cauchyPDFReal 0).const_mul _
  have hcb : Integrable (fun t : ℝ => ((a : ℝ) * D / π) * cauchyPDFReal 0 b (x - t)) :=
    ((integrable_cauchyPDFReal 0).comp_sub_left x).const_mul _
  have hcb_int : ∫ t : ℝ, cauchyPDFReal 0 b (x - t) = 1 := by
    rw [integral_sub_left_eq_self (f := cauchyPDFReal 0 b), integral_cauchyPDFReal_eq_one 0 hb]
  have hM : ∫ t : ℝ, (((b : ℝ) * B / π) * cauchyPDFReal 0 a t +
      ((a : ℝ) * D / π) * cauchyPDFReal 0 b (x - t)) = cauchyPDFReal 0 (a + b) x := by
    rw [integral_add hca hcb, integral_const_mul, integral_const_mul,
      integral_cauchyPDFReal_eq_one 0 ha, hcb_int, mul_one, mul_one, cauchyPDFReal_def,
      sub_zero, NNReal.coe_add]
    dsimp only [B, D, Δ]
    field_simp [pi_ne_zero, h1.ne', h2.ne']
    ring
  have htendM : Tendsto (fun R : ℝ => ∫ t in (-R)..R,
        (((b : ℝ) * B / π) * cauchyPDFReal 0 a t +
          ((a : ℝ) * D / π) * cauchyPDFReal 0 b (x - t)))
      atTop (𝓝 (cauchyPDFReal 0 (a + b) x)) := by
    have hm := intervalIntegral_tendsto_integral (hca.add hcb) tendsto_neg_atTop_atBot tendsto_id
    simpa only [Pi.add_apply, id_eq, hM] using hm
  set cLog : ℝ := (a : ℝ) * b * A / (2 * π ^ 2)
  set fLog : ℝ → ℝ := fun t => cLog * (Real.log (t ^ 2 + (a : ℝ) ^ 2) -
    Real.log ((t - x) ^ 2 + (b : ℝ) ^ 2))
  set gLog : ℝ → ℝ := fun t => cLog * ((2 * t) / (t ^ 2 + (a : ℝ) ^ 2) -
    (2 * (t - x)) / ((t - x) ^ 2 + (b : ℝ) ^ 2))
  have hsplit : ∀ R : ℝ,
      ∫ t in (-R)..R, cauchyPDFReal 0 a t * cauchyPDFReal 0 b (x - t) =
        (∫ t in (-R)..R, (((b : ℝ) * B / π) * cauchyPDFReal 0 a t +
          ((a : ℝ) * D / π) * cauchyPDFReal 0 b (x - t))) + (fLog R - fLog (-R)) := by
    intro R
    have hderiv : ∀ t ∈ uIcc (-R) R, HasDerivAt fLog (gLog t) t := by
      intro t _
      have h1d : HasDerivAt (fun s : ℝ => Real.log (s ^ 2 + (a : ℝ) ^ 2))
          ((2 * t) / (t ^ 2 + (a : ℝ) ^ 2)) t := by
        have hpos : t ^ 2 + (a : ℝ) ^ 2 ≠ 0 := by positivity
        have hsq : HasDerivAt (fun s : ℝ => s ^ 2 + (a : ℝ) ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_pow 2 t).add_const ((a : ℝ) ^ 2)
        simpa [div_eq_mul_inv] using hsq.log hpos
      have h2d : HasDerivAt (fun s : ℝ => Real.log ((s - x) ^ 2 + (b : ℝ) ^ 2))
          ((2 * (t - x)) / ((t - x) ^ 2 + (b : ℝ) ^ 2)) t := by
        have hpos : (t - x) ^ 2 + (b : ℝ) ^ 2 ≠ 0 := by positivity
        have hsub : HasDerivAt (fun s : ℝ => s - x) 1 t := (hasDerivAt_id t).sub_const x
        have hsq : HasDerivAt (fun s : ℝ => (s - x) ^ 2 + (b : ℝ) ^ 2) (2 * (t - x)) t := by
          simpa using ((hasDerivAt_pow 2 (t - x)).comp t hsub).add_const ((b : ℝ) ^ 2)
        simpa [div_eq_mul_inv] using hsq.log hpos
      exact (h1d.sub h2d).const_mul cLog
    have hg_int : IntervalIntegrable gLog volume (-R) R := by
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul (((continuous_const.mul continuous_id).div
        ((continuous_pow 2).add continuous_const)
          fun t => (add_pos_of_nonneg_of_pos (sq_nonneg t) (pow_pos ha' 2)).ne').sub
        ((continuous_const.mul (continuous_id.sub continuous_const)).div
        (((continuous_id.sub continuous_const).pow 2).add continuous_const)
          fun t => (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hb' 2)).ne'))
    have hfun : (fun t : ℝ => cauchyPDFReal 0 a t * cauchyPDFReal 0 b (x - t)) =
        fun t => (((b : ℝ) * B / π) * cauchyPDFReal 0 a t +
          ((a : ℝ) * D / π) * cauchyPDFReal 0 b (x - t)) + gLog t := by
      funext t
      simp only [cauchyPDFReal_def, sub_zero, gLog, cLog, B, D, A, Δ]
      have hd1 : t ^ 2 + (a : ℝ) ^ 2 ≠ 0 := by positivity
      have hd2 : (x - t) ^ 2 + (b : ℝ) ^ 2 ≠ 0 := by positivity
      have hd3 : (t - x) ^ 2 + (b : ℝ) ^ 2 = (x - t) ^ 2 + (b : ℝ) ^ 2 := by ring
      rw [hd3]
      field_simp [pi_ne_zero, hd1, hd2, h1.ne', h2.ne']
      ring
    have hm_int : IntervalIntegrable (fun t : ℝ => ((b : ℝ) * B / π) * cauchyPDFReal 0 a t +
        ((a : ℝ) * D / π) * cauchyPDFReal 0 b (x - t)) volume (-R) R :=
      (hca.add hcb).intervalIntegrable
    rw [hfun, intervalIntegral.integral_add hm_int hg_int,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hg_int]
  obtain ⟨htop, hbot⟩ := tendsto_log_sub_log_sq_atTop_atBot ha' hb'
  have hfLog0 : Tendsto (fun R : ℝ => fLog R - fLog (-R)) atTop (𝓝 0) := by
    have ht1 : Tendsto fLog atTop (𝓝 0) := by
      simpa only [mul_zero] using htop.const_mul cLog
    have ht2 : Tendsto (fun R : ℝ => fLog (-R)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, fLog, mul_zero] using
        (hbot.comp tendsto_neg_atTop_atBot).const_mul cLog
    simpa only [sub_zero] using ht1.sub ht2
  have htendR : Tendsto (fun R : ℝ =>
      ∫ t in (-R)..R, cauchyPDFReal 0 a t * cauchyPDFReal 0 b (x - t))
      atTop (𝓝 (cauchyPDFReal 0 (a + b) x)) := by
    have := htendM.add hfLog0
    rw [add_zero] at this
    exact this.congr fun R => (hsplit R).symm
  exact tendsto_nhds_unique htendL htendR

/-- The sum of two independent centered Cauchy random variables is Cauchy with the sum of the
scales. -/
theorem cauchyMeasure_map_add (a b : ℝ≥0) :
    ((cauchyMeasure 0 a).prod (cauchyMeasure 0 b)).map (fun p : ℝ × ℝ => p.1 + p.2) =
      cauchyMeasure 0 (a + b) := by
  change (cauchyMeasure 0 a) ∗ (cauchyMeasure 0 b) = cauchyMeasure 0 (a + b)
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [cauchyMeasure_of_scale_ne_zero _ ha, cauchyMeasure_of_scale_ne_zero _ hb,
    cauchyMeasure_of_scale_ne_zero _ (by simp [ha]),
    MeasureTheory.conv_withDensity_eq_withDensity_lintegral (measurable_cauchyPDF 0 b)]
  congr 1 with x
  rw [lintegral_withDensity_eq_lintegral_mul (μ := volume) (measurable_cauchyPDF 0 a)
    (g := fun t => cauchyPDF 0 b (-t + x)) (by fun_prop)]
  simp only [cauchyPDF_def, ← sub_eq_neg_add]
  rw [show (cauchyPDF 0 a * fun t => ENNReal.ofReal (cauchyPDFReal 0 b (x - t))) =
      fun t => ENNReal.ofReal (cauchyPDFReal 0 a t * cauchyPDFReal 0 b (x - t)) from
        funext fun t => (ENNReal.ofReal_mul (cauchyPDF_pos 0 ha t).le).symm,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_cauchyPDFReal_mul ha hb x)
      (ae_of_all _ fun t => mul_nonneg (cauchyPDF_pos 0 ha t).le (cauchyPDF_pos 0 hb (x - t)).le),
    integral_cauchyPDFReal_mul ha hb x]

/-! ### 1-stability of independent standard Cauchy coordinates -/

/-- Partial-sum 1-stability under independent standard Cauchy coordinates. -/
private theorem pi_cauchyMeasure_map_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) (s : Finset ι) :
    (Measure.pi fun _ : ι => cauchyMeasure 0 1).map (fun a : ι → ℝ => ∑ i ∈ s, w i * a i) =
      cauchyMeasure 0 (∑ i ∈ s, ‖w i‖₊) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, cauchyMeasure_zero_scale]
    rw [Measure.map_const, measure_univ, one_smul]
  | insert j s hj ih =>
    have hrew : (fun a : ι → ℝ => ∑ i ∈ insert j s, w i * a i) =
        (fun p : ℝ × ℝ => p.1 + p.2) ∘
          fun a : ι → ℝ => (w j * a j, ∑ i ∈ s, w i * a i) := by
      funext a
      rw [Function.comp_apply, Finset.sum_insert hj]
    have hm1 : Measurable fun a : ι → ℝ => w j * a j :=
      measurable_const.mul (measurable_pi_apply j)
    have hm2 : Measurable fun a : ι → ℝ => ∑ i ∈ s, w i * a i :=
      Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
    have hind_coord : iIndepFun (fun i (a : ι → ℝ) => a i)
        (Measure.pi fun _ : ι => cauchyMeasure 0 1) :=
      iIndepFun_pi (X := fun _ x => x) fun _ => aemeasurable_id
    have hind_sets := hind_coord.indepFun_finset {j} s
      (by simpa only [Finset.disjoint_singleton_left] using hj)
      fun _ => measurable_pi_apply _
    have hcomp : IndepFun (fun a : ι → ℝ => w j * a j) (fun a : ι → ℝ => ∑ i ∈ s, w i * a i)
        (Measure.pi fun _ : ι => cauchyMeasure 0 1) := by
      have hf : (fun a : ι → ℝ => w j * a j) =
          (fun f : {i // i ∈ ({j} : Finset ι)} → ℝ => w j * f ⟨j, Finset.mem_singleton_self j⟩) ∘
            Finset.restrict {j} := by
        funext a; rfl
      have hg : (fun a : ι → ℝ => ∑ i ∈ s, w i * a i) =
          (fun f : {i // i ∈ s} → ℝ => ∑ i : s, w i.1 * f i) ∘ Finset.restrict s := by
        funext a
        dsimp only [Function.comp_apply, Finset.restrict]
        exact (Finset.sum_coe_sort s (fun i => w i * a i)).symm
      rw [hf, hg]
      exact hind_sets.comp
        (measurable_const.mul (measurable_pi_apply _))
        (Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i))
    have hmap1 : (Measure.pi fun _ : ι => cauchyMeasure 0 1).map (fun a : ι → ℝ => w j * a j) =
        cauchyMeasure 0 ‖w j‖₊ := by
      have hm_eval :
          (Measure.pi fun _ : ι => cauchyMeasure 0 1).map ((w j * ·) ∘ Function.eval j) =
          ((Measure.pi fun _ : ι => cauchyMeasure 0 1).map (Function.eval j)).map (w j * ·) :=
        (Measure.map_map (measurable_const.mul measurable_id) (measurable_pi_apply j)).symm
      change (Measure.pi fun _ : ι => cauchyMeasure 0 1).map ((w j * ·) ∘ Function.eval j) = _
      rw [hm_eval, (measurePreserving_eval (fun _ : ι => cauchyMeasure 0 1) j).map_eq,
        cauchyMeasure_map_const_mul, mul_zero, mul_one]
    rw [hrew, ← Measure.map_map (by fun_prop) (hm1.prodMk hm2),
      (indepFun_iff_map_prod_eq_prod_map_map hm1.aemeasurable hm2.aemeasurable).1 hcomp, hmap1, ih,
      cauchyMeasure_map_add, Finset.sum_insert hj]

/-- **1-stability of independent standard Cauchy coordinates**: for any weight vector `w : ι → ℝ`,
`w ⬝ᵥ a` under `Measure.pi fun _ : ι => cauchyMeasure 0 1` has distribution
`cauchyMeasure 0 (∑ i, ‖w i‖₊)`. -/
theorem pi_cauchyMeasure_map_dotProduct {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    (Measure.pi fun _ : ι => cauchyMeasure 0 1).map (w ⬝ᵥ ·) =
      cauchyMeasure 0 (∑ i, ‖w i‖₊) := by
  simpa only [dotProduct] using pi_cauchyMeasure_map_sum w Finset.univ

end ProbabilityTheory
