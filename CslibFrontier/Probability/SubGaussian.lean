/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Moments/SubGaussian.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exponential moments of sub-Gaussian variables and empirical means

Two facts about sub-Gaussian moment-generating functions (Mathlib's `HasSubgaussianMGF`).

* If `X` is sub-Gaussian with variance proxy `c` and `2 s c < 1`, then
  `𝔼 exp (s X²) ≤ 1 / √(1 - 2 s c)`. The proof writes `exp (s y²)` as the moment-generating
  function of a standard Gaussian `g` at `√(2 s) y`, exchanges the two expectations and bounds
  `𝔼 exp (√(2 s) g X)` by the sub-Gaussian estimate; the remaining factor is the Gaussian
  integral `𝔼 exp (s c g²) = 1 / √(1 - 2 s c)`.
* **Hoeffding's lemma for an empirical mean**: for `m > 0` independent samples from `D` and `f`
  with values in `[0, 1]`, `∫ f ∂D - (∑ i, f (S i)) / m` is sub-Gaussian with variance proxy
  `1 / (4 m)` under `Measure.pi` [Hoeffding1963].

Together, at `s = 2 (m - 1)`, they bound `𝔼 exp (2 (m - 1) Δ²)` by `√m` for the deviation `Δ`
of an empirical mean; this is the exponential-moment step of McAllester's PAC-Bayes bound, where
[ShalevShwartzBenDavid2014, Section 31.1 and Exercise 31.1] uses the weaker bound `m`.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.lintegral_exp_mul_sq_le`: the exponential moment of `s X²`.
* `Cslib.Probability.hasSubgaussianMGF_integral_sub_sum_div`: the empirical mean of bounded
  i.i.d. samples is sub-Gaussian about its expectation.

## References

* [W. Hoeffding, *Probability inequalities for sums of bounded random variables*][Hoeffding1963]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- The Gaussian integral `𝔼 exp (a g²) = 1 / √(1 - 2a)` for a standard Gaussian `g` and
`a < 1 / 2`. -/
private theorem lintegral_exp_mul_sq_gaussianReal {a : ℝ} (ha : a < 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a * x ^ 2)) ∂gaussianReal 0 1 =
      ENNReal.ofReal (Real.sqrt (1 - 2 * a))⁻¹ := by
  have hb : 0 < 1 / 2 - a := by linarith
  have hpt (x : ℝ) : gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (a * x ^ 2)) =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - a) * x ^ 2)) := by
    have hexp : -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) + a * x ^ 2 = -(1 / 2 - a) * x ^ 2 := by
      push_cast
      ring
    rw [gaussianPDF, gaussianPDFReal, ← ENNReal.ofReal_mul (by positivity), mul_assoc,
      ← Real.exp_add, hexp, NNReal.coe_one, mul_one]
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) (by fun_prop)]
  simp only [Pi.mul_apply, hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq hb).const_mul _)
    (ae_of_all _ fun _ => by positivity), integral_const_mul, integral_gaussian]
  congr 1
  have h2 : (0 : ℝ) < 1 - 2 * a := by linarith
  rw [show Real.pi / (1 / 2 - a) = 2 * Real.pi / (1 - 2 * a) by
      rw [div_eq_div_iff hb.ne' h2.ne']; ring,
    Real.sqrt_div' _ h2.le]
  have : 0 < Real.sqrt (2 * Real.pi) := by positivity
  field_simp

/-- **The exponential moment of a square**: if `X` is sub-Gaussian with variance proxy `c` under
a probability measure, then `𝔼 exp (s X²) ≤ 1 / √(1 - 2 s c)` whenever `0 ≤ s` and `2 s c < 1`.
The proof integrates the sub-Gaussian bound against a standard Gaussian. -/
theorem HasSubgaussianMGF.lintegral_exp_mul_sq_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    {s : ℝ} (hs : 0 ≤ s) (hsc : 2 * s * c < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω ^ 2)) ∂μ ≤
      ENNReal.ofReal (Real.sqrt (1 - 2 * s * c))⁻¹ := by
  set t := Real.sqrt (2 * s)
  have ht : t ^ 2 = 2 * s := Real.sq_sqrt (by positivity)
  -- `exp (s y²)` is the moment-generating function of a standard Gaussian at `t y`.
  have hgauss (y : ℝ) : ENNReal.ofReal (Real.exp (s * y ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (t * y * x)) ∂gaussianReal 0 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal _)
      (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (t * y)
    simp only [mgf] at h
    rw [h]
    congr 2
    rw [mul_pow, ht]
    push_cast
    ring
  have hmeas : AEMeasurable (Function.uncurry fun ω x => ENNReal.ofReal (Real.exp (t * X ω * x)))
      (μ.prod (gaussianReal 0 1)) :=
    (Real.measurable_exp.comp_aemeasurable
      ((hX.aemeasurable.comp_fst.const_mul t).mul measurable_snd.aemeasurable)).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω ^ 2)) ∂μ
      = ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (Real.exp (t * X ω * x)) ∂gaussianReal 0 1 ∂μ :=
        lintegral_congr fun ω => hgauss (X ω)
    _ = ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (Real.exp (t * x * X ω)) ∂μ ∂gaussianReal 0 1 := by
        rw [lintegral_lintegral_swap hmeas]
        refine lintegral_congr fun x => lintegral_congr fun ω => ?_
        rw [mul_right_comm]
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp ((s * c) * x ^ 2)) ∂gaussianReal 0 1 := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hX.integrable_exp_mul _)
          (ae_of_all _ fun _ => (Real.exp_pos _).le)]
        refine ENNReal.ofReal_le_ofReal ((hX.mgf_le (t * x)).trans_eq ?_)
        congr 1
        rw [mul_pow, ht]
        ring
    _ = ENNReal.ofReal (Real.sqrt (1 - 2 * s * c))⁻¹ := by
        rw [lintegral_exp_mul_sq_gaussianReal (by linarith), mul_assoc]

end ProbabilityTheory

namespace Cslib.Probability

open ProbabilityTheory

/-- **Hoeffding's lemma for an empirical mean** [Hoeffding1963]: for `m > 0` independent samples
`S` from a probability measure `D` and a measurable `f` with values in `[0, 1]`, the deviation
`∫ f ∂D - (∑ i, f (S i)) / m` of the empirical mean is sub-Gaussian with variance proxy
`1 / (4 m)`. -/
theorem hasSubgaussianMGF_integral_sub_sum_div {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {f : Z → ℝ} (hf : Measurable f) (hf01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) :
    HasSubgaussianMGF (fun S : Fin m → Z => ∫ z, f z ∂D - (∑ i, f (S i)) / m) (4 * m : ℝ≥0)⁻¹
      (Measure.pi fun _ => D) := by
  have hcoord (i : Fin m) : HasSubgaussianMGF (fun S : Fin m → Z => ∫ z, f z ∂D - f (S i))
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (Measure.pi fun _ => D) := by
    have hmean : ∫ S, f (S i) ∂(Measure.pi fun _ : Fin m => D) = ∫ z, f z ∂D := by
      conv_rhs => rw [← (measurePreserving_eval (fun _ : Fin m => D) i).map_eq]
      rw [integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]
    have hfi : Measurable fun S : Fin m → Z => f (S i) := hf.comp (measurable_pi_apply i)
    have h := (hasSubgaussianMGF_of_mem_Icc (μ := Measure.pi fun _ : Fin m => D)
      hfi.aemeasurable (ae_of_all _ fun S => hf01 (S i))).neg
    refine h.congr (ae_of_all _ fun S => ?_)
    simp only [Pi.neg_apply, hmean, neg_sub]
  have hind : iIndepFun (fun i (S : Fin m → Z) => ∫ z, f z ∂D - f (S i))
      (Measure.pi fun _ => D) :=
    iIndepFun_pi (X := fun _ z => ∫ z, f z ∂D - f z) fun _ =>
      (measurable_const.sub hf).aemeasurable
  have hsum := (HasSubgaussianMGF.sum_of_iIndepFun hind
    (s := Finset.univ) fun i _ => hcoord i).const_mul (1 / (m : ℝ))
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hc : (4 * m : ℝ≥0)⁻¹ =
      .mk ((1 / (m : ℝ)) ^ 2) (sq_nonneg _) * ∑ _i : Fin m, (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_zero,
      nnnorm_one]
    ext1
    push_cast [NNReal.coe_mk]
    field_simp
    ring
  convert hsum using 1
  · funext S
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  · exact hc

end Cslib.Probability
