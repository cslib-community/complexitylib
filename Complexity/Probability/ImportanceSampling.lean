/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.MedianOfMeans
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Importance sampling for differences of expectations

A nonnegative likelihood ratio `W` changes the behavior law `P` into the target
law `Q`. The observed score is `L * (1 - W)`, not a separately specified random
variable with assumed moments. Its expectation and variance bound are proved
from the change of measure and the bounded observed loss. Both laws may live
on arbitrary measurable spaces.

## Main definitions

* `importanceScore`: the observable importance-weighted difference score.
* `densityChiSquared`: the squared likelihood-ratio discrepancy.

## Main results

* `importanceScore_integral`: unbiasedness for the actual difference of costs.
* `importanceScore_variance_le`: the derived squared-range/divergence bound.
* `importanceScore_confidence`: median-of-means confidence for independent logs.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Cslib.Probability
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The score computed from an observed loss and its logged likelihood ratio. -/
@[expose] def importanceScore (L W : Ω → ℝ) (z : Ω) : ℝ := L z * (1 - W z)

/-- Chi-squared discrepancy when `W` is a density of the target law relative
to the behavior law. Finiteness is expressed by `MemLp W 2 P`. -/
@[expose] def densityChiSquared (P : Measure Ω) (W : Ω → ℝ) : ℝ :=
  ∫ z, (1 - W z) ^ 2 ∂P

/-- The discrepancy is nonnegative, including the totalized nonintegrable case. -/
theorem densityChiSquared_nonneg (P : Measure Ω) (W : Ω → ℝ) :
    0 ≤ densityChiSquared P W := integral_nonneg fun _ => sq_nonneg _

/-- A bounded loss times a square-integrable density difference is square integrable. -/
theorem importanceScore_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    {L W : Ω → ℝ} (hL : Measurable L) (hW : MemLp W 2 P) {B : ℝ}
    (hbound : ∀ᵐ z ∂P, |L z| ≤ B) : MemLp (importanceScore L W) 2 P := by
  have hZ : MemLp (fun z => 1 - W z) 2 P := (memLp_const 1).sub hW
  apply (hZ.const_mul B).mono
    (hL.aestronglyMeasurable.mul hZ.aestronglyMeasurable)
  filter_upwards [hbound] with z hz
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  exact mul_le_mul_of_nonneg_right (hz.trans (le_abs_self B)) (abs_nonneg _)

/-- The score's expectation equals behavior cost minus target cost. The only
law-matching hypothesis is the ordinary density change of measure. -/
theorem importanceScore_integral (P Q : Measure Ω) [IsProbabilityMeasure P]
    {L W : Ω → ℝ} (hL : Measurable L)
    (hWm : Measurable W) (hW : MemLp W 2 P) (hWpos : ∀ z, 0 ≤ W z)
    (hchange : P.withDensity (fun z => ENNReal.ofReal (W z)) = Q)
    {B : ℝ} (hbound : ∀ᵐ z ∂P, |L z| ≤ B) :
    ∫ z, importanceScore L W z ∂P = (∫ z, L z ∂P) - ∫ z, L z ∂Q := by
  have hY := importanceScore_memLp P hL hW hbound
  have hLint : Integrable L P := Integrable.of_bound hL.aestronglyMeasurable B
    (hbound.mono fun _ h => by simpa only [Real.norm_eq_abs] using h)
  have hLW : Integrable (fun z => L z * W z) P := by
    convert hLint.sub (hY.integrable (by norm_num)) using 1
    ext z
    dsimp only [importanceScore, Pi.sub_apply]
    ring
  have htarget : ∫ z, L z ∂Q = ∫ z, L z * W z ∂P := by
    rw [← hchange, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hWpos _), smul_eq_mul, mul_comm]
  rw [htarget, ← integral_sub hLint hLW]
  congr 1
  ext z
  dsimp only [importanceScore]
  ring

/-- The loss range and the likelihood-ratio discrepancy imply the variance
bound; no variance or concentration conclusion is an experiment field. -/
theorem importanceScore_variance_le (P : Measure Ω) [IsProbabilityMeasure P]
    {L W : Ω → ℝ} (hL : Measurable L) (hW : MemLp W 2 P) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ᵐ z ∂P, |L z| ≤ B) :
    variance (importanceScore L W) P ≤ B ^ 2 * densityChiSquared P W := by
  have hY := importanceScore_memLp P hL hW hbound
  have hZ : MemLp (fun z => 1 - W z) 2 P := (memLp_const 1).sub hW
  calc variance (importanceScore L W) P ≤ ∫ z, importanceScore L W z ^ 2 ∂P :=
         variance_le_expectation_sq hY.aestronglyMeasurable
       _ ≤ ∫ z, B ^ 2 * (1 - W z) ^ 2 ∂P := by
         apply integral_mono_ae hY.integrable_sq (hZ.integrable_sq.const_mul _)
         filter_upwards [hbound] with z hz
         dsimp only [importanceScore]
         rw [mul_pow]
         have hs : L z ^ 2 ≤ B ^ 2 := by
           simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (L z)) hB).mpr hz
         exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
       _ = B ^ 2 * densityChiSquared P W := integral_const_mul _ _

/-- Confidence guarantee for the actual importance-weighted estimator on
independent logs, with block size and block count stated as integer inequalities. -/
theorem importanceScore_confidence (P Q : Measure Ω) [IsProbabilityMeasure P]
    {L W : Ω → ℝ} (hL : Measurable L)
    (hWm : Measurable W) (hW : MemLp W 2 P) (hWpos : ∀ z, 0 ≤ W z)
    (hchange : P.withDensity (fun z => ENNReal.ofReal (W z)) = Q)
    {B δ η : ℝ} (hB : 0 ≤ B) (hbound : ∀ᵐ z ∂P, |L z| ≤ B)
    (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hsize : 4 * (B ^ 2 * densityChiSquared P W) ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw P m k).real
      {z | δ ≤ |medianOfMeans (importanceScore L W) m k z -
        ((∫ x, L x ∂P) - ∫ x, L x ∂Q)|} ≤ η := by
  rw [← importanceScore_integral P Q hL hWm hW hWpos hchange hbound]
  exact medianOfMeans_confidence P (by unfold importanceScore; fun_prop)
    (importanceScore_memLp P hL hW hbound)
    (importanceScore_variance_le P hL hW hB hbound) hδ hη hm hk hsize hblocks

/-- Zero discrepancy forces the likelihood ratio to be one almost everywhere. -/
theorem ae_eq_one_of_densityChiSquared_eq_zero
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ} (hW : MemLp W 2 P)
    (hzero : densityChiSquared P W = 0) : ∀ᵐ z ∂P, W z = 1 := by
  have hZ := ((memLp_const (1 : ℝ)).sub hW).integrable_sq
  have hz := (integral_eq_zero_iff_of_nonneg (fun z : Ω => sq_nonneg (1 - W z))
    (show Integrable (fun z => (1 - W z) ^ 2) P from hZ)).mp hzero
  filter_upwards [hz] with z hz
  have := sq_eq_zero_iff.mp hz
  linarith

/-- At zero discrepancy the target cost equals the behavior cost. Therefore
outputting zero needs no samples and is strictly accurate for every positive tolerance. -/
theorem cost_gap_eq_zero_of_densityChiSquared_eq_zero
    (P Q : Measure Ω) [IsProbabilityMeasure P]
    {L W : Ω → ℝ} (hL : Measurable L) (hWm : Measurable W)
    (hW : MemLp W 2 P) (hWpos : ∀ z, 0 ≤ W z)
    (hchange : P.withDensity (fun z => ENNReal.ofReal (W z)) = Q)
    {B : ℝ} (hbound : ∀ᵐ z ∂P, |L z| ≤ B) (hzero : densityChiSquared P W = 0) :
    (∫ z, L z ∂P) - ∫ z, L z ∂Q = 0 := by
  rw [← importanceScore_integral P Q hL hWm hW hWpos hchange hbound]
  have hz := ae_eq_one_of_densityChiSquared_eq_zero P hW hzero
  calc (∫ z, importanceScore L W z ∂P) = ∫ _z : Ω, (0 : ℝ) ∂P := by
         apply integral_congr_ae
         filter_upwards [hz] with z hz
         simp [importanceScore, hz]
       _ = 0 := integral_zero _ _

/-- For a normalized likelihood ratio, chi-squared divergence is its second
moment minus one. The normalization follows from the actual target law. -/
theorem densityChiSquared_eq_integral_sq_sub_one
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {W : Ω → ℝ} (hWm : Measurable W) (hW : MemLp W 2 P) (hWpos : ∀ z, 0 ≤ W z)
    (hchange : P.withDensity (fun z => ENNReal.ofReal (W z)) = Q) :
    densityChiSquared P W = (∫ z, W z ^ 2 ∂P) - 1 := by
  have hmean : ∫ z, W z ∂P = 1 := by
    have hi := integral_withDensity_eq_integral_toReal_smul (μ := P)
      (f := fun z => ENNReal.ofReal (W z)) (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun _ : Ω => (1 : ℝ))
    rw [hchange] at hi
    simp only [integral_const, probReal_univ, smul_eq_mul,
      ENNReal.toReal_ofReal (hWpos _), mul_one] at hi
    exact hi.symm
  have hWi := hW.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have heq : (fun z => (1 - W z) ^ 2) = (fun z => 1 - 2 * W z + W z ^ 2) := by
    ext z
    ring
  have hsub : Integrable (fun z => 1 - 2 * W z) P :=
    (integrable_const 1).sub (hWi.const_mul 2)
  unfold densityChiSquared
  rw [heq, integral_add hsub hW.integrable_sq,
    integral_sub (integrable_const 1) (hWi.const_mul 2), integral_const_mul, hmean]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- A density that depends only on the observable record remains the exact
density after discarding latent information. -/
theorem withDensity_map_of_factorization {Z : Type*} [MeasurableSpace Z]
    (P Q : Measure Ω) {f : Ω → Z} (hf : Measurable f)
    {g : Z → ℝ} (hg : Measurable g)
    (hchange : P.withDensity (fun x => ENNReal.ofReal (g (f x))) = Q) :
    (P.map f).withDensity (fun z => ENNReal.ofReal (g z)) = Q.map f := by
  ext E hE
  rw [withDensity_apply _ hE, setLIntegral_map hE (by fun_prop) hf,
    Measure.map_apply hf hE, ← hchange, withDensity_apply _ (hf hE)]

end Cslib.Probability
