/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Gaussian.Measure
public import CslibFrontier.Foundations.Probability.Gaussian.Smoothing
public import CslibFrontier.Foundations.MeasureTheory.Group.ConvolutionDensity

public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Adding a continuous Gaussian to a coset discrete Gaussian

## Main results

* `ZLattice.conv_discreteGaussian_eq_withDensity`: the exact relative density after adding
  continuous Gaussian noise to a coset discrete Gaussian.
* `ZLattice.tvDist_conv_discreteGaussian_le`: an unconditional full-L1 bound using the actual
  nonzero dual masses and the strictly positive input-coset normalizer.
* `ZLattice.tvDist_conv_discreteGaussian_le_of_dual_mass_le`: the source's `4ε` bound.
* `ZLattice.tvDist_conv_discreteGaussian_le_of_gap`: a quantitative sufficient width criterion.

The convolution uses the actual discrete Gaussian on `L + u`: sample the lattice at center
`-u`, then add `u`. The continuous Gaussian has density `gaussianWeight s / s ^ dim` with
respect to canonical volume. Both measures are normalized before applying total variation.
The positive combined width `t` satisfies `t² = r² + s²`, equivalently `t = √(r² + s²)`.

## References

[Regev2009], Claim 3.9 and equation (11), printed pages 22–23 of the May 2, 2009 author
version, with its full-L1 statistical-distance convention from printed page 13 (range `[0, 2]`).
The minimum smoothing parameter is replaced by the actual nonzero dual mass bound used in
the source's proof; the final theorem discharges that bound using an explicit dual gap.
These are analytic probability statements. The actual scalar and mod-one distribution bounds
of Corollary 3.10 are proved in `Gaussian.Projection`. The periodic-density-series formula,
the LWE experiment in Lemma 3.11, efficient sampling, finite precision and the quantum reduction
remain separate.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Module
open scoped ENNReal RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem gaussianWeight_mul_complete_square (r s t : ℝ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (ht2 : t ^ 2 = r ^ 2 + s ^ 2) (x y : E) :
    gaussianWeight r y * gaussianWeight s (x - y) =
      gaussianWeight t x * gaussianWeight (r * s / t) (y - (r / t) ^ 2 • x) := by
  unfold gaussianWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_smul_right, real_inner_comm y x]
  field_simp
  rw [ht2]
  ring

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private theorem lintegral_gaussianWeight_discreteGaussian (r s t : ℝ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (ht2 : t ^ 2 = r ^ 2 + s ^ 2)
    (u x : E) :
    (∫⁻ y, ENNReal.ofReal (gaussianWeight s (-y + x) / s ^ finrank ℝ E)
      ∂((discreteGaussian L r hr (-u)).toMeasure.map (fun z : L ↦ (z : E) + u))) =
      ENNReal.ofReal (gaussianWeight t x *
        gaussianMass L (r * s / t) ((r / t) ^ 2 • x - u) /
          (s ^ finrank ℝ E * gaussianMass L r (-u))) := by
  have hm : Measurable (fun z : L ↦ (z : E) + u) := by fun_prop
  rw [lintegral_map (by unfold gaussianWeight; fun_prop) hm,
    lintegral_countable']
  have hp : 0 < s ^ finrank ℝ E := pow_pos hs _
  have hmass := gaussianMass_pos L r hr (-u)
  have hh : 0 < r * s / t := div_pos (mul_pos hr hs) ht
  have hsum := (summable_gaussianWeight L (r * s / t) hh
    ((r / t) ^ 2 • x - u)).mul_left (gaussianWeight t x)
  rw [show gaussianWeight t x * gaussianMass L (r * s / t) ((r / t) ^ 2 • x - u) /
      (s ^ finrank ℝ E * gaussianMass L r (-u)) =
      ∑' z : L, gaussianWeight t x *
        gaussianWeight (r * s / t) ((z : E) - ((r / t) ^ 2 • x - u)) /
          (s ^ finrank ℝ E * gaussianMass L r (-u)) by
    rw [tsum_div_const, tsum_mul_left]; rfl]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun z ↦ div_nonneg
    (mul_nonneg (gaussianWeight_pos _ _).le (gaussianWeight_pos _ _).le)
    (mul_pos hp hmass).le) (hsum.div_const _)]
  apply tsum_congr
  intro z
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    discreteGaussian_apply, ← ENNReal.ofReal_div_of_pos hmass,
    ← ENNReal.ofReal_mul (div_nonneg (gaussianWeight_pos _ _).le hp.le)]
  congr 1
  have hsq := gaussianWeight_mul_complete_square r s t hr hs ht ht2 x ((z : E) + u)
  have hc : (z : E) + u - (r / t) ^ 2 • x =
      (z : E) - ((r / t) ^ 2 • x - u) := by abel
  rw [hc] at hsq
  rw [sub_neg_eq_add]
  have hx : -((z : E) + u) + x = x - ((z : E) + u) := by abel
  rw [hx]
  rw [div_mul_div_comm, mul_comm (gaussianWeight s _) (gaussianWeight r _), hsq]

/-- The actual coset discrete Gaussian convolved with a normalized continuous Gaussian has
an exact density relative to the continuous Gaussian of combined width. The positive `t`
satisfying `t² = r² + s²` is `√(r² + s²)`. No smoothing assumption is used. -/
theorem conv_discreteGaussian_eq_withDensity (r s t : ℝ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (ht2 : t ^ 2 = r ^ 2 + s ^ 2) (u : E) :
    Measure.conv ((discreteGaussian L r hr (-u)).toMeasure.map (fun z : L ↦ (z : E) + u))
      (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))) =
    (volume.withDensity
      (fun x : E ↦ ENNReal.ofReal (gaussianWeight t x / t ^ finrank ℝ E))).withDensity
      (fun x ↦ ENNReal.ofReal
        ((covolume L / (r * s / t) ^ finrank ℝ E *
          gaussianMass L (r * s / t) ((r / t) ^ 2 • x - u)) /
          (covolume L / r ^ finrank ℝ E * gaussianMass L r (-u)))) := by
  have hc := covolume_pos L volume
  have hm := gaussianMass_pos L r hr (-u)
  have hh : 0 < r * s / t := div_pos (mul_pos hr hs) ht
  have hf : Measurable (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E)) :=
    ((continuous_gaussianWeight s).div_const _).measurable.ennreal_ofReal
  have hg : Measurable (fun x : E ↦ ENNReal.ofReal
      ((covolume L / (r * s / t) ^ finrank ℝ E *
        gaussianMass L (r * s / t) ((r / t) ^ 2 • x - u)) /
        (covolume L / r ^ finrank ℝ E * gaussianMass L r (-u)))) := by
    apply Measurable.ennreal_ofReal
    exact (continuous_const.mul ((continuous_gaussianMass L _ hh).comp
      ((continuous_const.smul continuous_id).sub continuous_const))).measurable.div_const _
  rw [conv_withDensity_eq_withDensity_lintegral hf, ← withDensity_mul _
    (((continuous_gaussianWeight t).div_const _).measurable.ennreal_ofReal) hg]
  congr 1
  funext x
  rw [lintegral_gaussianWeight_discreteGaussian L r s t hr hs ht ht2 u x]
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (div_nonneg (gaussianWeight_pos _ _).le (pow_pos ht _).le)]
  congr 1
  simp only [div_pow, mul_pow]
  field_simp

/-- The full-L1 distance of the actual coset Gaussian convolution is bounded by its two
actual nonzero dual masses, divided by the positive normalized mass of the input coset. -/
theorem tvDist_conv_discreteGaussian_le (r s t : ℝ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (ht2 : t ^ 2 = r ^ 2 + s ^ 2) (u : E) :
    tvDist
      (Measure.conv ((discreteGaussian L r hr (-u)).toMeasure.map (fun z : L ↦ (z : E) + u))
        (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))))
      (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight t x / t ^ finrank ℝ E))) ≤
    ((gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / (r * s / t)) 0 - 1) +
      (gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / r) 0 - 1)) /
      (covolume L / r ^ finrank ℝ E * gaussianMass L r (-u)) := by
  let A (w : ℝ) (c : E) := covolume L / w ^ finrank ℝ E * gaussianMass L w c
  let h := r * s / t
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  let δ (w : ℝ) := gaussianMass D (1 / w) 0 - 1
  let ν := volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight t x / t ^ finrank ℝ E))
  let f : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (A h ((r / t) ^ 2 • x - u) / A r (-u))
  have hh : 0 < h := div_pos (mul_pos hr hs) ht
  have hA : 0 < A r (-u) := mul_pos (div_pos (covolume_pos L volume) (pow_pos hr _))
    (gaussianMass_pos L r hr (-u))
  have : IsProbabilityMeasure ν := isProbabilityMeasure_gaussianWeight t ht
  have : IsProbabilityMeasure
      (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))) :=
    isProbabilityMeasure_gaussianWeight s hs
  have hconv : Measure.conv
      ((discreteGaussian L r hr (-u)).toMeasure.map (fun z : L ↦ (z : E) + u))
      (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))) =
      ν.withDensity f := conv_discreteGaussian_eq_withDensity L r s t hr hs ht ht2 u
  have : IsProbabilityMeasure (ν.withDensity f) := by rw [← hconv]; infer_instance
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    exact (continuous_const.mul ((continuous_gaussianMass L h hh).comp
      ((continuous_const.smul continuous_id).sub continuous_const))).measurable.div_const _
  have hlin : ∫⁻ x, f x ∂ν = 1 := by
    simpa only [withDensity_apply f MeasurableSet.univ, Measure.restrict_univ] using
      (measure_univ (μ := ν.withDensity f))
  have hfi : Integrable f ν := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [enorm_eq_self, hlin] using (show (1 : ℝ≥0∞) < ∞ by simp)
  have hbound (x : E) : |1 - (f x).toReal| ≤ (δ h + δ r) / A r (-u) := by
    have hnum : 0 < A h ((r / t) ^ 2 • x - u) :=
      mul_pos (div_pos (covolume_pos L volume) (pow_pos hh _)) (gaussianMass_pos L h hh _)
    rw [show (f x).toReal = A h ((r / t) ^ 2 • x - u) / A r (-u) from
      ENNReal.toReal_ofReal (div_pos hnum hA).le]
    rw [one_sub_div hA.ne', abs_div, abs_of_pos hA]
    apply div_le_div_of_nonneg_right _ hA.le
    calc
      |A r (-u) - A h ((r / t) ^ 2 • x - u)| =
          |(A r (-u) - 1) + (1 - A h ((r / t) ^ 2 • x - u))| := by congr 1; ring
      _ ≤ |A r (-u) - 1| + |1 - A h ((r / t) ^ 2 • x - u)| := abs_add_le _ _
      _ ≤ δ r + δ h := add_le_add (abs_gaussianMass_normalized_sub_one_le L r hr (-u))
        (by simpa only [abs_sub_comm] using
          (abs_gaussianMass_normalized_sub_one_le L h hh ((r / t) ^ 2 • x - u)))
      _ = _ := add_comm _ _
  rw [hconv, tvDist_withDensity_self_eq_integral hfi]
  change (∫ x, |1 - (f x).toReal| ∂ν) ≤ (δ h + δ r) / A r (-u)
  calc
    _ ≤ ∫ _ : E, (δ h + δ r) / A r (-u) ∂ν := by
      exact integral_mono ((integrable_const (1 : ℝ)).sub
        (integrable_toReal_of_lintegral_ne_top hf.aemeasurable (by rw [hlin]; simp))).abs
        (integrable_const _) hbound
    _ = _ := by simp

/-- The source's `4ε` full-L1 bound follows from an actual nonzero dual mass bound at width
`r * s / t`. The premise is a checkable sum bound, not a smoothing or sampling assertion. -/
theorem tvDist_conv_discreteGaussian_le_of_dual_mass_le (r s t : ℝ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (ht2 : t ^ 2 = r ^ 2 + s ^ 2) (u : E)
    (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
      (1 / (r * s / t)) 0 - 1 ≤ ε) :
    tvDist
      (Measure.conv ((discreteGaussian L r hr (-u)).toMeasure.map (fun z : L ↦ (z : E) + u))
        (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))))
      (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight t x / t ^ finrank ℝ E))) ≤
      4 * ε := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have hh : 0 < r * s / t := div_pos (mul_pos hr hs) ht
  have hst : s ≤ t := by nlinarith [sq_pos_of_pos hr]
  have hhr : r * s / t ≤ r := (div_le_iff₀ ht).mpr (by nlinarith)
  have hm : gaussianMass D (1 / r) 0 ≤ gaussianMass D (1 / (r * s / t)) 0 := by
    exact Summable.tsum_le_tsum (fun z : D ↦ gaussianWeight_le_of_le (one_div_pos.mpr hr)
      (one_div_le_one_div_of_le hh hhr) ((z : E) - 0))
      (summable_gaussianWeight D (1 / r) (one_div_pos.mpr hr) 0)
      (summable_gaussianWeight D (1 / (r * s / t)) (one_div_pos.mpr hh) 0)
  have hdr : gaussianMass D (1 / r) 0 - 1 ≤ ε := by linarith
  have hA := (abs_le.mp ((abs_gaussianMass_normalized_sub_one_le L r hr (-u)).trans hdr)).1
  have hpos : 0 < covolume L / r ^ finrank ℝ E * gaussianMass L r (-u) :=
    mul_pos (div_pos (covolume_pos L volume) (pow_pos hr _)) (gaussianMass_pos L r hr (-u))
  apply (tvDist_conv_discreteGaussian_le L r s t hr hs ht ht2 u).trans
  apply (div_le_iff₀ hpos).mpr
  calc
    _ ≤ 2 * ε := by change (gaussianMass D _ 0 - 1) + (gaussianMass D _ 0 - 1) ≤ _; linarith
    _ ≤ 4 * ε * (1 - ε) := by nlinarith
    _ ≤ 4 * ε * (covolume L / r ^ finrank ℝ E * gaussianMass L r (-u)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rfl

/-- A positive dual gap and the explicit Gaussian tail criterion suffice for the actual
coset convolution bound. This discharges the small-dual-mass premise quantitatively. -/
theorem tvDist_conv_discreteGaussian_le_of_gap (r s t : ℝ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (ht2 : t ^ 2 = r ^ 2 + s ^ 2) (u : E)
    (a : ℝ) (ha : 0 < a)
    (hgap : ∀ w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
      w ≠ 0 → a ≤ ‖(w : E)‖)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hnum : 2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * (r * s / t) ^ 2 * a ^ 2 / 4) ≤
      ε / (1 + ε)) :
    tvDist
      (Measure.conv ((discreteGaussian L r hr (-u)).toMeasure.map (fun z : L ↦ (z : E) + u))
        (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))))
      (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight t x / t ^ finrank ℝ E))) ≤
      4 * ε :=
  tvDist_conv_discreteGaussian_le_of_dual_mass_le L r s t hr hs ht ht2 u ε hε.le hεhalf
    (gaussianMass_dual_sub_one_le_of_gap L (r * s / t) (div_pos (mul_pos hr hs) ht)
      a ha hgap ε hε hnum)

end ZLattice
