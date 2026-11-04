/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`)

public import Complexity.Init
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.Basic
import Complexity.Foundations.Probability.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Projections of the standard Gaussian measure

Let `X` be a standard Gaussian vector of a finite-dimensional real inner product space `E`
(`stdGaussian E`). Its covariance is the inner product, so:

* the projection `⟪u, X⟫` is a centered Gaussian of variance `‖u‖ ^ 2`
  (`stdGaussian_map_inner`);
* projections onto orthogonal vectors are uncorrelated, and since they are jointly Gaussian,
  independent (`indepFun_inner_stdGaussian`), so their joint law is the product of their laws
  (`stdGaussian_map_inner_prod`).

Hence the projection onto a nonzero `u` lands in a set `s` with probability at most
`volume s / (√(2π) ‖u‖)` (`stdGaussian_inner_mem_le`), and has absolute value at least `c > 0`
with probability at most `‖u‖ ^ 2 / c ^ 2` (`stdGaussian_le_abs_inner_le`).

The standard Gaussian vector of `EuclideanSpace ℝ ι` is a vector of independent standard Gaussian
coordinates (`measurePreserving_toLp_pi_gaussianReal`), which transfers these facts to the
product measure `Measure.pi fun _ : ι => gaussianReal 0 1` on `ι → ℝ`; for instance `a ⬝ᵥ ·` is
a centered Gaussian of variance `‖a‖ ^ 2` there (`pi_gaussianReal_map_dotProduct`).

## Main results

* `ProbabilityTheory.stdGaussian_map_inner`: the law of a projection.
* `ProbabilityTheory.indepFun_inner_stdGaussian`: projections onto orthogonal vectors are
  independent.
* `ProbabilityTheory.stdGaussian_map_inner_prod`: the joint law of projections onto orthogonal
  vectors.
* `ProbabilityTheory.stdGaussian_inner_mem_le`, `ProbabilityTheory.stdGaussian_le_abs_inner_le`:
  window and tail bounds for a projection.
* `ProbabilityTheory.measurePreserving_toLp_pi_gaussianReal`: independent standard Gaussian
  coordinates form a standard Gaussian vector of `EuclideanSpace ℝ ι`.
* `ProbabilityTheory.pi_gaussianReal_map_dotProduct`: the law of a projection of independent
  standard Gaussian coordinates.
* `ProbabilityTheory.memLp_dotProduct_pi_gaussianReal`,
  `ProbabilityTheory.integrable_dotProduct_pi_gaussianReal`: its moments.
* `ProbabilityTheory.measureReal_pi_gaussianReal_eq`: the product measure of standard Gaussians
  carries events to the standard Gaussian measure on `EuclideanSpace ℝ ι`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The law of a projection.** Under the standard Gaussian measure, `⟪u, ·⟫` is a centered
Gaussian of variance `‖u‖ ^ 2`. -/
theorem stdGaussian_map_inner (u : E) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) = gaussianReal 0 (‖u‖₊ ^ 2) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ u)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm,
    Real.toNNReal_pow (norm_nonneg u), norm_toNNReal] at h
  exact h

/-- **Orthogonal projections are independent.** Under the standard Gaussian measure, `⟪u, ·⟫`
and `⟪v, ·⟫` are jointly Gaussian with covariance `⟪u, v⟫`, so they are independent when `u` and
`v` are orthogonal. -/
theorem indepFun_inner_stdGaussian {u v : E} (huv : ⟪u, v⟫ = 0) :
    IndepFun (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫) (stdGaussian E) := by
  have hlaw : HasGaussianLaw (fun x => (innerSL ℝ u x, innerSL ℝ v x)) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun ((innerSL ℝ u).prod (innerSL ℝ v))
  have hcov : cov[innerSL ℝ u, innerSL ℝ v; stdGaussian E] = 0 := by
    have h := covarianceBilin_apply_eq_cov (μ := stdGaussian E) IsGaussian.memLp_two_id u v
    rw [covarianceBilin_stdGaussian, innerSL_apply_apply ℝ] at h
    exact h.symm.trans huv
  exact hlaw.indepFun_of_covariance_eq_zero hcov

/-- The joint law of the projections onto orthogonal vectors `u` and `v` is the product of
centered Gaussians of variances `‖u‖ ^ 2` and `‖v‖ ^ 2`. -/
theorem stdGaussian_map_inner_prod {u v : E} (huv : ⟪u, v⟫ = 0) :
    (stdGaussian E).map (fun x => (⟪u, x⟫, ⟪v, x⟫)) =
      (gaussianReal 0 (‖u‖₊ ^ 2)).prod (gaussianReal 0 (‖v‖₊ ^ 2)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1
      (indepFun_inner_stdGaussian huv), stdGaussian_map_inner, stdGaussian_map_inner]

/-- **Window bound.** The projection of a standard Gaussian vector onto a nonzero vector `u` lands
in a measurable set `s` with probability at most `volume s / (√(2π) ‖u‖)`. -/
theorem stdGaussian_inner_mem_le {u : E} (hu : u ≠ 0) {s : Set ℝ} (hs : MeasurableSet s) :
    stdGaussian E {x | ⟪u, x⟫ ∈ s} ≤ ENNReal.ofReal (√(2 * Real.pi) * ‖u‖)⁻¹ * volume s := by
  have hv : ‖u‖₊ ^ 2 ≠ 0 := pow_ne_zero 2 (nnnorm_ne_zero_iff.2 hu)
  have h := gaussianReal_le_ofReal_mul_volume 0 hv s
  rw [← stdGaussian_map_inner, Measure.map_apply (by fun_prop) hs, NNReal.coe_pow, coe_nnnorm,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg u)] at h
  exact h

/-- **Tail bound.** The projection of a standard Gaussian vector onto `u` has absolute value at
least `c > 0` with probability at most `‖u‖ ^ 2 / c ^ 2`. -/
theorem stdGaussian_le_abs_inner_le (u : E) {c : ℝ} (hc : 0 < c) :
    stdGaussian E {x | c ≤ |⟪u, x⟫|} ≤ ENNReal.ofReal (‖u‖ ^ 2 / c ^ 2) := by
  have h := gaussianReal_meas_ge_le 0 (‖u‖₊ ^ 2) hc
  rw [← stdGaussian_map_inner, Measure.map_apply (by fun_prop)
    (measurableSet_le measurable_const (by fun_prop)), NNReal.coe_pow, coe_nnnorm] at h
  simp only [sub_zero] at h
  exact h

/-- Independent standard Gaussian coordinates form a standard Gaussian vector of
`EuclideanSpace ℝ ι`. -/
theorem measurePreserving_toLp_pi_gaussianReal (ι : Type*) [Fintype ι] :
    MeasurePreserving (WithLp.toLp 2) (Measure.pi fun _ : ι => gaussianReal 0 1)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
  ⟨by fun_prop, map_pi_eq_stdGaussian⟩

/-- Under independent standard Gaussian coordinates, the projection `a ⬝ᵥ ·` is a centered
Gaussian of variance `‖a‖ ^ 2`, the squared Euclidean norm of `a`. -/
theorem pi_gaussianReal_map_dotProduct {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (a ⬝ᵥ ·) =
      gaussianReal 0 (‖WithLp.toLp 2 a‖₊ ^ 2) := by
  have h : (a ⬝ᵥ ·) = (fun x : EuclideanSpace ℝ ι => ⟪WithLp.toLp 2 a, x⟫) ∘ WithLp.toLp 2 := by
    funext z
    simp only [Function.comp_apply, EuclideanSpace.inner_toLp_toLp, star_trivial,
      dotProduct_comm]
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_toLp_pi_gaussianReal ι).map_eq, stdGaussian_map_inner]

/-- Under independent standard Gaussian coordinates, the projection `a ⬝ᵥ ·` has finite moments
of every finite order. -/
theorem memLp_dotProduct_pi_gaussianReal {ι : Type*} [Fintype ι] (a : ι → ℝ) {p : ℝ≥0∞}
    (hp : p ≠ ∞) :
    MemLp (fun x => a ⬝ᵥ x) p (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hD : Measurable fun x : ι → ℝ => a ⬝ᵥ x := by fun_prop
  exact (memLp_id_gaussianReal' p hp).comp_measurePreserving
    ⟨hD, pi_gaussianReal_map_dotProduct a⟩

/-- Under independent standard Gaussian coordinates, the projection `a ⬝ᵥ ·` is integrable. -/
theorem integrable_dotProduct_pi_gaussianReal {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Integrable (fun x => a ⬝ᵥ x) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  memLp_one_iff_integrable.1 (memLp_dotProduct_pi_gaussianReal a ENNReal.one_ne_top)

/-- The product of standard Gaussians on `ι → ℝ` carries an event to the same event under the
standard Gaussian measure of `EuclideanSpace ℝ ι`. -/
theorem measureReal_pi_gaussianReal_eq {ι : Type*} [Fintype ι]
    {s : Set (EuclideanSpace ℝ ι)} (hs : MeasurableSet s) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {ω | WithLp.toLp 2 ω ∈ s} =
      (stdGaussian (EuclideanSpace ℝ ι)).real s :=
  (measurePreserving_toLp_pi_gaussianReal ι).measureReal_preimage hs.nullMeasurableSet

end ProbabilityTheory
