/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `Correlated.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import CslibFrontier.Foundations.MeasureTheory.Constructions.BorelSpace.Order
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Correlated Gaussians and Gaussian noise stability

Two standard Gaussians `z`, `z'` are *`ρ`-correlated* when they are jointly Gaussian with
`E[z z'] = ρ` [O'Donnell, Definition 11.6][ODonnell2014]. Following Fact 11.7, we define their
law `correlatedGaussian ρ` concretely as the law of `(g₁, ρ g₁ + √(1 - ρ²) g₂)` for independent
standard Gaussians `g₁`, `g₂`. For unit vectors `u`, `v` of a finite-dimensional real inner
product space, the projections `⟪u, X⟫`, `⟪v, X⟫` of a standard Gaussian vector `X` are
`⟪u, v⟫`-correlated (`stdGaussian_map_inner_prod_eq_correlatedGaussian`, Fact 11.7). For
`-1 ≤ ρ ≤ 1` it follows that both marginals are standard Gaussians, the law is invariant under
swapping and under negating both coordinates, and `E[z z'] = ρ`. Hence the construction provably
agrees with Definition 11.6: it is jointly Gaussian (`isGaussian_correlatedGaussian`), and every
jointly Gaussian law on the plane with means `0`, variances `1` and correlation `ρ` equals it
(`eq_correlatedGaussian`).

An *`n`-dimensional* `ρ`-correlated pair (Definition 11.10) has mutually independent
`ρ`-correlated coordinate pairs (`correlatedGaussianPi`); equivalently `z` is a standard Gaussian
vector and `z' = ρ z + √(1 - ρ²) g` for an independent standard Gaussian vector `g`
(`correlatedGaussianPi_eq_map`). The first vector is a standard Gaussian vector
(`correlatedGaussianPi_map_fst`); for `|ρ| ≤ 1` so is the second, and the law is invariant under
swapping the two (`correlatedGaussianPi_map_snd`, `correlatedGaussianPi_map_swap`). The
projections `a ⬝ᵥ z`, `a ⬝ᵥ z'` form a `ρ`-correlated pair scaled by `√(a ⬝ᵥ a)`
(`correlatedGaussianPi_map_dotProduct`). The *Gaussian noise stability* `Stab_ρ[f] = E[f z f z']`
(`gaussianNoiseStability`, Definition 11.18) of a halfspace through
the origin is `1 - (2 / π) arccos ρ` (Corollary 11.20), and that of the indicator of `(-∞, 0]` in
one coordinate is `1 / 2 - arccos ρ / (2π)` (Example 11.19); both rest on Sheppard's formula.

## Main definitions

* `ProbabilityTheory.correlatedGaussian`: the law of a `ρ`-correlated pair of standard Gaussians.
* `ProbabilityTheory.correlatedGaussianPi`: the law of an `n`-dimensional `ρ`-correlated pair.
* `ProbabilityTheory.gaussianNoiseStability`: the Gaussian noise stability `Stab_ρ[f]`.

## Main results

* `ProbabilityTheory.isGaussian_correlatedGaussian`, `ProbabilityTheory.eq_correlatedGaussian`:
  the construction agrees with Definition 11.6.
* `ProbabilityTheory.stdGaussian_map_inner_prod_eq_correlatedGaussian`: Fact 11.7.
* `ProbabilityTheory.correlatedGaussian_zero`, `ProbabilityTheory.correlatedGaussian_one`,
  `ProbabilityTheory.correlatedGaussian_neg_one`: a `0`-correlated pair is independent, and a
  `±1`-correlated pair is `(g, ±g)`.
* `ProbabilityTheory.correlatedGaussian_map_fst`, `ProbabilityTheory.correlatedGaussian_map_snd`,
  `ProbabilityTheory.correlatedGaussian_map_swap`, `ProbabilityTheory.correlatedGaussian_map_neg`,
  `ProbabilityTheory.correlatedGaussian_map_neg_snd`,
  `ProbabilityTheory.integral_correlatedGaussian_fst_mul_snd`: marginals, symmetries and
  correlation.
* `ProbabilityTheory.measureReal_correlatedGaussian_zero_mem_uIoc`,
  `ProbabilityTheory.integral_correlatedGaussian_indicator_Iic_mul`: Sheppard's Formula, in the
  forms (11.2) and (11.1).
* `ProbabilityTheory.integral_correlatedGaussian_ite_pos_mul_ite_pos`: Corollary 11.20 on the
  line.
* `ProbabilityTheory.correlatedGaussianPi_eq_map_pi`,
  `ProbabilityTheory.correlatedGaussianPi_eq_map`,
  `ProbabilityTheory.correlatedGaussianPi_one`,
  `ProbabilityTheory.correlatedGaussianPi_map_eval`,
  `ProbabilityTheory.correlatedGaussianPi_map_fst`,
  `ProbabilityTheory.correlatedGaussianPi_map_snd`,
  `ProbabilityTheory.correlatedGaussianPi_map_swap`,
  `ProbabilityTheory.measurePreserving_fst_correlatedGaussianPi`,
  `ProbabilityTheory.measurePreserving_snd_correlatedGaussianPi`,
  `ProbabilityTheory.correlatedGaussianPi_map_dotProduct`: the `n`-dimensional pair.
* `ProbabilityTheory.gaussianNoiseStability_comp_eval`,
  `ProbabilityTheory.gaussianNoiseStability_comp_dotProduct`: reduction to the line.
* `ProbabilityTheory.gaussianNoiseStability_indicator_Iic_eval`: Example 11.19.
* `ProbabilityTheory.gaussianNoiseStability_ite_pos_dotProduct`,
  `ProbabilityTheory.gaussianNoiseStability_ite_nonneg_dotProduct`: Corollary 11.20.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Set
open scoped RealInnerProductSpace Interval

namespace ProbabilityTheory

/-! ### Correlated pairs of standard Gaussians -/

/-- The law of a **`ρ`-correlated pair of standard Gaussians**
[O'Donnell, Definition 11.6][ODonnell2014], realized as in [O'Donnell, Fact 11.7][ODonnell2014]
by the law of `(g₁, ρ g₁ + √(1 - ρ²) g₂)` for independent standard Gaussians `g₁` and `g₂`. It is
meant for `-1 ≤ ρ ≤ 1`; outside that range `√(1 - ρ²) = 0` in Lean. For `|ρ| ≤ 1` it provably is
the law of Definition 11.6, the jointly Gaussian law with means `0`, variances `1` and
correlation `ρ` (`isGaussian_correlatedGaussian`, `eq_correlatedGaussian`). -/
noncomputable def correlatedGaussian (ρ : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map fun g => (g.1, ρ * g.1 + √(1 - ρ ^ 2) * g.2)

/-- The defining formula of `correlatedGaussian`: the law of `(g₁, ρ g₁ + √(1 - ρ²) g₂)`. -/
theorem correlatedGaussian_def (ρ : ℝ) :
    correlatedGaussian ρ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      fun g => (g.1, ρ * g.1 + √(1 - ρ ^ 2) * g.2) := by
  rw [correlatedGaussian]

instance isProbabilityMeasure_correlatedGaussian (ρ : ℝ) :
    IsProbabilityMeasure (correlatedGaussian ρ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

/-- Moving the scale `c` of the second Gaussian into its variance. -/
private theorem gaussianReal_prod_map_affine (ρ c : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun g => (g.1, ρ * g.1 + c * g.2)) =
      ((gaussianReal 0 1).prod (gaussianReal 0 (.mk (c ^ 2) (sq_nonneg c)))).map
        fun g => (g.1, ρ * g.1 + g.2) := by
  have h : gaussianReal 0 (.mk (c ^ 2) (sq_nonneg c)) = (gaussianReal 0 1).map (c * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  have h2 := Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1) (f := id)
    (g := fun x : ℝ => c * x) measurable_id (by fun_prop)
  rw [Measure.map_id] at h2
  rw [h, h2, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Correlated Gaussians as projections** [O'Donnell, Fact 11.7][ODonnell2014]. For unit
vectors `u` and `v` and a standard Gaussian vector `X`, the projections `⟪u, X⟫` and `⟪v, X⟫` are
`⟪u, v⟫`-correlated standard Gaussians. Indeed `v = ρ u + w` with `w` orthogonal to `u` and
`‖w‖ ^ 2 = 1 - ρ ^ 2`, so `⟪u, X⟫` and `⟪w, X⟫` are independent. -/
theorem stdGaussian_map_inner_prod_eq_correlatedGaussian {u v : E} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    (stdGaussian E).map (fun x => (⟪u, x⟫, ⟪v, x⟫)) = correlatedGaussian ⟪u, v⟫ := by
  set ρ := ⟪u, v⟫ with hρ
  set w := v - ρ • u with hw
  have huw : ⟪u, w⟫ = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    ring
  have hww : ‖w‖ ^ 2 = 1 - ρ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hw, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hv, real_inner_comm u v, ← hρ]
    ring
  have hpair : (fun x => (⟪u, x⟫, ⟪v, x⟫)) =
      (fun p : ℝ × ℝ => (p.1, ρ * p.1 + p.2)) ∘ fun x => (⟪u, x⟫, ⟪w, x⟫) := by
    funext x
    simp only [Function.comp_apply, hw, inner_sub_left, real_inner_smul_left]
    ring_nf
  have h1 : ‖u‖₊ ^ 2 = 1 := by
    ext
    simp only [NNReal.coe_pow, coe_nnnorm, hu, one_pow, NNReal.coe_one]
  have h2 : ‖w‖₊ ^ 2 = .mk (√(1 - ρ ^ 2) ^ 2) (sq_nonneg _) := by
    ext
    simp only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_mk]
    rw [sq_sqrt (by nlinarith [sq_nonneg ‖w‖]), hww]
  rw [hpair, ← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map_inner_prod huw, h1,
    h2, correlatedGaussian, gaussianReal_prod_map_affine]

/-- For `-1 ≤ ρ ≤ 1` there are unit vectors of the plane with inner product `ρ`. -/
private theorem exists_norm_eq_one_inner_eq {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ∃ u v : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫ = ρ := by
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith [abs_le.1 hρ]
  refine ⟨EuclideanSpace.single 0 1, WithLp.toLp 2 ![ρ, √(1 - ρ ^ 2)], by simp, ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs,
      sq_abs, sq_sqrt (sub_nonneg.2 hρ2), add_sub_cancel, sqrt_one]
  · rw [EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul, Matrix.cons_val_zero]

/-- The first coordinate of a correlated pair is a standard Gaussian. -/
theorem correlatedGaussian_map_fst (ρ : ℝ) :
    (correlatedGaussian ρ).map Prod.fst = gaussianReal 0 1 := by
  rw [correlatedGaussian, Measure.map_map measurable_fst (by fun_prop)]
  exact (Measure.map_fst_prod).trans (by rw [measure_univ, one_smul])

/-- The second coordinate of a `ρ`-correlated pair is a standard Gaussian when `|ρ| ≤ 1`. -/
theorem correlatedGaussian_map_snd {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    (correlatedGaussian ρ).map Prod.snd = gaussianReal 0 1 := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_norm_eq_one_inner_eq hρ
  rw [← stdGaussian_map_inner_prod_eq_correlatedGaussian hu hv,
    Measure.map_map measurable_snd (by fun_prop)]
  refine (stdGaussian_map_inner v).trans ?_
  congr
  ext
  simp only [NNReal.coe_pow, coe_nnnorm, hv, one_pow, NNReal.coe_one]

/-- A `ρ`-correlated pair is symmetric: `(z', z)` has the same law as `(z, z')`. -/
theorem correlatedGaussian_map_swap {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    (correlatedGaussian ρ).map Prod.swap = correlatedGaussian ρ := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_norm_eq_one_inner_eq hρ
  conv_lhs => rw [← stdGaussian_map_inner_prod_eq_correlatedGaussian hu hv,
    Measure.map_map measurable_swap (by fun_prop)]
  exact (stdGaussian_map_inner_prod_eq_correlatedGaussian hv hu).trans
    (by rw [real_inner_comm])

/-- A `ρ`-correlated pair is invariant under negation: `(-z, -z')` has the same law as
`(z, z')`. -/
theorem correlatedGaussian_map_neg {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    (correlatedGaussian ρ).map (fun p => -p) = correlatedGaussian ρ := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_norm_eq_one_inner_eq hρ
  conv_lhs => rw [← stdGaussian_map_inner_prod_eq_correlatedGaussian hu hv,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun p : ℝ × ℝ => -p) ∘ (fun x => (⟪u, x⟫, ⟪v, x⟫)) =
      fun x => (⟪-u, x⟫, ⟪-v, x⟫) := by
    funext x
    simp only [Function.comp_apply, Prod.neg_mk, inner_neg_left]
  rw [hcomp, stdGaussian_map_inner_prod_eq_correlatedGaussian (by rw [norm_neg, hu])
    (by rw [norm_neg, hv]), inner_neg_neg]

/-- **The correlation of a correlated pair.** The product of a `ρ`-correlated pair of standard
Gaussians has mean `ρ` when `|ρ| ≤ 1`. -/
theorem integral_correlatedGaussian_fst_mul_snd {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ∫ p, p.1 * p.2 ∂correlatedGaussian ρ = ρ := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_norm_eq_one_inner_eq hρ
  rw [← stdGaussian_map_inner_prod_eq_correlatedGaussian hu hv,
    integral_map (by fun_prop) (by fun_prop)]
  have h := covarianceBilin_apply (μ := stdGaussian (EuclideanSpace ℝ (Fin 2)))
    IsGaussian.memLp_two_id u v
  simp only [covarianceBilin_stdGaussian, id_eq, integral_id_stdGaussian, sub_zero] at h
  exact h.symm

/-- A `ρ`-correlated pair is jointly Gaussian, as [O'Donnell, Definition 11.6][ODonnell2014]
requires: it is a linear image of a pair of independent standard Gaussians. -/
instance isGaussian_correlatedGaussian (ρ : ℝ) : IsGaussian (correlatedGaussian ρ) := by
  have h : (fun g : ℝ × ℝ => (g.1, ρ * g.1 + √(1 - ρ ^ 2) * g.2)) =
      ⇑((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ρ • ContinuousLinearMap.fst ℝ ℝ ℝ + √(1 - ρ ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    funext g
    simp
  rw [correlatedGaussian, h]
  infer_instance

/-- The mean and variance of a linear functional `L` under a measure on the plane whose
coordinates have mean `0`, variance `1` and correlation `ρ`. -/
private theorem integral_dual_variance_dual {ν : Measure (ℝ × ℝ)} [IsGaussian ν] {ρ : ℝ}
    (h1 : ∫ p, p.1 ∂ν = 0) (h2 : ∫ p, p.2 ∂ν = 0) (h11 : ∫ p, p.1 ^ 2 ∂ν = 1)
    (h22 : ∫ p, p.2 ^ 2 ∂ν = 1) (h12 : ∫ p, p.1 * p.2 ∂ν = ρ) (L : StrongDual ℝ (ℝ × ℝ)) :
    ν[L] = 0 ∧ Var[L; ν] = L (1, 0) ^ 2 + 2 * ρ * L (1, 0) * L (0, 1) + L (0, 1) ^ 2 := by
  set a := L (1, 0)
  set b := L (0, 1)
  have hL : ⇑L = fun p : ℝ × ℝ => a * p.1 + b * p.2 := by
    funext p
    have : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm a, mul_comm b]
  have m1 : MemLp (fun p : ℝ × ℝ => p.1) 2 ν :=
    IsGaussian.memLp_dual ν (ContinuousLinearMap.fst ℝ ℝ ℝ) 2 (by simp)
  have m2 : MemLp (fun p : ℝ × ℝ => p.2) 2 ν :=
    IsGaussian.memLp_dual ν (ContinuousLinearMap.snd ℝ ℝ ℝ) 2 (by simp)
  have i1 : Integrable (fun p : ℝ × ℝ => p.1) ν := m1.integrable (by simp)
  have i2 : Integrable (fun p : ℝ × ℝ => p.2) ν := m2.integrable (by simp)
  have i11 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ν :=
    m1.integrable_sq
  have i22 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ν :=
    m2.integrable_sq
  have i12 : Integrable (fun p : ℝ × ℝ => p.1 * p.2) ν := m1.integrable_mul m2
  have hmean : ν[L] = 0 := by
    rw [hL, integral_add (i1.const_mul a) (i2.const_mul b), integral_const_mul,
      integral_const_mul, h1, h2]
    ring
  refine ⟨hmean, ?_⟩
  rw [variance_of_integral_eq_zero (by fun_prop) hmean, hL]
  have hsq : (fun p : ℝ × ℝ => (a * p.1 + b * p.2) ^ 2) =
      fun p => a ^ 2 * p.1 ^ 2 + 2 * a * b * (p.1 * p.2) + b ^ 2 * p.2 ^ 2 := by
    funext p
    ring
  have j : Integrable (fun p : ℝ × ℝ => a ^ 2 * p.1 ^ 2 + 2 * a * b * (p.1 * p.2)) ν :=
    (i11.const_mul _).add (i12.const_mul _)
  rw [hsq, integral_add j (i22.const_mul _), integral_add (i11.const_mul _) (i12.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, h11, h12, h22]
  ring

/-- **Definition 11.6 and Fact 11.7 agree** [O'Donnell, Definition 11.6][ODonnell2014]. A
jointly Gaussian law on the plane whose coordinates have mean `0`, variance `1` and correlation
`ρ` is `correlatedGaussian ρ`: both laws have the same characteristic function. -/
theorem eq_correlatedGaussian {ν : Measure (ℝ × ℝ)} [IsGaussian ν] {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (h1 : ∫ p, p.1 ∂ν = 0) (h2 : ∫ p, p.2 ∂ν = 0) (h11 : ∫ p, p.1 ^ 2 ∂ν = 1)
    (h22 : ∫ p, p.2 ^ 2 ∂ν = 1) (h12 : ∫ p, p.1 * p.2 ∂ν = ρ) :
    ν = correlatedGaussian ρ := by
  have hfst {f : ℝ → ℝ} (hf : Measurable f) :
      ∫ p, f p.1 ∂correlatedGaussian ρ = ∫ x, f x ∂gaussianReal 0 1 := by
    rw [← correlatedGaussian_map_fst ρ, integral_map (by fun_prop) hf.aestronglyMeasurable]
  have hsnd {f : ℝ → ℝ} (hf : Measurable f) :
      ∫ p, f p.2 ∂correlatedGaussian ρ = ∫ x, f x ∂gaussianReal 0 1 := by
    rw [← correlatedGaussian_map_snd hρ, integral_map (by fun_prop) hf.aestronglyMeasurable]
  have hm : ∫ x, x ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
  have hv : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero (by fun_prop) hm] at this
    exact_mod_cast this
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  obtain ⟨e1, v1⟩ := integral_dual_variance_dual h1 h2 h11 h22 h12 L
  obtain ⟨e2, v2⟩ := integral_dual_variance_dual (ν := correlatedGaussian ρ)
    ((hfst measurable_id).trans hm) ((hsnd measurable_id).trans hm)
    ((hfst (measurable_id.pow_const 2)).trans hv)
    ((hsnd (measurable_id.pow_const 2)).trans hv) (integral_correlatedGaussian_fst_mul_snd hρ) L
  rw [IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq, integral_complex_ofReal,
    integral_complex_ofReal, e1, e2, v1, v2]

/-- **Sheppard's Formula**, in the form [O'Donnell, Example 11.19, (11.2)][ODonnell2014]: a
`ρ`-correlated pair of standard Gaussians differs in sign (`0` lies between them) with
probability `arccos ρ / π`. -/
theorem measureReal_correlatedGaussian_zero_mem_uIoc {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    (correlatedGaussian ρ).real {p | (0 : ℝ) ∈ Ι p.1 p.2} = arccos ρ / π := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_norm_eq_one_inner_eq hρ
  rw [← stdGaussian_map_inner_prod_eq_correlatedGaussian hu hv, map_measureReal_apply
    (by fun_prop) (measurableSet_setOf_mem_uIoc measurable_fst measurable_snd 0)]
  exact measureReal_stdGaussian_zero_mem_uIoc_eq_arccos hu hv

/-- The `±1` indicator of the positive half-line. -/
private noncomputable def signPos (x : ℝ) : ℝ := if 0 < x then 1 else -1

@[fun_prop]
private theorem measurable_signPos : Measurable signPos :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

/-- After negating both arguments, the product of signs is `-1` exactly when `0` lies between
the arguments. -/
private theorem signPos_neg_mul_signPos_neg (x y : ℝ) :
    signPos (-x) * signPos (-y) =
      1 - 2 * {p : ℝ × ℝ | (0 : ℝ) ∈ Ι p.1 p.2}.indicator 1 (x, y) := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;>
    simp only [signPos, Left.neg_pos_iff, indicator, mem_ofPred_eq, mem_uIoc, Pi.one_apply,
      ← not_lt, hx, hy, not_true_eq_false, not_false_eq_true, and_true, and_false, or_false,
      false_or, ite_true, ite_false] <;> norm_num

/-- **The noise stability of the sign**: for a `ρ`-correlated pair `(z, z')`,
`E[sgn z sgn z'] = 1 - (2 / π) arccos ρ` [O'Donnell, Corollary 11.20][ODonnell2014]. Here
`sgn 0 = -1`, whereas the book takes `sgn 0 = 1`; that convention is the closed-halfspace case
`gaussianNoiseStability_ite_nonneg_dotProduct`. -/
theorem integral_correlatedGaussian_ite_pos_mul_ite_pos {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ∫ p, (if 0 < p.1 then (1 : ℝ) else -1) * (if 0 < p.2 then 1 else -1) ∂correlatedGaussian ρ =
      1 - 2 / π * arccos ρ := by
  change ∫ p, signPos p.1 * signPos p.2 ∂correlatedGaussian ρ = _
  have hC := measurableSet_setOf_mem_uIoc measurable_fst measurable_snd (0 : ℝ)
  conv_lhs => rw [← correlatedGaussian_map_neg hρ]
  rw [integral_map (f := fun p : ℝ × ℝ => signPos p.1 * signPos p.2) (by fun_prop)
    (by fun_prop)]
  simp only [Prod.fst_neg, Prod.snd_neg, signPos_neg_mul_signPos_neg, Prod.mk.eta]
  rw [integral_sub (integrable_const _) ((integrable_const _).indicator hC |>.const_mul 2),
    integral_const_mul, integral_const, integral_indicator_one hC, probReal_univ, smul_eq_mul,
    mul_one, measureReal_correlatedGaussian_zero_mem_uIoc hρ]
  ring

/-- `sgn` written through the indicator of `(-∞, 0]`. -/
private theorem signPos_eq (x : ℝ) : signPos x = 1 - 2 * (Iic (0 : ℝ)).indicator 1 x := by
  simp only [signPos, indicator, mem_Iic, Pi.one_apply, ← not_lt]
  split_ifs <;> norm_num

private theorem norm_signPos_le (x : ℝ) : ‖signPos x‖ ≤ 1 := by
  simp only [signPos]
  split_ifs <;> norm_num

/-- A `0`-correlated pair is a pair of independent standard Gaussians. -/
theorem correlatedGaussian_zero :
    correlatedGaussian 0 = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  rw [correlatedGaussian]
  simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero, sqrt_one, one_mul, Prod.mk.eta, Measure.map_id']

/-- Negating the second coordinate of a `ρ`-correlated pair gives a `-ρ`-correlated pair. -/
theorem correlatedGaussian_map_neg_snd (ρ : ℝ) :
    (correlatedGaussian ρ).map (fun p => (p.1, -p.2)) = correlatedGaussian (-ρ) := by
  have hprod : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun g => (g.1, -g.2)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    rw [show (fun g : ℝ × ℝ => (g.1, -g.2)) = Prod.map id (fun y => -y) from rfl,
      ← Measure.map_prod_map _ _ measurable_id measurable_neg, Measure.map_id,
      gaussianReal_zero_map_neg]
  rw [correlatedGaussian, correlatedGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  conv_rhs => rw [← hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext g
  simp only [Function.comp_apply, neg_sq, Prod.mk.injEq, true_and]
  ring

/-- A `1`-correlated pair is a standard Gaussian repeated: `(g, g)`. -/
theorem correlatedGaussian_one :
    correlatedGaussian 1 = (gaussianReal 0 1).map fun x => (x, x) := by
  have h : (fun g : ℝ × ℝ => (g.1, 1 * g.1 + √(1 - 1 ^ 2) * g.2)) =
      (fun x => (x, x)) ∘ Prod.fst := by
    funext g
    simp only [one_mul, one_pow, sub_self, sqrt_zero, zero_mul, add_zero, Function.comp_apply]
  rw [correlatedGaussian, h, ← Measure.map_map (by fun_prop) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- A `-1`-correlated pair is a standard Gaussian and its negation: `(g, -g)`. -/
theorem correlatedGaussian_neg_one :
    correlatedGaussian (-1) = (gaussianReal 0 1).map fun x => (x, -x) := by
  rw [← correlatedGaussian_map_neg_snd, correlatedGaussian_one,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- `E[sgn g] = 0`: at `ρ = 0` the pair is independent, so `E[sgn g] ^ 2 = 1 - (2 / π) (π / 2)`. -/
private theorem integral_gaussianReal_signPos : ∫ x, signPos x ∂gaussianReal 0 1 = 0 := by
  have h := integral_correlatedGaussian_ite_pos_mul_ite_pos (ρ := 0) (by norm_num)
  change ∫ p, signPos p.1 * signPos p.2 ∂correlatedGaussian 0 = _ at h
  rw [correlatedGaussian_zero, integral_prod_mul (f := signPos) (g := signPos), arccos_zero] at h
  field_simp at h
  simpa using h

/-- **Sheppard's Formula** [O'Donnell, Example 11.19, (11.1)][ODonnell2014]: two `ρ`-correlated
standard Gaussians are both nonpositive with probability `1 / 2 - arccos ρ / (2π)`, i.e. the
indicator `f` of `(-∞, 0]` has `E[f z f z'] = 1 / 2 - arccos ρ / (2π)`. -/
theorem integral_correlatedGaussian_indicator_Iic_mul {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ∫ p, (Iic (0 : ℝ)).indicator 1 p.1 * (Iic (0 : ℝ)).indicator 1 p.2 ∂correlatedGaussian ρ =
      1 / 2 - arccos ρ / (2 * π) := by
  have hpt : ∀ p : ℝ × ℝ, (Iic (0 : ℝ)).indicator 1 p.1 * (Iic (0 : ℝ)).indicator 1 p.2 =
      1 / 4 * (1 - signPos p.1 - signPos p.2 + signPos p.1 * signPos p.2) := fun p => by
    rw [signPos_eq, signPos_eq]
    ring
  have hint : ∀ {g : ℝ × ℝ → ℝ}, Measurable g → (∀ p, ‖g p‖ ≤ 1) →
      Integrable g (correlatedGaussian ρ) := fun hg hb =>
    Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all _ hb)
  have h1 : Integrable (fun p : ℝ × ℝ => signPos p.1) (correlatedGaussian ρ) :=
    hint (by fun_prop) fun p => norm_signPos_le p.1
  have h2 : Integrable (fun p : ℝ × ℝ => signPos p.2) (correlatedGaussian ρ) :=
    hint (by fun_prop) fun p => norm_signPos_le p.2
  have h12 : Integrable (fun p : ℝ × ℝ => signPos p.1 * signPos p.2) (correlatedGaussian ρ) :=
    hint (by fun_prop) fun p => by
      rw [norm_mul]
      exact (mul_le_mul (norm_signPos_le _) (norm_signPos_le _) (norm_nonneg _)
        zero_le_one).trans_eq (one_mul 1)
  have hfst : ∫ p, signPos p.1 ∂correlatedGaussian ρ = 0 := by
    rw [← integral_gaussianReal_signPos, ← correlatedGaussian_map_fst ρ,
      integral_map (by fun_prop) (by fun_prop)]
  have hsnd : ∫ p, signPos p.2 ∂correlatedGaussian ρ = 0 := by
    rw [← integral_gaussianReal_signPos, ← correlatedGaussian_map_snd hρ,
      integral_map (by fun_prop) (by fun_prop)]
  have hstab := integral_correlatedGaussian_ite_pos_mul_ite_pos hρ
  change ∫ p, signPos p.1 * signPos p.2 ∂correlatedGaussian ρ = _ at hstab
  simp only [hpt]
  rw [integral_const_mul,
    integral_add (f := fun p : ℝ × ℝ => 1 - signPos p.1 - signPos p.2)
      (((integrable_const _).sub h1).sub h2) h12,
    integral_sub (f := fun p : ℝ × ℝ => 1 - signPos p.1) ((integrable_const _).sub h1) h2,
    integral_sub (integrable_const _) h1,
    integral_const, probReal_univ, smul_eq_mul, mul_one, hfst, hsnd, hstab]
  field_simp
  ring

/-! ### `n`-dimensional correlated Gaussians and noise stability -/

variable (ι : Type*) [Fintype ι]

/-- The law of **`ρ`-correlated `n`-dimensional Gaussians**
[O'Donnell, Definition 11.10][ODonnell2014]: random vectors `z`, `z'` indexed by `ι` whose
coordinate pairs `(z i, z' i)` are mutually independent `ρ`-correlated pairs of standard
Gaussians. -/
noncomputable def correlatedGaussianPi (ρ : ℝ) : Measure ((ι → ℝ) × (ι → ℝ)) :=
  (Measure.pi fun _ : ι => correlatedGaussian ρ).map
    fun p => (fun i => (p i).1, fun i => (p i).2)

instance isProbabilityMeasure_correlatedGaussianPi (ρ : ℝ) :
    IsProbabilityMeasure (correlatedGaussianPi ι ρ) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

/-- `ρ`-correlated vectors are assembled from mutually independent `ρ`-correlated coordinate
pairs. This is the definition of `correlatedGaussianPi`. -/
theorem correlatedGaussianPi_eq_map_pi (ρ : ℝ) :
    correlatedGaussianPi ι ρ =
      (Measure.pi fun _ : ι => correlatedGaussian ρ).map
        fun p => (fun i => (p i).1, fun i => (p i).2) := by
  rw [correlatedGaussianPi]

/-- **`ρ`-correlated vectors from independent ones**
[O'Donnell, Definition 11.10, Remark 11.11][ODonnell2014]:
`(z, z')` is `ρ`-correlated when `z` is a standard Gaussian vector and `z' = ρ z + √(1 - ρ²) g`
for an independent standard Gaussian vector `g`. -/
theorem correlatedGaussianPi_eq_map (ρ : ℝ) :
    correlatedGaussianPi ι ρ =
      ((Measure.pi fun _ : ι => gaussianReal 0 1).prod
        (Measure.pi fun _ : ι => gaussianReal 0 1)).map
          fun q => (q.1, fun i => ρ * q.1 i + √(1 - ρ ^ 2) * q.2 i) := by
  have hL : Measurable fun g : ℝ × ℝ => (g.1, ρ * g.1 + √(1 - ρ ^ 2) * g.2) := by fun_prop
  have h1 := Measure.pi_map_pi (μ := fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (f := fun _ => fun g : ℝ × ℝ => (g.1, ρ * g.1 + √(1 - ρ ^ 2) * g.2))
    fun _ => hL.aemeasurable
  rw [← (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι _ _).map_eq,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _), correlatedGaussianPi]
  change ((Measure.pi fun _ : ι => ((gaussianReal 0 1).prod (gaussianReal 0 1)).map _).map _) = _
  rw [← h1, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- `1`-correlated Gaussian vectors are `(z, z)` for a standard Gaussian vector `z`. -/
theorem correlatedGaussianPi_one :
    correlatedGaussianPi ι 1 =
      (Measure.pi fun _ : ι => gaussianReal 0 1).map fun z => (z, z) := by
  have h : (fun q : (ι → ℝ) × (ι → ℝ) => (q.1, fun i => 1 * q.1 i + √(1 - 1 ^ 2) * q.2 i)) =
      (fun z => (z, z)) ∘ Prod.fst := by
    funext q
    simp only [one_mul, one_pow, sub_self, sqrt_zero, zero_mul, add_zero, Function.comp_apply]
  rw [correlatedGaussianPi_eq_map, h, ← Measure.map_map (by fun_prop) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- The coordinate pairs of `ρ`-correlated vectors are `ρ`-correlated. -/
theorem correlatedGaussianPi_map_eval (ρ : ℝ) (i : ι) :
    (correlatedGaussianPi ι ρ).map (fun p => (p.1 i, p.2 i)) = correlatedGaussian ρ := by
  rw [correlatedGaussianPi, Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval _ i).map_eq

/-- The first vector of a `ρ`-correlated pair is a standard Gaussian vector. -/
theorem correlatedGaussianPi_map_fst (ρ : ℝ) :
    (correlatedGaussianPi ι ρ).map Prod.fst = Measure.pi fun _ : ι => gaussianReal 0 1 := by
  rw [correlatedGaussianPi, Measure.map_map measurable_fst (by fun_prop)]
  refine (Measure.pi_map_pi (f := fun _ => Prod.fst) fun _ => measurable_fst.aemeasurable).trans ?_
  simp only [correlatedGaussian_map_fst]

/-- The second vector of a `ρ`-correlated pair is a standard Gaussian vector when `|ρ| ≤ 1`. -/
theorem correlatedGaussianPi_map_snd {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    (correlatedGaussianPi ι ρ).map Prod.snd = Measure.pi fun _ : ι => gaussianReal 0 1 := by
  rw [correlatedGaussianPi, Measure.map_map measurable_snd (by fun_prop)]
  refine (Measure.pi_map_pi (f := fun _ => Prod.snd) fun _ => measurable_snd.aemeasurable).trans ?_
  simp only [correlatedGaussian_map_snd hρ]

/-- The first projection carries `ρ`-correlated vectors to a standard Gaussian vector. -/
theorem measurePreserving_fst_correlatedGaussianPi (ρ : ℝ) :
    MeasurePreserving Prod.fst (correlatedGaussianPi ι ρ)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  ⟨measurable_fst, correlatedGaussianPi_map_fst ι ρ⟩

/-- The second projection carries `ρ`-correlated vectors to a standard Gaussian vector when
`|ρ| ≤ 1`. -/
theorem measurePreserving_snd_correlatedGaussianPi {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    MeasurePreserving Prod.snd (correlatedGaussianPi ι ρ)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  ⟨measurable_snd, correlatedGaussianPi_map_snd ι hρ⟩

/-- `ρ`-correlated vectors are symmetric: `(z', z)` has the same law as `(z, z')` when
`|ρ| ≤ 1`. -/
theorem correlatedGaussianPi_map_swap {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    (correlatedGaussianPi ι ρ).map Prod.swap = correlatedGaussianPi ι ρ := by
  have h := Measure.pi_map_pi (μ := fun _ : ι => correlatedGaussian ρ) (f := fun _ => Prod.swap)
    fun _ => measurable_swap.aemeasurable
  simp only [correlatedGaussian_map_swap hρ] at h
  rw [correlatedGaussianPi, Measure.map_map measurable_swap (by fun_prop)]
  conv_rhs => rw [← h, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **Projections of correlated vectors.** For `ρ`-correlated vectors `z`, `z'`, the projections
`a ⬝ᵥ z` and `a ⬝ᵥ z'` are a `ρ`-correlated pair of standard Gaussians scaled by `√(a ⬝ᵥ a)`. -/
theorem correlatedGaussianPi_map_dotProduct (ρ : ℝ) (a : ι → ℝ) :
    (correlatedGaussianPi ι ρ).map (fun p => (a ⬝ᵥ p.1, a ⬝ᵥ p.2)) =
      (correlatedGaussian ρ).map fun p => (√(a ⬝ᵥ a) * p.1, √(a ⬝ᵥ a) * p.2) := by
  set c := √(a ⬝ᵥ a)
  set σ := √(1 - ρ ^ 2)
  have hD : Measurable fun z : ι → ℝ => a ⬝ᵥ z := by fun_prop
  have hlaw := pi_gaussianReal_map_dotProduct_eq_map_const_mul a
  have hcomp : (fun p : (ι → ℝ) × (ι → ℝ) => (a ⬝ᵥ p.1, a ⬝ᵥ p.2)) ∘
      (fun q : (ι → ℝ) × (ι → ℝ) => (q.1, fun i => ρ * q.1 i + σ * q.2 i)) =
        (fun s : ℝ × ℝ => (s.1, ρ * s.1 + σ * s.2)) ∘ Prod.map (a ⬝ᵥ ·) (a ⬝ᵥ ·) := by
    funext q
    refine Prod.ext rfl ?_
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, dotProduct, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [correlatedGaussianPi_eq_map, Measure.map_map (by fun_prop) (by fun_prop), hcomp,
    ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_prod_map _ _ hD hD, hlaw,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), correlatedGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1 with g : 1
  exact Prod.ext rfl (by simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]; ring)

variable {ι}

/-- The **Gaussian noise stability** `Stab_ρ[f] = E[f z f z']` of `f` at `ρ`, for
`ρ`-correlated `n`-dimensional Gaussians `z`, `z'` [O'Donnell, Definition 11.18][ODonnell2014].
The book assumes `f ∈ L²(γ)` and `ρ ∈ [-1, 1]`; here `f` and `ρ` are arbitrary, and the Bochner
integral is `0` when `f z f z'` is not integrable. -/
@[expose] noncomputable def gaussianNoiseStability (ρ : ℝ) (f : (ι → ℝ) → ℝ) : ℝ :=
  ∫ p, f p.1 * f p.2 ∂correlatedGaussianPi ι ρ

/-- The noise stability of a function of one coordinate is that of the function on the line. -/
theorem gaussianNoiseStability_comp_eval (ρ : ℝ) (i : ι) {g : ℝ → ℝ} (hg : Measurable g) :
    gaussianNoiseStability ρ (fun z => g (z i)) = ∫ p, g p.1 * g p.2 ∂correlatedGaussian ρ := by
  rw [gaussianNoiseStability, ← correlatedGaussianPi_map_eval ι ρ i,
    integral_map (f := fun p : ℝ × ℝ => g p.1 * g p.2) (by fun_prop) (by fun_prop)]

/-- The noise stability of a function of the projection `a ⬝ᵥ z` is that of a function on the
line, after scaling by `√(a ⬝ᵥ a)`. -/
theorem gaussianNoiseStability_comp_dotProduct (ρ : ℝ) (a : ι → ℝ) {g : ℝ → ℝ}
    (hg : Measurable g) :
    gaussianNoiseStability ρ (fun z => g (a ⬝ᵥ z)) =
      ∫ p, g (√(a ⬝ᵥ a) * p.1) * g (√(a ⬝ᵥ a) * p.2) ∂correlatedGaussian ρ := by
  have hF : Measurable fun q : ℝ × ℝ => g q.1 * g q.2 := by fun_prop
  have h := integral_map (μ := correlatedGaussianPi ι ρ)
    (φ := fun p => (a ⬝ᵥ p.1, a ⬝ᵥ p.2)) (by fun_prop) hF.aestronglyMeasurable
  rw [correlatedGaussianPi_map_dotProduct, integral_map (by fun_prop) hF.aestronglyMeasurable]
    at h
  exact h.symm

/-- **Example 11.19** [O'Donnell, Example 11.19][ODonnell2014]: the indicator `f` of
`z i ≤ 0` has Gaussian noise stability `Stab_ρ[f] = 1 / 2 - arccos ρ / (2π)`. -/
theorem gaussianNoiseStability_indicator_Iic_eval {ρ : ℝ} (hρ : |ρ| ≤ 1) (i : ι) :
    gaussianNoiseStability ρ (fun z : ι → ℝ => (Iic (0 : ℝ)).indicator 1 (z i)) =
      1 / 2 - arccos ρ / (2 * π) := by
  rw [gaussianNoiseStability_comp_eval ρ i (measurable_one.indicator measurableSet_Iic),
    integral_correlatedGaussian_indicator_Iic_mul hρ]

/-- **Corollary 11.20, open halfspaces** [O'Donnell, Corollary 11.20][ODonnell2014]: the `±1`
indicator `h` of the open halfspace `0 < a ⬝ᵥ z`, for `a ≠ 0`, has Gaussian noise stability
`Stab_ρ[h] = 1 - (2 / π) arccos ρ`. -/
theorem gaussianNoiseStability_ite_pos_dotProduct {ρ : ℝ} (hρ : |ρ| ≤ 1) {a : ι → ℝ}
    (ha : a ≠ 0) :
    gaussianNoiseStability ρ (fun z => if 0 < a ⬝ᵥ z then (1 : ℝ) else -1) =
      1 - 2 / π * arccos ρ := by
  change gaussianNoiseStability ρ (fun z => signPos (a ⬝ᵥ z)) = _
  rw [gaussianNoiseStability_comp_dotProduct ρ a measurable_signPos]
  simp only [signPos, mul_pos_iff_of_pos_left (sqrt_dotProduct_self_pos ha)]
  exact integral_correlatedGaussian_ite_pos_mul_ite_pos hρ

/-- **Corollary 11.20, closed halfspaces** [O'Donnell, Corollary 11.20][ODonnell2014]: the `±1`
indicator `h` of the closed halfspace `0 ≤ a ⬝ᵥ z`, for `a ≠ 0`, has Gaussian noise stability
`Stab_ρ[h] = 1 - (2 / π) arccos ρ`. It is `-1` times the indicator for the open halfspace of
`-a`. -/
theorem gaussianNoiseStability_ite_nonneg_dotProduct {ρ : ℝ} (hρ : |ρ| ≤ 1) {a : ι → ℝ}
    (ha : a ≠ 0) :
    gaussianNoiseStability ρ (fun z => if 0 ≤ a ⬝ᵥ z then (1 : ℝ) else -1) =
      1 - 2 / π * arccos ρ := by
  rw [← gaussianNoiseStability_ite_pos_dotProduct hρ (neg_ne_zero.2 ha), gaussianNoiseStability,
    gaussianNoiseStability]
  congr 1 with p : 1
  simp only [neg_dotProduct, Left.neg_pos_iff]
  simp only [← not_le]
  split_ifs <;> norm_num

end ProbabilityTheory
