/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, new file `Mathlib/Probability/Moments/Reasonable.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.UniformOn
import CslibFrontier.Foundations.Probability.Gaussian.Moments

/-!
# Reasonable random variables

A real random variable `X` on a measure space `(Ω, μ)` is *`B`-reasonable* when it has a finite
fourth moment and `E[X⁴] ≤ B E[X²]²` [O'Donnell, Definition 9.1][ODonnell2014]. Under the uniform
distribution on a finite type this is the inequality `𝔼 X ^ 4 ≤ B (𝔼 X ^ 2) ^ 2` between finite
averages (`ProbabilityTheory.isReasonable_uniformOn_univ_iff`). Generalizing the uniform `±1` bit
of [O'Donnell, Example 9.2][ODonnell2014], every random variable taking only the values `±1` is
`1`-reasonable; it has `E[X²] = 1` and `E[X³] = E[X]`, so a uniformly random `±1` bit satisfies
`E[X] = E[X³] = 0`.

On a finite type, `CslibFrontier.Foundations.Data.Finset.PaleyZygmund` deliberately states
reasonableness as the hypothesis `𝔼 X ^ 4 ≤ B (𝔼 X ^ 2) ^ 2` for the tail and anticoncentration
bounds (`Fintype.pow_four_mul_dens_le_of_expect_pow_four_le`,
`Fintype.sq_one_sub_sq_le_mul_dens_of_expect_pow_four_le`); `isReasonable_uniformOn_univ_iff`
converts between the two. The predicate here is needed for random variables on general probability
spaces, such as Gaussians, where reasonableness also requires a finite fourth moment and must
transfer along laws (`HasLaw.isReasonable_iff`) and under scaling.

## Main definitions

* `ProbabilityTheory.IsReasonable`: the `B`-reasonable random variables.

## Main results

* `ProbabilityTheory.IsReasonable.mono`, `ProbabilityTheory.IsReasonable.const_mul`,
  `ProbabilityTheory.isReasonable_const_mul_iff`, `ProbabilityTheory.HasLaw.isReasonable_iff`:
  monotonicity in `B`, scale invariance and dependence on the law only.
* `ProbabilityTheory.integral_uniformOn_univ`,
  `ProbabilityTheory.isReasonable_uniformOn_univ_iff`: the uniform distribution on a finite type,
  where reasonableness is an inequality between finite averages.
* `ProbabilityTheory.isReasonable_id_gaussianReal`,
  `ProbabilityTheory.HasLaw.isReasonable_three_of_gaussianReal`: a standard Gaussian is
  `3`-reasonable [O'Donnell, Example 9.2][ODonnell2014].
* `ProbabilityTheory.isReasonable_one_of_sq_eq_one`: `±1`-valued random variables are
  `1`-reasonable.
* `ProbabilityTheory.integral_sq_eq_one_of_sq_eq_one`,
  `ProbabilityTheory.integral_pow_three_eq_integral_of_sq_eq_one`: their second and third
  moments.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B C : ℝ} {X : Ω → ℝ}

/-- A real random variable `X` on `(Ω, μ)` is **`B`-reasonable** when it has a finite fourth
moment and `E[X⁴] ≤ B E[X²]²` [O'Donnell, Definition 9.1][ODonnell2014]. The integrability
field makes the moments meaningful (a Bochner integral of a non-integrable function is `0`). The
book also assumes `B ≥ 1`; that condition is dropped here. On a probability space it holds
automatically unless `X = 0` almost everywhere, since `E[X²]² ≤ E[X⁴]` there.

This is the measure-theoretic form of the definition. Under the uniform distribution on a finite
type it is the inequality between finite averages `𝔼 X ^ 4 ≤ B (𝔼 X ^ 2) ^ 2`
(`isReasonable_uniformOn_univ_iff`). -/
structure IsReasonable (B : ℝ) (X : Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- A reasonable random variable has a finite fourth moment. -/
  memLp : MemLp X 4 μ
  /-- The fourth moment is at most `B` times the square of the second moment. -/
  integral_pow_four_le : ∫ ω, X ω ^ 4 ∂μ ≤ B * (∫ ω, X ω ^ 2 ∂μ) ^ 2

/-- A `B`-reasonable random variable is `C`-reasonable for every `C ≥ B`. -/
theorem IsReasonable.mono (hX : IsReasonable B X μ) (hBC : B ≤ C) : IsReasonable C X μ :=
  ⟨hX.memLp, hX.integral_pow_four_le.trans
    (mul_le_mul_of_nonneg_right hBC (sq_nonneg _))⟩

/-- Reasonableness is invariant under scaling: if `X` is `B`-reasonable then so is `c X`. -/
theorem IsReasonable.const_mul (hX : IsReasonable B X μ) (c : ℝ) :
    IsReasonable B (fun ω => c * X ω) μ := by
  refine ⟨hX.memLp.const_mul c, ?_⟩
  simp only [mul_pow, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hX.integral_pow_four_le (pow_nonneg (sq_nonneg c) 2)
  calc c ^ 4 * ∫ ω, X ω ^ 4 ∂μ = (c ^ 2) ^ 2 * ∫ ω, X ω ^ 4 ∂μ := by ring
    _ ≤ (c ^ 2) ^ 2 * (B * (∫ ω, X ω ^ 2 ∂μ) ^ 2) := h
    _ = B * ((c ^ 2) ^ 2 * (∫ ω, X ω ^ 2 ∂μ) ^ 2) := by ring

/-- Reasonableness is invariant under scaling by a nonzero constant. -/
theorem isReasonable_const_mul_iff {c : ℝ} (hc : c ≠ 0) :
    IsReasonable B (fun ω => c * X ω) μ ↔ IsReasonable B X μ := by
  refine ⟨fun h => ?_, fun h => h.const_mul c⟩
  have h' := h.const_mul c⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at h'
  exact h'

/-- Reasonableness depends only on the law: if `X` has law `ν`, then `X` is `B`-reasonable
exactly when the identity is `B`-reasonable under `ν`. -/
theorem HasLaw.isReasonable_iff {ν : Measure ℝ} (hX : HasLaw X ν μ) :
    IsReasonable B X μ ↔ IsReasonable B id ν := by
  have h4 : ∫ ω, X ω ^ 4 ∂μ = ∫ x, x ^ 4 ∂ν :=
    hX.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  have h2 : ∫ ω, X ω ^ 2 ∂μ = ∫ x, x ^ 2 ∂ν :=
    hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  have hm : MemLp X 4 μ ↔ MemLp id 4 ν := by
    rw [← hX.map_eq]
    exact (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).symm
  refine ⟨fun h => ⟨hm.1 h.memLp, ?_⟩, fun h => ⟨hm.2 h.memLp, ?_⟩⟩
  · simpa only [id_eq, ← h4, ← h2] using h.integral_pow_four_le
  · simpa only [id_eq, h4, h2] using h.integral_pow_four_le

section Uniform

variable {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- The integral against the uniform distribution on a finite type is the average. -/
theorem integral_uniformOn_univ (f : α → ℝ) :
    ∫ x, f x ∂uniformOn (Set.univ : Set α) = 𝔼 x, f x := by
  rw [integral_fintype .of_finite, Finset.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [measureReal_def, uniformOn_univ, div_eq_inv_mul]

/-- Under the uniform distribution on a finite type, `X` is `B`-reasonable exactly when
`𝔼 X ^ 4 ≤ B (𝔼 X ^ 2) ^ 2` [O'Donnell, Definition 9.1][ODonnell2014]. -/
theorem isReasonable_uniformOn_univ_iff {X : α → ℝ} :
    IsReasonable B X (uniformOn (Set.univ : Set α)) ↔
      𝔼 x, X x ^ 4 ≤ B * (𝔼 x, X x ^ 2) ^ 2 := by
  rw [← integral_uniformOn_univ, ← integral_uniformOn_univ]
  exact ⟨fun h => h.integral_pow_four_le, fun h => ⟨.of_discrete, h⟩⟩

end Uniform

section Gaussian

/-- A standard Gaussian is `3`-reasonable [O'Donnell, Example 9.2][ODonnell2014]. -/
theorem isReasonable_id_gaussianReal : IsReasonable 3 id (gaussianReal 0 1) :=
  ⟨memLp_id_gaussianReal 4, by
    simp only [id_eq, integral_pow_four_gaussianReal, integral_sq_gaussianReal]
    norm_num⟩

variable {g : Ω → ℝ}

/-- A random variable with standard Gaussian law is `3`-reasonable
[O'Donnell, Example 9.2][ODonnell2014]. -/
theorem HasLaw.isReasonable_three_of_gaussianReal (hg : HasLaw g (gaussianReal 0 1) μ) :
    IsReasonable 3 g μ :=
  hg.isReasonable_iff.2 isReasonable_id_gaussianReal

end Gaussian

section Sign

/-- The third moment of a `±1`-valued random variable is its mean. -/
theorem integral_pow_three_eq_integral_of_sq_eq_one (h : ∀ᵐ ω ∂μ, X ω ^ 2 = 1) :
    ∫ ω, X ω ^ 3 ∂μ = ∫ ω, X ω ∂μ :=
  integral_congr_ae (h.mono fun ω hω => by
    change X ω ^ 3 = X ω
    rw [pow_succ', hω, mul_one])

variable [IsProbabilityMeasure μ]

/-- The second moment of a `±1`-valued random variable is `1`. -/
theorem integral_sq_eq_one_of_sq_eq_one (h : ∀ᵐ ω ∂μ, X ω ^ 2 = 1) :
    ∫ ω, X ω ^ 2 ∂μ = 1 := by
  rw [integral_congr_ae h]
  simp

/-- A `±1`-valued random variable is `1`-reasonable. This generalizes the uniform `±1` bit of
[O'Donnell, Example 9.2][ODonnell2014] to any law on `{-1, 1}`. -/
theorem isReasonable_one_of_sq_eq_one (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ^ 2 = 1) :
    IsReasonable 1 X μ := by
  refine ⟨MemLp.of_bound hX.aestronglyMeasurable 1 (h.mono fun ω hω => ?_), ?_⟩
  · rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one, hω]
  · have h4 : ∫ ω, X ω ^ 4 ∂μ = 1 := by
      rw [integral_congr_ae (h.mono fun ω hω => (show X ω ^ 4 = 1 by
        rw [show X ω ^ 4 = (X ω ^ 2) ^ 2 by ring, hω, one_pow]))]
      simp
    rw [h4, integral_sq_eq_one_of_sq_eq_one h]
    norm_num

end Sign

end ProbabilityTheory
