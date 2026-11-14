/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `Quadrant.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.CDF
public import CslibFrontier.Foundations.Probability.Gaussian.Correlated
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate

/-!
# The Gaussian quadrant probability function

For `ρ ∈ [-1, 1]` and `α, β ∈ [0, 1]`, the *Gaussian quadrant probability* `Λ_ρ(α, β)` is the
probability that a `ρ`-correlated pair `(z, z')` of standard Gaussians satisfies `z ≤ t` and
`z' ≤ t'`, where `Φ t = α` and `Φ t' = β` for the standard Gaussian cdf `Φ`
[O'Donnell, Definition 11.77][ODonnell2014]. Since `Φ` is continuous and strictly increasing,
`z ≤ t` holds exactly when `Φ z ≤ α`, so we define (`gaussianQuadrant`)
`Λ_ρ(α, β) = P[Φ z ≤ α, Φ z' ≤ β]` without inverting `Φ`. This is total in `α`, `β`: values
outside `[0, 1]` act as if clamped to `[0, 1]` (`gaussianQuadrant_eq_clamp_left`). The bridge
`gaussianQuadrant_cdf_cdf` recovers the book's form `Λ_ρ(Φ t, Φ t') = P[z ≤ t, z' ≤ t']`. The
diagonal `Λ_ρ(α) = Λ_ρ(α, α)` of Borell's Isoperimetric Theorem is written
`gaussianQuadrant ρ α α`.

We prove the parts of [O'Donnell, Exercise 11.19][ODonnell2014] other than the derivative
formula (d):

* (a) a halfspace `a ⬝ᵥ z ≤ b` of Gaussian volume `α` has noise stability `Λ_ρ(α)`;
* (b) the special values: symmetry, `ρ ∈ {0, 1, -1}`, `α` or `β ∈ {0, 1}`, the reflection
  `Λ_{-ρ}(α, β) = α - Λ_ρ(α, 1 - β)` and Sheppard's value at `α = β = 1 / 2`;
* (c) `Λ_ρ(α, β) ≥ αβ` for `ρ ≥ 0`, and `≤` for `ρ ≤ 0` (non-strict);
* (e) `|Λ_ρ(α, β) - Λ_ρ(α', β')| ≤ |α - α'| + |β - β'|`, so `Λ_ρ(α)` is `2`-Lipschitz.

## Main definitions

* `ProbabilityTheory.gaussianQuadrant`: the Gaussian quadrant probability `Λ_ρ(α, β)`.

## Main results

* `ProbabilityTheory.gaussianQuadrant_cdf_cdf`: `Λ_ρ(Φ t, Φ t') = P[z ≤ t, z' ≤ t']`.
* `ProbabilityTheory.gaussianQuadrant_eq_clamp_left`,
  `ProbabilityTheory.gaussianQuadrant_eq_clamp_right`, `ProbabilityTheory.gaussianQuadrant_mono`,
  `ProbabilityTheory.gaussianQuadrant_le_min`: clamping, monotonicity and the upper bound.
* `ProbabilityTheory.measureReal_pi_gaussianReal_setOf_dotProduct_le`: the Gaussian volume of a
  halfspace.
* `ProbabilityTheory.gaussianNoiseStability_indicator_setOf_dotProduct_le`,
  `ProbabilityTheory.gaussianNoiseStability_indicator_setOf_dotProduct_le_of_measureReal_eq`:
  Exercise 11.19 (a).
* `ProbabilityTheory.gaussianQuadrant_comm`, `ProbabilityTheory.gaussianQuadrant_zero`,
  `ProbabilityTheory.gaussianQuadrant_one`, `ProbabilityTheory.gaussianQuadrant_neg_one`,
  `ProbabilityTheory.gaussianQuadrant_zero_left`, `ProbabilityTheory.gaussianQuadrant_zero_right`,
  `ProbabilityTheory.gaussianQuadrant_one_left`, `ProbabilityTheory.gaussianQuadrant_one_right`,
  `ProbabilityTheory.gaussianQuadrant_neg`,
  `ProbabilityTheory.gaussianQuadrant_neg_eq_sub_one_sub_left`,
  `ProbabilityTheory.gaussianQuadrant_half_half`: Exercise 11.19 (b).
* `ProbabilityTheory.mul_le_gaussianQuadrant`, `ProbabilityTheory.gaussianQuadrant_le_mul`:
  Exercise 11.19 (c).
* `ProbabilityTheory.abs_gaussianQuadrant_sub_le_left`,
  `ProbabilityTheory.abs_gaussianQuadrant_sub_le_right`,
  `ProbabilityTheory.abs_gaussianQuadrant_sub_le`,
  `ProbabilityTheory.lipschitzWith_gaussianQuadrant_diag`,
  `ProbabilityTheory.lipschitzWith_gaussianQuadrant`: Exercise 11.19 (e).
* `ProbabilityTheory.continuous_gaussianQuadrant`, `ProbabilityTheory.measurable_gaussianQuadrant`,
  `Measurable.gaussianQuadrant`: joint continuity and measurability.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

local notation "Φ" => cdf (gaussianReal 0 1)

/-! ### Facts about `Φ` -/

private theorem measurableSet_cdf_le (α : ℝ) : MeasurableSet {x | Φ x ≤ α} :=
  measurable_cdf _ measurableSet_Iic

private theorem measurableSet_quadrant (α β : ℝ) :
    MeasurableSet {p : ℝ × ℝ | Φ p.1 ≤ α ∧ Φ p.2 ≤ β} :=
  ((measurableSet_cdf_le α).preimage measurable_fst).inter
    ((measurableSet_cdf_le β).preimage measurable_snd)

private theorem cdf_pos' (x : ℝ) : 0 < Φ x :=
  cdf_pos (gaussianReal_absolutelyContinuous' 0 one_ne_zero) x

/-- `Φ x ≤ α` is unchanged by clamping `α` to `[0, 1]`. -/
private theorem cdf_le_iff_le_clamp (x α : ℝ) : Φ x ≤ α ↔ Φ x ≤ max (min α 1) 0 := by
  simp only [le_max_iff, le_min_iff, not_le.2 (cdf_pos' x), or_false, cdf_le_one, and_true]

private theorem measureReal_setOf_cdf_le_clamp (α : ℝ) :
    (gaussianReal 0 1).real {x | Φ x ≤ α} = max (min α 1) 0 := by
  have : {x | Φ x ≤ α} = {x | Φ x ≤ max (min α 1) 0} := by
    ext x
    exact cdf_le_iff_le_clamp x α
  rw [this, measureReal_setOf_cdf_gaussianReal_le 0 one_ne_zero (le_max_right _ _)
    (max_le (min_le_right _ _) zero_le_one)]

private theorem ae_cdf_ne (c : ℝ) : ∀ᵐ y ∂gaussianReal 0 1, Φ y ≠ c := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  refine (measure_eq_zero_iff_ae_notMem.1 (Subsingleton.measure_zero ?_ (gaussianReal 0 1)) :
    ∀ᵐ y ∂gaussianReal 0 1, y ∉ {y | Φ y = c})
  exact fun x hx y hy => (strictMono_cdf_gaussianReal 0 one_ne_zero).injective
    (hx.trans hy.symm)

/-- The first coordinate of a correlated pair satisfies `Φ z ≤ α` with probability `α`, clamped
to `[0, 1]`. -/
private theorem measureReal_fst_cdf_le (ρ α : ℝ) :
    (correlatedGaussian ρ).real {p | Φ p.1 ≤ α} = max (min α 1) 0 := by
  have h := map_measureReal_apply (μ := correlatedGaussian ρ) measurable_fst
    (measurableSet_cdf_le α)
  rw [correlatedGaussian_map_fst, measureReal_setOf_cdf_le_clamp] at h
  exact h.symm

private theorem measureReal_snd_cdf_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (β : ℝ) :
    (correlatedGaussian ρ).real {p | Φ p.2 ≤ β} = max (min β 1) 0 := by
  have h := map_measureReal_apply (μ := correlatedGaussian ρ) measurable_snd
    (measurableSet_cdf_le β)
  rw [correlatedGaussian_map_snd hρ, measureReal_setOf_cdf_le_clamp] at h
  exact h.symm

/-! ### The quadrant probability -/

/-- The **Gaussian quadrant probability function** `Λ_ρ(α, β)`
[O'Donnell, Definition 11.77][ODonnell2014]: the probability that a `ρ`-correlated pair
`(z, z')` of standard Gaussians has `Φ z ≤ α` and `Φ z' ≤ β`, for the standard Gaussian cdf `Φ`.
For `α = Φ t`, `β = Φ t'` this is the book's `P[z ≤ t, z' ≤ t']` (`gaussianQuadrant_cdf_cdf`).
It is meant for `ρ ∈ [-1, 1]` and `α, β ∈ [0, 1]`; arguments outside `[0, 1]` act as if clamped
to it. -/
noncomputable def gaussianQuadrant (ρ α β : ℝ) : ℝ :=
  (correlatedGaussian ρ).real {p | Φ p.1 ≤ α ∧ Φ p.2 ≤ β}

/-- The defining formula of `gaussianQuadrant`. -/
theorem gaussianQuadrant_def (ρ α β : ℝ) :
    gaussianQuadrant ρ α β = (correlatedGaussian ρ).real {p | Φ p.1 ≤ α ∧ Φ p.2 ≤ β} := by
  rw [gaussianQuadrant]

/-- **The book's form of `Λ_ρ`**: `Λ_ρ(Φ t, Φ t') = P[z ≤ t, z' ≤ t']` for a `ρ`-correlated
pair `(z, z')` [O'Donnell, Definition 11.77][ODonnell2014]. -/
theorem gaussianQuadrant_cdf_cdf (ρ t t' : ℝ) :
    gaussianQuadrant ρ (Φ t) (Φ t') = (correlatedGaussian ρ).real {p | p.1 ≤ t ∧ p.2 ≤ t'} := by
  simp only [gaussianQuadrant_def, (strictMono_cdf_gaussianReal 0 one_ne_zero).le_iff_le]

/-- `Λ_ρ(α, β)` is nonnegative. -/
theorem gaussianQuadrant_nonneg (ρ α β : ℝ) : 0 ≤ gaussianQuadrant ρ α β :=
  measureReal_nonneg

/-- `Λ_ρ(α, β)` is at most `1`. -/
theorem gaussianQuadrant_le_one (ρ α β : ℝ) : gaussianQuadrant ρ α β ≤ 1 :=
  measureReal_le_one

/-- `Λ_ρ(α, β)` is monotone in `α` and `β`. -/
theorem gaussianQuadrant_mono (ρ : ℝ) {α α' β β' : ℝ} (hα : α ≤ α') (hβ : β ≤ β') :
    gaussianQuadrant ρ α β ≤ gaussianQuadrant ρ α' β' :=
  measureReal_mono fun _ hp => ⟨hp.1.trans hα, hp.2.trans hβ⟩

/-- Clamping the first argument of `Λ_ρ` to `[0, 1]` does not change it. -/
theorem gaussianQuadrant_eq_clamp_left (ρ α β : ℝ) :
    gaussianQuadrant ρ α β = gaussianQuadrant ρ (max (min α 1) 0) β := by
  simp only [gaussianQuadrant_def, ← cdf_le_iff_le_clamp]

/-- Clamping the second argument of `Λ_ρ` to `[0, 1]` does not change it. -/
theorem gaussianQuadrant_eq_clamp_right (ρ α β : ℝ) :
    gaussianQuadrant ρ α β = gaussianQuadrant ρ α (max (min β 1) 0) := by
  simp only [gaussianQuadrant_def, ← cdf_le_iff_le_clamp]

/-! ### Exercise 11.19 (b): special values -/

/-- **Symmetry** [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_ρ(α, β) = Λ_ρ(β, α)`. -/
theorem gaussianQuadrant_comm {ρ : ℝ} (hρ : |ρ| ≤ 1) (α β : ℝ) :
    gaussianQuadrant ρ α β = gaussianQuadrant ρ β α := by
  conv_lhs => rw [gaussianQuadrant_def, ← correlatedGaussian_map_swap hρ,
    map_measureReal_apply measurable_swap (measurableSet_quadrant α β)]
  rw [gaussianQuadrant_def]
  congr 1
  ext p
  exact and_comm

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_ρ(α, 0) = 0`. -/
theorem gaussianQuadrant_zero_right (ρ α : ℝ) : gaussianQuadrant ρ α 0 = 0 := by
  have : {p : ℝ × ℝ | Φ p.1 ≤ α ∧ Φ p.2 ≤ 0} = ∅ :=
    eq_empty_of_forall_notMem fun p hp => (cdf_pos' p.2).not_ge hp.2
  rw [gaussianQuadrant_def, this, measureReal_empty]

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_ρ(0, β) = 0`. -/
theorem gaussianQuadrant_zero_left (ρ β : ℝ) : gaussianQuadrant ρ 0 β = 0 := by
  have : {p : ℝ × ℝ | Φ p.1 ≤ 0 ∧ Φ p.2 ≤ β} = ∅ :=
    eq_empty_of_forall_notMem fun p hp => (cdf_pos' p.1).not_ge hp.1
  rw [gaussianQuadrant_def, this, measureReal_empty]

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_ρ(α, 1) = α` for `α ∈ [0, 1]`. -/
theorem gaussianQuadrant_one_right (ρ : ℝ) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    gaussianQuadrant ρ α 1 = α := by
  have : {p : ℝ × ℝ | Φ p.1 ≤ α ∧ Φ p.2 ≤ 1} = {p | Φ p.1 ≤ α} := by
    ext p
    simp only [mem_ofPred_eq, cdf_le_one, and_true]
  rw [gaussianQuadrant_def, this, measureReal_fst_cdf_le, min_eq_left h1, max_eq_left h0]

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_ρ(1, β) = β` for `β ∈ [0, 1]`. -/
theorem gaussianQuadrant_one_left {ρ : ℝ} (hρ : |ρ| ≤ 1) {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    gaussianQuadrant ρ 1 β = β := by
  have : {p : ℝ × ℝ | Φ p.1 ≤ 1 ∧ Φ p.2 ≤ β} = {p | Φ p.2 ≤ β} := by
    ext p
    simp only [mem_ofPred_eq, cdf_le_one, true_and]
  rw [gaussianQuadrant_def, this, measureReal_snd_cdf_le hρ, min_eq_left h1, max_eq_left h0]

/-- `Λ_ρ(α, β) ≤ min α β` for `α, β ∈ [0, 1]`: the quadrant lies in each half-plane. -/
theorem gaussianQuadrant_le_min {ρ : ℝ} (hρ : |ρ| ≤ 1) {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : gaussianQuadrant ρ α β ≤ min α β :=
  le_min ((gaussianQuadrant_mono ρ le_rfl hβ1).trans_eq (gaussianQuadrant_one_right ρ hα0 hα1))
    ((gaussianQuadrant_mono ρ hα1 le_rfl).trans_eq (gaussianQuadrant_one_left hρ hβ0 hβ1))

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_0(α, β) = αβ` for `α, β ∈ [0, 1]`. -/
theorem gaussianQuadrant_zero {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) : gaussianQuadrant 0 α β = α * β := by
  rw [gaussianQuadrant_def, correlatedGaussian_zero]
  change ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
    ({x | Φ x ≤ α} ×ˢ {x | Φ x ≤ β}) = _
  rw [measureReal_prod_prod, measureReal_setOf_cdf_gaussianReal_le 0 one_ne_zero hα0 hα1,
    measureReal_setOf_cdf_gaussianReal_le 0 one_ne_zero hβ0 hβ1]

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_1(α, β) = min α β` for `α, β ∈ [0, 1]` (the
bound `β ≤ 1` is not needed). -/
theorem gaussianQuadrant_one {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) :
    gaussianQuadrant 1 α β = min α β := by
  have : (fun x : ℝ => (x, x)) ⁻¹' {p | Φ p.1 ≤ α ∧ Φ p.2 ≤ β} = {x | Φ x ≤ min α β} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, le_min_iff]
  rw [gaussianQuadrant_def, correlatedGaussian_one,
    map_measureReal_apply (by fun_prop) (measurableSet_quadrant α β), this,
    measureReal_setOf_cdf_gaussianReal_le 0 one_ne_zero (le_min hα0 hβ0)
      ((min_le_left _ _).trans hα1)]

/-- **Reflection** [O'Donnell, Exercise 11.19][ODonnell2014]:
`Λ_{-ρ}(α, β) = α - Λ_ρ(α, 1 - β)` for `α ∈ [0, 1]`. -/
theorem gaussianQuadrant_neg {ρ : ℝ} (hρ : |ρ| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (β : ℝ) : gaussianQuadrant (-ρ) α β = α - gaussianQuadrant ρ α (1 - β) := by
  set μ := correlatedGaussian ρ
  have hS : gaussianQuadrant (-ρ) α β =
      μ.real ({p | Φ p.1 ≤ α} \ {p | Φ p.1 ≤ α ∧ Φ p.2 < 1 - β}) := by
    rw [gaussianQuadrant_def, ← correlatedGaussian_map_neg_snd,
      map_measureReal_apply (by fun_prop) (measurableSet_quadrant α β)]
    congr 1
    ext p
    simp only [mem_preimage, mem_ofPred_eq, mem_sdiff, cdf_gaussianReal_neg one_ne_zero, not_and,
      not_lt, sub_le_comm]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  have hae : ∀ᵐ p ∂μ, Φ p.2 ≠ 1 - β := by
    refine ae_of_ae_map (p := fun y => Φ y ≠ 1 - β) measurable_snd.aemeasurable ?_
    rw [correlatedGaussian_map_snd hρ]
    exact ae_cdf_ne _
  have hlt : μ.real {p | Φ p.1 ≤ α ∧ Φ p.2 < 1 - β} = gaussianQuadrant ρ α (1 - β) := by
    rw [gaussianQuadrant_def]
    refine measureReal_congr (Filter.eventuallyEqSet_iff.2 (hae.mono fun p hp => ?_))
    simp only [mem_ofPred_eq, lt_iff_le_and_ne, hp, ne_eq, not_false_eq_true, and_true]
  have hmeas : MeasurableSet {p : ℝ × ℝ | Φ p.1 ≤ α ∧ Φ p.2 < 1 - β} :=
    ((measurableSet_cdf_le α).preimage measurable_fst).inter
      ((measurable_cdf _ measurableSet_Iio).preimage measurable_snd)
  have hsub : {p : ℝ × ℝ | Φ p.1 ≤ α ∧ Φ p.2 < 1 - β} ⊆ {p | Φ p.1 ≤ α} := fun _ hp => hp.1
  rw [hS, measureReal_sdiff hsub hmeas, hlt, measureReal_fst_cdf_le,
    min_eq_left h1, max_eq_left h0]

/-- **Reflection** [O'Donnell, Exercise 11.19][ODonnell2014]:
`Λ_{-ρ}(α, β) = β - Λ_ρ(1 - α, β)` for `β ∈ [0, 1]`. -/
theorem gaussianQuadrant_neg_eq_sub_one_sub_left {ρ : ℝ} (hρ : |ρ| ≤ 1) (α : ℝ) {β : ℝ}
    (h0 : 0 ≤ β) (h1 : β ≤ 1) : gaussianQuadrant (-ρ) α β = β - gaussianQuadrant ρ (1 - α) β := by
  rw [gaussianQuadrant_comm (by rwa [abs_neg]), gaussianQuadrant_neg hρ h0 h1,
    gaussianQuadrant_comm hρ]

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_{-1}(α, β) = max (α + β - 1) 0` for
`α, β ∈ [0, 1]` (the bound `0 ≤ β` is not needed). -/
theorem gaussianQuadrant_neg_one {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ1 : β ≤ 1) :
    gaussianQuadrant (-1) α β = max (α + β - 1) 0 := by
  rw [gaussianQuadrant_neg (by norm_num) hα0 hα1, gaussianQuadrant_one hα0 hα1 (by linarith)]
  rcases le_total α (1 - β) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), sub_self]
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring

/-- The probability of a quadrant as the integral of a product of indicators. -/
private theorem integral_indicator_Iic_mul_indicator_Iic (μ : Measure (ℝ × ℝ)) (t t' : ℝ) :
    ∫ p, (Iic t).indicator 1 p.1 * (Iic t').indicator 1 p.2 ∂μ =
      μ.real {p | p.1 ≤ t ∧ p.2 ≤ t'} := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ t ∧ p.2 ≤ t'} :=
    (measurableSet_Iic.preimage measurable_fst).inter (measurableSet_Iic.preimage measurable_snd)
  rw [← integral_indicator_one hS]
  congr 1
  funext p
  by_cases h1 : p.1 ≤ t <;> by_cases h2 : p.2 ≤ t' <;>
    simp [indicator, h1, h2]

/-- **Sheppard's value** [O'Donnell, Exercise 11.19][ODonnell2014]:
`Λ_ρ(1 / 2, 1 / 2) = 1 / 2 - arccos ρ / (2π)`. -/
theorem gaussianQuadrant_half_half {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    gaussianQuadrant ρ (1 / 2) (1 / 2) = 1 / 2 - arccos ρ / (2 * π) := by
  conv_lhs => rw [one_div, ← cdf_gaussianReal_zero_zero one_ne_zero]
  rw [gaussianQuadrant_cdf_cdf,
    ← integral_indicator_Iic_mul_indicator_Iic, integral_correlatedGaussian_indicator_Iic_mul hρ]

/-! ### Exercise 11.19 (c): comparison with independence -/

/-- Fubini for a correlated pair `(z, ρ z + √(1 - ρ²) g)`: the probability that `z ∈ A` and
`Φ z' ≤ β` integrates over `z ∈ A` the conditional probability that `Φ z' ≤ β`. -/
private theorem measure_correlatedGaussian_fst_mem_cdf_le (ρ β : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    correlatedGaussian ρ {p | p.1 ∈ A ∧ Φ p.2 ≤ β} =
      ∫⁻ x in A, gaussianReal 0 1 {y | Φ (ρ * x + √(1 - ρ ^ 2) * y) ≤ β} ∂gaussianReal 0 1 := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ∈ A ∧ Φ p.2 ≤ β} :=
    (hA.preimage measurable_fst).inter ((measurableSet_cdf_le β).preimage measurable_snd)
  rw [correlatedGaussian_def, Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop)), ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx]
    congr 1
    ext y
    simp only [mem_preimage, mem_ofPred_eq, hx, true_and]
  · rw [indicator_of_notMem hx, ← measure_empty (μ := gaussianReal 0 1)]
    congr 1
    ext y
    simp only [mem_preimage, mem_ofPred_eq, hx, false_and, mem_empty_iff_false]

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: positively correlated Gaussians are at least as
likely as independent ones to lie in a lower quadrant, `αβ ≤ Λ_ρ(α, β)` for `ρ ∈ [0, 1]` and
`α, β ∈ [0, 1]`. -/
theorem mul_le_gaussianQuadrant {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {α β : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : α * β ≤ gaussianQuadrant ρ α β := by
  set A := {x : ℝ | Φ x ≤ α}
  have hA : MeasurableSet A := measurableSet_cdf_le α
  set q : ℝ → ℝ≥0∞ := fun x => gaussianReal 0 1 {y | Φ (ρ * x + √(1 - ρ ^ 2) * y) ≤ β}
  -- The conditional probability `q` is antitone, so it is larger on `A` than off `A`.
  have hq : ∀ x ∈ A, ∀ x' ∈ Aᶜ, q x' ≤ q x := fun x hx x' hx' => by
    have hlt : x < x' := (monotone_cdf _).reflect_lt (hx.trans_lt (not_le.1 hx'))
    refine measure_mono fun y (hy : Φ _ ≤ β) => ?_
    exact (monotone_cdf _ (add_le_add_left (mul_le_mul_of_nonneg_left hlt.le hρ0) _)).trans hy
  have hcheb : gaussianReal 0 1 A * ∫⁻ x in Aᶜ, q x ∂gaussianReal 0 1 ≤
      gaussianReal 0 1 Aᶜ * ∫⁻ x in A, q x ∂gaussianReal 0 1 :=
    calc gaussianReal 0 1 A * ∫⁻ x in Aᶜ, q x ∂gaussianReal 0 1
        = ∫⁻ x' in Aᶜ, ∫⁻ _ in A, q x' ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
          rw [← lintegral_const_mul' _ _ (measure_ne_top _ _)]
          refine lintegral_congr fun x' => ?_
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ x' in Aᶜ, ∫⁻ x in A, q x ∂gaussianReal 0 1 ∂gaussianReal 0 1 :=
          setLIntegral_mono' hA.compl fun x' hx' => setLIntegral_mono' hA fun x hx => hq x hx x' hx'
      _ = gaussianReal 0 1 Aᶜ * ∫⁻ x in A, q x ∂gaussianReal 0 1 := by
          rw [setLIntegral_const, mul_comm]
  have hkey : gaussianReal 0 1 A * ∫⁻ x, q x ∂gaussianReal 0 1 ≤
      ∫⁻ x in A, q x ∂gaussianReal 0 1 := by
    rw [← lintegral_add_compl q hA, mul_add]
    calc _ ≤ gaussianReal 0 1 A * ∫⁻ x in A, q x ∂gaussianReal 0 1 +
          gaussianReal 0 1 Aᶜ * ∫⁻ x in A, q x ∂gaussianReal 0 1 := add_le_add le_rfl hcheb
      _ = ∫⁻ x in A, q x ∂gaussianReal 0 1 := by
          rw [← add_mul, measure_add_measure_compl hA, measure_univ, one_mul]
  have hΛ := measure_correlatedGaussian_fst_mem_cdf_le ρ β hA
  have hβ := measure_correlatedGaussian_fst_mem_cdf_le ρ β MeasurableSet.univ
  rw [Measure.restrict_univ] at hβ
  have e1 : (gaussianReal 0 1).real A = α :=
    measureReal_setOf_cdf_gaussianReal_le 0 one_ne_zero hα0 hα1
  have e2 : (correlatedGaussian ρ).real {p | p.1 ∈ univ ∧ Φ p.2 ≤ β} = β := by
    simp only [mem_univ, true_and]
    rw [measureReal_snd_cdf_le (abs_le.2 ⟨by linarith, hρ1⟩), min_eq_left hβ1, max_eq_left hβ0]
  rw [gaussianQuadrant_def]
  calc α * β = (gaussianReal 0 1 A *
        correlatedGaussian ρ {p | p.1 ∈ univ ∧ Φ p.2 ≤ β}).toReal := by
        rw [ENNReal.toReal_mul]
        exact congrArg₂ (· * ·) e1.symm e2.symm
    _ ≤ (correlatedGaussian ρ {p | p.1 ∈ A ∧ Φ p.2 ≤ β}).toReal := by
        rw [hΛ, hβ]
        exact ENNReal.toReal_mono (hΛ ▸ measure_ne_top _ _) hkey

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_ρ(α, β) ≤ αβ` for `ρ ∈ [-1, 0]` and
`α, β ∈ [0, 1]`. -/
theorem gaussianQuadrant_le_mul {ρ : ℝ} (hρ0 : -1 ≤ ρ) (hρ1 : ρ ≤ 0) {α β : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : gaussianQuadrant ρ α β ≤ α * β := by
  have h := mul_le_gaussianQuadrant (ρ := -ρ) (β := 1 - β) (by linarith) (by linarith) hα0 hα1
    (by linarith) (by linarith)
  rw [← neg_neg ρ, gaussianQuadrant_neg (abs_le.2 ⟨by linarith, by linarith⟩) hα0 hα1]
  linarith

/-! ### Exercise 11.19 (e): Lipschitz continuity -/

/-- `Λ_ρ` is `1`-Lipschitz in its first argument. -/
theorem abs_gaussianQuadrant_sub_le_left (ρ α α' β : ℝ) :
    |gaussianQuadrant ρ α β - gaussianQuadrant ρ α' β| ≤ |α - α'| := by
  wlog h : α' ≤ α generalizing α α'
  · rw [abs_sub_comm, abs_sub_comm α]
    exact this α' α (le_of_not_ge h)
  have hsub : {p : ℝ × ℝ | Φ p.1 ≤ α' ∧ Φ p.2 ≤ β} ⊆ {p | Φ p.1 ≤ α ∧ Φ p.2 ≤ β} :=
    fun _ hp => ⟨hp.1.trans h, hp.2⟩
  -- The two events differ only where `α' < Φ z ≤ α`.
  have hdiff : {p : ℝ × ℝ | Φ p.1 ≤ α ∧ Φ p.2 ≤ β} \ {p | Φ p.1 ≤ α' ∧ Φ p.2 ≤ β} ⊆
      {p | Φ p.1 ≤ α} \ {p | Φ p.1 ≤ α'} :=
    fun _ hp => ⟨hp.1.1, fun h' => hp.2 ⟨h', hp.1.2⟩⟩
  have hsub' : {p : ℝ × ℝ | Φ p.1 ≤ α'} ⊆ {p | Φ p.1 ≤ α} := fun _ hp => hp.trans h
  rw [abs_of_nonneg (sub_nonneg.2 (gaussianQuadrant_mono ρ h le_rfl)),
    abs_of_nonneg (sub_nonneg.2 h), gaussianQuadrant_def, gaussianQuadrant_def,
    ← measureReal_sdiff hsub (measurableSet_quadrant _ _)]
  refine (measureReal_mono hdiff).trans ?_
  rw [measureReal_sdiff hsub' ((measurableSet_cdf_le α').preimage measurable_fst),
    measureReal_fst_cdf_le, measureReal_fst_cdf_le]
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- `Λ_ρ` is `1`-Lipschitz in its second argument. -/
theorem abs_gaussianQuadrant_sub_le_right {ρ : ℝ} (hρ : |ρ| ≤ 1) (α β β' : ℝ) :
    |gaussianQuadrant ρ α β - gaussianQuadrant ρ α β'| ≤ |β - β'| := by
  rw [gaussianQuadrant_comm hρ α β, gaussianQuadrant_comm hρ α β']
  exact abs_gaussianQuadrant_sub_le_left ρ β β' α

/-- **Lipschitz continuity** [O'Donnell, Exercise 11.19][ODonnell2014]:
`|Λ_ρ(α, β) - Λ_ρ(α', β')| ≤ |α - α'| + |β - β'|`. -/
theorem abs_gaussianQuadrant_sub_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (α β α' β' : ℝ) :
    |gaussianQuadrant ρ α β - gaussianQuadrant ρ α' β'| ≤ |α - α'| + |β - β'| :=
  (abs_sub_le _ (gaussianQuadrant ρ α' β) _).trans
    (add_le_add (abs_gaussianQuadrant_sub_le_left ρ α α' β)
      (abs_gaussianQuadrant_sub_le_right hρ α' β β'))

/-- [O'Donnell, Exercise 11.19][ODonnell2014]: `Λ_ρ(α) = Λ_ρ(α, α)` is a `2`-Lipschitz function
of `α`. -/
theorem lipschitzWith_gaussianQuadrant_diag {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    LipschitzWith 2 fun α => gaussianQuadrant ρ α α := by
  refine LipschitzWith.of_dist_le_mul fun α α' => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat, two_mul]
  exact abs_gaussianQuadrant_sub_le hρ α α α' α'

/-- `Λ_ρ` is `2`-Lipschitz on the plane, with the sup metric, for `|ρ| ≤ 1`. -/
theorem lipschitzWith_gaussianQuadrant {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    LipschitzWith 2 fun q : ℝ × ℝ => gaussianQuadrant ρ q.1 q.2 := by
  refine LipschitzWith.of_dist_le_mul fun q q' => ?_
  rw [Real.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat, two_mul]
  exact (abs_gaussianQuadrant_sub_le hρ _ _ _ _).trans
    (add_le_add (le_max_left _ _) (le_max_right _ _))

/-- `Λ_ρ` is jointly continuous for `|ρ| ≤ 1`. -/
theorem continuous_gaussianQuadrant {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    Continuous fun q : ℝ × ℝ => gaussianQuadrant ρ q.1 q.2 :=
  (lipschitzWith_gaussianQuadrant hρ).continuous

/-- `Λ_ρ` is jointly measurable for `|ρ| ≤ 1`. -/
theorem measurable_gaussianQuadrant {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    Measurable fun q : ℝ × ℝ => gaussianQuadrant ρ q.1 q.2 :=
  (continuous_gaussianQuadrant hρ).measurable

/-- `x ↦ Λ_ρ(a x, b x)` is measurable for measurable `a`, `b` and `|ρ| ≤ 1`. -/
theorem _root_.Measurable.gaussianQuadrant {α : Type*} [MeasurableSpace α] {ρ : ℝ}
    (hρ : |ρ| ≤ 1) {a b : α → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => gaussianQuadrant ρ (a x) (b x) :=
  (measurable_gaussianQuadrant hρ).comp (ha.prodMk hb)

/-! ### Exercise 11.19 (a): halfspaces -/

variable {ι : Type*} [Fintype ι]

/-- The halfspace `a ⬝ᵥ z ≤ b`, for `a ≠ 0`, has standard Gaussian volume `Φ (b / √(a ⬝ᵥ a))`,
where `√(a ⬝ᵥ a)` is the Euclidean norm of `a`. -/
theorem measureReal_pi_gaussianReal_setOf_dotProduct_le {a : ι → ℝ} (ha : a ≠ 0) (b : ℝ) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {z | a ⬝ᵥ z ≤ b} = Φ (b / √(a ⬝ᵥ a)) := by
  have h := map_measureReal_apply (μ := Measure.pi fun _ : ι => gaussianReal 0 1)
    (f := (a ⬝ᵥ ·)) (by fun_prop) (measurableSet_Iic (a := b))
  rw [pi_gaussianReal_map_dotProduct_eq_map_const_mul, map_measureReal_apply (by fun_prop)
    measurableSet_Iic, preimage_const_mul_Iic₀ b (sqrt_dotProduct_self_pos ha)] at h
  rw [cdf_eq_real, h]
  rfl

/-- **Noise stability of halfspaces** [O'Donnell, Exercise 11.19][ODonnell2014]: the indicator of
a halfspace `H = {z | a ⬝ᵥ z ≤ b}`, for `a ≠ 0`, of Gaussian volume `α` has
`Stab_ρ[1_H] = Λ_ρ(α)`. -/
theorem gaussianNoiseStability_indicator_setOf_dotProduct_le (ρ : ℝ) {a : ι → ℝ} (ha : a ≠ 0)
    (b : ℝ) :
    gaussianNoiseStability ρ ({z | a ⬝ᵥ z ≤ b}.indicator 1) =
      gaussianQuadrant ρ ((Measure.pi fun _ : ι => gaussianReal 0 1).real {z | a ⬝ᵥ z ≤ b})
        ((Measure.pi fun _ : ι => gaussianReal 0 1).real {z | a ⬝ᵥ z ≤ b}) := by
  have hpos := sqrt_dotProduct_self_pos ha
  have hind : ({z | a ⬝ᵥ z ≤ b}.indicator 1 : (ι → ℝ) → ℝ) =
      fun z => (Iic b).indicator 1 (a ⬝ᵥ z) := rfl
  have hscale : ∀ x, (Iic b).indicator (1 : ℝ → ℝ) (√(a ⬝ᵥ a) * x) =
      (Iic (b / √(a ⬝ᵥ a))).indicator 1 x := fun x => by
    simp only [indicator_apply, mem_Iic, Pi.one_apply, le_div_iff₀ hpos, mul_comm x]
  rw [measureReal_pi_gaussianReal_setOf_dotProduct_le ha, gaussianQuadrant_cdf_cdf, hind,
    gaussianNoiseStability_comp_dotProduct ρ a (measurable_one.indicator measurableSet_Iic)]
  simp only [hscale]
  exact integral_indicator_Iic_mul_indicator_Iic _ _ _

/-- **Noise stability of halfspaces** [O'Donnell, Exercise 11.19][ODonnell2014]: the indicator of
a halfspace `H = {z | a ⬝ᵥ z ≤ b}`, for `a ≠ 0`, of Gaussian volume `α` has
`Stab_ρ[1_H] = Λ_ρ(α)`; this form takes the volume as a hypothesis. -/
theorem gaussianNoiseStability_indicator_setOf_dotProduct_le_of_measureReal_eq (ρ : ℝ)
    {a : ι → ℝ} (ha : a ≠ 0) {b α : ℝ}
    (hα : (Measure.pi fun _ : ι => gaussianReal 0 1).real {z | a ⬝ᵥ z ≤ b} = α) :
    gaussianNoiseStability ρ ({z | a ⬝ᵥ z ≤ b}.indicator 1) = gaussianQuadrant ρ α α := by
  rw [gaussianNoiseStability_indicator_setOf_dotProduct_le ρ ha, hα]

end ProbabilityTheory
