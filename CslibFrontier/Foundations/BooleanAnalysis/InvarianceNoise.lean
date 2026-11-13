/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Invariance
public import CslibFrontier.Foundations.BooleanAnalysis.StableInfluence
public import CslibFrontier.Foundations.Probability.Multilinear.InvarianceLipschitz
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Invariance on the cube for Lipschitz tests and noise-smoothed functions

[O'Donnell, Corollaries 11.68 and 11.69][ODonnell2014]. Write `f(y)` for the Fourier expansion of
`f : (ι → Bool) → ℝ` evaluated at independent random variables `y i` whose laws `μ i` satisfy
Hypothesis 11.65 (for instance standard Gaussians, `hasInvarianceMoments_gaussianReal`), and
`E[ψ(f(x))]` for the expectation `𝔼 x, ψ (f x)` over uniformly random bits.

Inequality (11.31) is Corollary 11.68 on the cube: if `f` has degree at most `k`, `Var[f] ≤ 1`
and every influence is at most `ε`, then `|E[ψ(f(x))] - E[ψ(f(y))]| ≤ 9 K · 2ᵏ · ε^(1/4)` for
`K`-Lipschitz `ψ`. Splitting `f = f^{≤k} + f^{>k}` extends it to all `f`: if `Var[f] ≤ 1` and
`f^{≤k}` has influences at most `ε`, then
`|E[ψ(f(x))] - E[ψ(f(y))]| ≤ 9 K · 2ᵏ · ε^(1/4) + 2 K ‖f^{>k}‖₂` (inequality (11.32)), where
`‖f^{>k}‖₂² = ∑_{|S| > k} f̂(S)²`.

Applied to `f = T_{1-δ} h` for `h` with `Var[h] ≤ 1` and no `(ε, δ)`-notable coordinates, i.e.
`Inf_i^{(1-δ)}[h] ≤ ε` for every `i` [O'Donnell, Definition 6.9][ODonnell2014], the tail is at
most `(1 - δ)ᵏ` for every `k`, which gives inequality (11.33) (the book weakens `(1 - δ)ᵏ` to
`exp(-k δ)`); choosing `k = ⌊ln(1/ε) / 3⌋` yields
`|E[ψ(T_{1-δ}h(x))] - E[ψ(T_{1-δ}h(y))]| ≤ 15 K · ε^(δ/3)` for `ε ≤ 1` and `δ ≤ 1/20`.

## Main results

* `Cslib.BitString.abs_expect_comp_sub_integral_comp_multilinearEval_le_of_lipschitzWith`:
  Corollary 11.68 on the cube, inequality (11.31).
* `Cslib.BitString.abs_expect_comp_sub_le_sqrt`: Lipschitz tests of two functions on the cube
  differ by at most `K` times their `L²` distance.
* `Cslib.BitString.abs_expect_comp_sub_integral_comp_multilinearEval_le_add_sqrt`:
  Corollary 11.69, first statement, inequality (11.32).
* `Cslib.BitString.abs_expect_comp_noiseOp_sub_integral_comp_multilinearEval_le_add_pow`:
  inequality (11.33), with `(1 - δ)ᵏ` in place of the book's `exp(-k δ)`.
* `Cslib.BitString.abs_expect_comp_noiseOp_sub_integral_comp_multilinearEval_le_of_lipschitzWith`:
  Corollary 11.69, second statement.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real
open scoped BigOperators NNReal

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] {ψ : ℝ → ℝ} {K : ℝ≥0}

/-! ### Corollary 11.68 on the cube -/

/-- **Corollary 11.68 on the cube**, inequality (11.31) of
[O'Donnell, Corollary 11.68][ODonnell2014]: if `f` on the cube has degree at most `k`, variance
at most `1` and every influence at most `ε ≥ 0`, then for every `K`-Lipschitz `ψ : ℝ → ℝ`, the
expectation of `ψ ∘ f` at uniformly random bits differs from that of `ψ` applied to the Fourier
expansion of `f` at `y` by at most `9 K · 2ᵏ · ε^(1/4)`, where the `y i` are independent with laws
`μ i` satisfying Hypothesis 11.65. The book leaves the hypothesis `Var[f] ≤ 1` implicit in
(11.31); it is inherited from Corollary 11.68. -/
theorem abs_expect_comp_sub_integral_comp_multilinearEval_le_of_lipschitzWith
    (hμ : ∀ i, HasInvarianceMoments (μ i)) {f : (ι → Bool) → ℝ} {k : ℕ} (hf : totalDegree f ≤ k)
    (hvar : 𝔼 x, (f x - 𝔼 y, f y) ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, influence i f ≤ ε)
    (hψ : LipschitzWith K ψ) :
    |𝔼 x, ψ (f x) - ∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ| ≤
      9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ) := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq] at hvar
  have h := abs_integral_comp_multilinearEval_sub_le_of_lipschitzWith (fun _ => rademacher) μ
    (fun _ => hasInvarianceMoments_rademacher) hμ (totalDegree_le_iff_fourierCoeff_eq_zero.1 hf)
    hvar hε0 (fun i => (multilinearInfluence_fourierCoeff f i).trans_le (hε i)) hψ
  simpa only [integral_pi_rademacher, multilinearEval_fourierCoeff_signVal] using h

/-- On the cube, `|𝔼 x, ψ (f x) - 𝔼 x, ψ (g x)| ≤ K ‖f - g‖₂` for `K`-Lipschitz `ψ`, where
`‖f - g‖₂² = ∑ S, (f̂(S) - ĝ(S))²`. -/
theorem abs_expect_comp_sub_le_sqrt (hψ : LipschitzWith K ψ) (f g : (ι → Bool) → ℝ) :
    |𝔼 x, ψ (f x) - 𝔼 x, ψ (g x)| ≤
      K * √(∑ S, (fourierCoeff f S - fourierCoeff g S) ^ 2) := by
  have h := abs_integral_comp_multilinearEval_sub_le_sqrt (fun _ : ι => rademacher)
    (fun _ => hasInvarianceMoments_rademacher) hψ (fourierCoeff f) (fourierCoeff g)
  simpa only [integral_pi_rademacher, multilinearEval_fourierCoeff_signVal] using h

/-! ### Corollary 11.69, first statement -/

/-- **Corollary 11.69**, first statement, inequality (11.32) of
[O'Donnell, Corollary 11.69][ODonnell2014]: if `f` on the cube has variance at most `1` and its
low-degree part `f^{≤k}` has every influence `Inf_t[f^{≤k}] = ∑_{t ∈ S, |S| ≤ k} f̂(S)²` at most
`ε ≥ 0`, then for every `K`-Lipschitz `ψ : ℝ → ℝ`,
`|𝔼 x, ψ (f x) - E[ψ(f(y))]| ≤ 9 K · 2ᵏ · ε^(1/4) + 2 K ‖f^{>k}‖₂`, where
`‖f^{>k}‖₂ = √(∑_{|S| > k} f̂(S)²)` and `f(y)` is the Fourier expansion of `f` at independent `y i`
with laws `μ i` satisfying Hypothesis 11.65. -/
theorem abs_expect_comp_sub_integral_comp_multilinearEval_le_add_sqrt
    (hμ : ∀ i, HasInvarianceMoments (μ i)) {f : (ι → Bool) → ℝ} (k : ℕ)
    (hvar : 𝔼 x, (f x - 𝔼 y, f y) ^ 2 ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ t, ∑ S with t ∈ S ∧ #S ≤ k, fourierCoeff f S ^ 2 ≤ ε) (hψ : LipschitzWith K ψ) :
    |𝔼 x, ψ (f x) - ∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ| ≤
      9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ) + 2 * K * √(∑ S with k < #S, fourierCoeff f S ^ 2) := by
  set G : Finset ι → ℝ := fun S => if #S ≤ k then fourierCoeff f S else 0
  set g : (ι → Bool) → ℝ := fun x => ∑ S, G S * chi ℝ S x
  have hg : fourierCoeff g = G := funext (fourierCoeff_sum_mul_chi G)
  have htail : ∑ S, (fourierCoeff f S - fourierCoeff g S) ^ 2 =
      ∑ S with k < #S, fourierCoeff f S ^ 2 := by
    rw [hg, sum_filter]
    refine sum_congr rfl fun S _ => ?_
    by_cases hS : #S ≤ k <;> simp [G, hS, not_lt.2, lt_of_not_ge]
  have hlow : |𝔼 x, ψ (g x) - ∫ y, ψ (multilinearEval (fourierCoeff g) y) ∂Measure.pi μ| ≤
      9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ) := by
    refine abs_expect_comp_sub_integral_comp_multilinearEval_le_of_lipschitzWith μ hμ
      (totalDegree_le_iff_fourierCoeff_eq_zero.2 fun S hS => ?_) ?_ hε0 (fun t => ?_) hψ
    · simp [hg, G, not_le.2 hS]
    · refine le_trans ?_ hvar
      rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq, expect_sub_expect_sq_eq_sum_fourierCoeff_sq,
        hg]
      refine sum_le_sum fun S _ => ?_
      by_cases hS : #S ≤ k <;> simp [G, hS, sq_nonneg]
    · rw [influence_eq_sum_fourierCoeff_sq, hg]
      refine le_trans (le_of_eq ?_) (hε t)
      rw [← filter_filter, sum_filter (fun S : Finset ι => #S ≤ k)]
      refine sum_congr rfl fun S _ => ?_
      by_cases hS : #S ≤ k <;> simp [G, hS]
  have h1 := abs_expect_comp_sub_le_sqrt hψ f g
  have h2 := abs_integral_comp_multilinearEval_sub_le_sqrt μ hμ hψ (fourierCoeff f)
    (fourierCoeff g)
  rw [htail] at h1 h2
  have h3 := abs_sub_le (𝔼 x, ψ (f x)) (𝔼 x, ψ (g x))
    (∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ)
  have h4 := abs_sub_le (𝔼 x, ψ (g x))
    (∫ y, ψ (multilinearEval (fourierCoeff g) y) ∂Measure.pi μ)
    (∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ)
  rw [abs_sub_comm (∫ y, ψ (multilinearEval (fourierCoeff g) y) ∂_)] at h4
  linarith

/-! ### Corollary 11.69, second statement -/

/-- Inequality (11.33) of [O'Donnell, Corollary 11.69][ODonnell2014]: if `h` on the cube has
variance at most `1` and no `(ε, δ)`-notable coordinates, i.e. `Inf_i^{(1-δ)}[h] ≤ ε` for every
`i`, with `0 ≤ δ ≤ 1` and `ε ≥ 0`, then for every `k` and every `K`-Lipschitz `ψ`,
`|E[ψ(T_{1-δ}h(x))] - E[ψ(T_{1-δ}h(y))]| ≤ 9 K · 2ᵏ · ε^(1/4) + 2 K (1 - δ)ᵏ`, where
`T_{1-δ}h(y)` is the Fourier expansion of `T_{1-δ}h` at independent `y i` with laws `μ i`
satisfying Hypothesis 11.65. This is the sharper form of (11.33): the book then bounds
`(1 - δ)ᵏ ≤ exp(-k δ)`. -/
theorem abs_expect_comp_noiseOp_sub_integral_comp_multilinearEval_le_add_pow
    (hμ : ∀ i, HasInvarianceMoments (μ i)) {h : (ι → Bool) → ℝ} (k : ℕ)
    (hvar : 𝔼 x, (h x - 𝔼 y, h y) ^ 2 ≤ 1) {ε δ : ℝ} (hε0 : 0 ≤ ε) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hε : ∀ i, stableInfluence (1 - δ) i h ≤ ε) (hψ : LipschitzWith K ψ) :
    |𝔼 x, ψ (noiseOp (1 - δ) h x) -
        ∫ y, ψ (multilinearEval (fourierCoeff (noiseOp (1 - δ) h)) y) ∂Measure.pi μ| ≤
      9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ) + 2 * K * (1 - δ) ^ k := by
  have hρ0 : 0 ≤ 1 - δ := by linarith
  have hρ1 : 1 - δ ≤ 1 := by linarith
  have hvar' : ∑ S with S ≠ ∅, fourierCoeff h S ^ 2 ≤ 1 := by
    rwa [← expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
  refine (abs_expect_comp_sub_integral_comp_multilinearEval_le_add_sqrt μ hμ k ?_ hε0
    (fun t => ?_) hψ).trans ?_
  · exact (expect_sub_expect_sq_noiseOp_le (abs_le.2 ⟨by linarith, hρ1⟩) h).trans hvar
  · refine le_trans ?_ ((influence_noiseOp_le_stableInfluence hρ0 hρ1 t h).trans (hε t))
    rw [influence_eq_sum_fourierCoeff_sq, ← filter_filter]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  · gcongr
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∑ S with k < #S, fourierCoeff (noiseOp (1 - δ) h) S ^ 2
        ≤ ∑ S with S ≠ ∅, ((1 - δ) ^ k) ^ 2 * fourierCoeff h S ^ 2 := by
          refine sum_le_sum_of_subset_of_nonneg (fun S hS => ?_) (fun _ _ _ => by positivity)
            |>.trans' (sum_le_sum fun S hS => ?_)
          · simp only [mem_filter, mem_univ, true_and] at hS ⊢
            rintro rfl
            simp at hS
          · simp only [mem_filter, mem_univ, true_and] at hS
            rw [fourierCoeff_noiseOp, mul_pow, ← pow_mul, ← pow_mul]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ0 hρ1 (by omega))
              (sq_nonneg _)
      _ = ((1 - δ) ^ k) ^ 2 * ∑ S with S ≠ ∅, fourierCoeff h S ^ 2 := (mul_sum _ _ _).symm
      _ ≤ ((1 - δ) ^ k) ^ 2 := mul_le_of_le_one_right (by positivity) hvar'

/-- The arithmetic of [O'Donnell, Corollary 11.69][ODonnell2014]: for `0 < ε ≤ 1`,
`0 ≤ δ ≤ 1/20` and `k = ⌊ln(1/ε) / 3⌋`, both `2ᵏ ε^(1/4) ≤ ε^(δ/3)` and
`(1 - δ)ᵏ ≤ 3 ε^(δ/3)`. -/
private theorem pow_mul_rpow_le_and_pow_le {ε δ : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hδ₀ : 0 ≤ δ)
    (hδ : δ ≤ 1 / 20) :
    (2 : ℝ) ^ ⌊-log ε / 3⌋₊ * ε ^ (1 / 4 : ℝ) ≤ ε ^ (δ / 3) ∧
      (1 - δ) ^ ⌊-log ε / 3⌋₊ ≤ 3 * ε ^ (δ / 3) := by
  set L := -log ε / 3
  have hlog : log ε ≤ 0 := log_nonpos hε₀.le hε₁
  have hL : 0 ≤ L := by simp only [L]; linarith
  set k := ⌊L⌋₊
  have hkL : (k : ℝ) ≤ L := Nat.floor_le hL
  have hLk : L < k + 1 := Nat.lt_floor_add_one L
  rw [rpow_def_of_pos hε₀, rpow_def_of_pos hε₀]
  constructor
  · have h2 : (2 : ℝ) ^ k = exp (k * log 2) := by
      rw [← rpow_natCast, rpow_def_of_pos two_pos, mul_comm]
    rw [h2, ← exp_add]
    refine exp_le_exp.2 ?_
    have hl2 : log 2 < 0.6931471808 := log_two_lt_d9
    have hl2' : 0 < log 2 := log_pos one_lt_two
    have : (k : ℝ) * log 2 ≤ L * log 2 := mul_le_mul_of_nonneg_right hkL hl2'.le
    simp only [L] at this
    nlinarith
  · calc (1 - δ) ^ k ≤ exp (-δ) ^ k := by
          gcongr
          · linarith
          · linarith [add_one_le_exp (-δ)]
      _ = exp (-δ * k) := by rw [← exp_nat_mul]; ring_nf
      _ ≤ exp δ * exp (log ε * (δ / 3)) := by
          rw [← exp_add]
          refine exp_le_exp.2 ?_
          simp only [L] at hLk
          nlinarith
      _ ≤ 3 * exp (log ε * (δ / 3)) := by
          gcongr
          calc exp δ ≤ exp 1 := exp_le_exp.2 (by linarith)
            _ ≤ 3 := by linarith [exp_one_lt_d9]

/-- **Corollary 11.69**, second statement [O'Donnell, Corollary 11.69][ODonnell2014]: if `h` on
the cube has variance at most `1` and no `(ε, δ)`-notable coordinates, i.e.
`Inf_i^{(1-δ)}[h] ≤ ε` for every `i`, with `0 ≤ ε ≤ 1` and `0 ≤ δ ≤ 1/20`, then for every
`K`-Lipschitz `ψ : ℝ → ℝ`, `|E[ψ(T_{1-δ}h(x))] - E[ψ(T_{1-δ}h(y))]| ≤ 15 K · ε^(δ/3)`, where
`T_{1-δ}h(y)` is the Fourier expansion of `T_{1-δ}h` at independent `y i` with laws `μ i`
satisfying Hypothesis 11.65 (for instance standard Gaussians). -/
theorem abs_expect_comp_noiseOp_sub_integral_comp_multilinearEval_le_of_lipschitzWith
    (hμ : ∀ i, HasInvarianceMoments (μ i)) {h : (ι → Bool) → ℝ}
    (hvar : 𝔼 x, (h x - 𝔼 y, h y) ^ 2 ≤ 1) {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 20) (hε : ∀ i, stableInfluence (1 - δ) i h ≤ ε) (hψ : LipschitzWith K ψ) :
    |𝔼 x, ψ (noiseOp (1 - δ) h x) -
        ∫ y, ψ (multilinearEval (fourierCoeff (noiseOp (1 - δ) h)) y) ∂Measure.pi μ| ≤
      15 * K * ε ^ (δ / 3) := by
  have hb (k : ℕ) := abs_expect_comp_noiseOp_sub_integral_comp_multilinearEval_le_add_pow μ hμ k
    hvar hε0 hδ0 (by linarith) hε hψ
  have hK : (0 : ℝ) ≤ K := K.2
  rcases hε0.eq_or_lt with rfl | hε0
  · rcases hδ0.eq_or_lt with rfl | hδ0
    · refine (hb 0).trans ?_
      rw [zero_div, rpow_zero, zero_rpow (by norm_num), pow_zero, pow_zero]
      linarith
    rw [zero_rpow (by positivity), mul_zero]
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith)
      (by linarith : 1 - δ < 1)).const_mul (2 * K : ℝ)
    rw [mul_zero] at ht
    exact ge_of_tendsto' ht fun k => by simpa [zero_rpow] using hb k
  obtain ⟨h1, h2⟩ := pow_mul_rpow_le_and_pow_le hε0 hε1 hδ0 hδ
  refine (hb ⌊-log ε / 3⌋₊).trans ?_
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 9 * K)
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * K)
  linarith

end Cslib.BitString
