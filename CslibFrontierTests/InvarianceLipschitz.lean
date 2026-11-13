/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import CslibFrontier.Foundations.Analysis.Calculus.LipschitzSmoothing
import CslibFrontier.Foundations.BooleanAnalysis.InvarianceNoise
import CslibFrontier.Foundations.Probability.Multilinear.InvarianceLipschitz

/-! # Tests for invariance with Lipschitz tests and noise-smoothed functions

Linear forms `∑ aᵢ xᵢ` as formal multilinear polynomials; the moving-average smoothing of the
`1`-Lipschitz function `|·|` (Proposition 11.58); Corollary 11.68 for Lipschitz tests, where the
normalized sum of `m = 100⁴` variables and the clamp `u ↦ min 1 (max 0 u)` give the bound `0.18`,
below the trivial bound `1`, and its form (11.31) on the cube; the monotonicity of stable
influences in the rate and under noise; and Corollary 11.69, for a linear form plus a scaled
parity (a high-degree tail) and for `T_{1-δ}` of linear forms, where the normalized sum of
`m = 100⁶⁰` signs with `δ = 1/20` gives the bound `0.15`. -/

namespace CslibFrontierTests.InvarianceLipschitz

open MeasureTheory ProbabilityTheory Finset Cslib.BitString
open scoped BigOperators

/-- The law of `n` independent uniformly random signs. -/
noncomputable abbrev signs (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => rademacher

/-- The law of `n` independent standard Gaussians. -/
noncomputable abbrev gaussians (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-! ### Linear forms -/

/-- The coefficients of the linear form `∑ aᵢ xᵢ`. -/
def linearForm {n : ℕ} (a : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i, if S = {i} then a i else 0

/-- The coefficient of a singleton `{t}` is `a t`. -/
theorem linearForm_singleton {n : ℕ} (a : Fin n → ℝ) (t : Fin n) : linearForm a {t} = a t := by
  rw [linearForm, Fintype.sum_eq_single t fun i hi => by simp [Ne.symm hi]]
  simp

/-- Only singletons have nonzero coefficients. -/
theorem linearForm_eq_zero {n : ℕ} (a : Fin n → ℝ) {S : Finset (Fin n)} (hS : #S ≠ 1) :
    linearForm a S = 0 :=
  sum_eq_zero fun i _ => by simp [show S ≠ {i} from fun h => hS (by simp [h])]

/-- The influence of `t` on `∑ aᵢ xᵢ` is `a t ^ 2`. -/
theorem multilinearInfluence_linearForm {n : ℕ} (a : Fin n → ℝ) (t : Fin n) :
    multilinearInfluence (linearForm a) t = a t ^ 2 := by
  rw [multilinearInfluence_def, sum_eq_single_of_mem {t} (by simp) fun S hS hSt => ?_,
    linearForm_singleton]
  rw [linearForm_eq_zero a fun h => hSt ?_, sq, zero_mul]
  obtain ⟨i, rfl⟩ := card_eq_one.1 h
  simp_all

/-- The squared coefficients of `∑ aᵢ xᵢ` sum to `∑ aᵢ²`. -/
theorem sum_linearForm_sq {n : ℕ} (a : Fin n → ℝ) : ∑ S, linearForm a S ^ 2 = ∑ i, a i ^ 2 := by
  have hcard : ∀ S, (#S : ℝ) * linearForm a S ^ 2 = linearForm a S ^ 2 := fun S => by
    by_cases h : #S = 1
    · simp [h]
    · simp [linearForm_eq_zero a h]
  have h := sum_multilinearInfluence (linearForm a)
  simp only [hcard, multilinearInfluence_linearForm] at h
  exact h.symm

/-- The variance of `∑ aᵢ xᵢ` is at most `∑ aᵢ²`. -/
theorem sum_ne_empty_linearForm_sq_le {n : ℕ} (a : Fin n → ℝ) :
    ∑ S with S ≠ ∅, linearForm a S ^ 2 ≤ ∑ i, a i ^ 2 :=
  (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _).trans_eq
    (sum_linearForm_sq a)

/-- The linear form `linearForm a` evaluates to `∑ aᵢ vᵢ`. -/
theorem multilinearEval_linearForm {n : ℕ} (a : Fin n → ℝ) (v : Fin n → ℝ) :
    multilinearEval (linearForm a) v = ∑ i, a i * v i := by
  simp only [multilinearEval_def, linearForm, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

/-! ### Smoothing Lipschitz functions (Proposition 11.58) -/

/-- The absolute value is `1`-Lipschitz (Mathlib's `lipschitzWith_one_norm`). -/
theorem lipschitzWith_abs : LipschitzWith 1 fun u : ℝ => |u| :=
  lipschitzWith_one_norm

/-- The four-fold moving average of `|·|` with window `1 / 4` is `C⁴`, within `1` of `|·|`, and
has fourth derivative at most `8 / (1 / 4)³ = 512`. -/
example : ContDiff ℝ 4 ((Real.movingAverage (1 / 4))^[4] fun u : ℝ => |u|) ∧
    (∀ s, |(Real.movingAverage (1 / 4))^[4] (fun u : ℝ => |u|) s - (|s|)| ≤ 1) ∧
    ∀ s, |iteratedDeriv 4 ((Real.movingAverage (1 / 4))^[4] fun u : ℝ => |u|) s| ≤ 512 := by
  refine ⟨Real.contDiff_iterate_movingAverage continuous_abs 4, fun s => ?_, fun s => ?_⟩
  · have h := lipschitzWith_abs.abs_iterate_movingAverage_sub_le (by norm_num : (0 : ℝ) < 1 / 4)
      4 s
    norm_num at h
    exact h
  · have h := lipschitzWith_abs.abs_iteratedDeriv_iterate_movingAverage_le
      (by norm_num : (0 : ℝ) < 1 / 4) (k := 3) (m := 4) (by norm_num) s
    norm_num at h
    exact h

/-- A moving average of the `1`-Lipschitz function `|·|` is `1`-Lipschitz. -/
example : LipschitzWith 1 (Real.movingAverage (1 / 4) fun u : ℝ => |u|) :=
  lipschitzWith_abs.movingAverage _

/-- The moving average of `|·|` over `[0, 1]` at `0` is `∫₀¹ |t| dt = 1 / 2`. -/
example : Real.movingAverage 1 (fun u : ℝ => |u|) 0 = 1 / 2 := by
  rw [Real.movingAverage_def, inv_one, one_mul]
  simp only [zero_add]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => t) fun t ht => by
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact abs_of_nonneg ht.1]
  norm_num

/-- Proposition 11.58 for `|·|` with `η = 1` and derivatives up to order `4`: a `C⁴` function
within `1` of `|·|` whose derivatives of orders `1` to `4` are at most `8ᵏ⁻¹`. -/
example : ∃ ψ' : ℝ → ℝ, ContDiff ℝ 4 ψ' ∧ (∀ s, |ψ' s - (|s|)| ≤ 1) ∧
    ∀ k, k < 4 → ∀ s, |iteratedDeriv (k + 1) ψ' s| ≤ 8 ^ k := by
  obtain ⟨ψ', h1, h2, h3⟩ := lipschitzWith_abs.exists_contDiff_smoothing 4 one_pos
  refine ⟨ψ', h1, fun s => by simpa using h2 s, fun k hk s => ?_⟩
  have := h3 k hk s
  norm_num at this
  exact this

/-! ### Corollary 11.68: Lipschitz test functions -/

/-- The clamp `u ↦ min 1 (max 0 u)` is `1`-Lipschitz. -/
theorem lipschitzWith_clamp : LipschitzWith 1 fun u : ℝ => min 1 (max 0 u) :=
  (LipschitzWith.id.const_max 0).const_min 1

/-- Corollary 11.68 for the normalized sum `∑ xᵢ / √m` and the clamp: replacing signs by
Gaussians changes the expectation by at most `9 · 2 · (1 / m)^(1/4) = 18 m^(-1/4)`. -/
theorem abs_integral_clamp_normalizedSum_sub_le (m : ℕ) (hm : 0 < m) :
    |∫ v, min 1 (max 0 (∑ i, (√m)⁻¹ * v i)) ∂signs m -
        ∫ v, min 1 (max 0 (∑ i, (√m)⁻¹ * v i)) ∂gaussians m| ≤
      18 * ((m : ℝ)⁻¹) ^ (1 / 4 : ℝ) := by
  have hsq : ((√(m : ℝ))⁻¹) ^ 2 = (m : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hvar : ∑ _i : Fin m, ((√(m : ℝ))⁻¹) ^ 2 ≤ 1 := by
    rw [hsq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hm']
  have h := abs_integral_comp_multilinearEval_sub_le_of_lipschitzWith _ _
    (fun _ => hasInvarianceMoments_rademacher) (fun _ => hasInvarianceMoments_gaussianReal)
    (k := 1) (c := linearForm fun _ : Fin m => (√(m : ℝ))⁻¹)
    (fun S hS => linearForm_eq_zero _ (by omega)) ((sum_ne_empty_linearForm_sq_le _).trans hvar)
    (ε := (m : ℝ)⁻¹) (by positivity) (fun t => ((multilinearInfluence_linearForm _ t).trans hsq).le)
    lipschitzWith_clamp
  simp only [multilinearEval_linearForm] at h
  refine h.trans_eq ?_
  norm_num

/-- For `m = 100⁴` variables the bound is `18 / 100`, well below the trivial bound `1` for a
difference of two expectations of the clamp, which takes values in `[0, 1]`. -/
example : |∫ v, min 1 (max 0 (∑ i, (√(100 ^ 4 : ℕ))⁻¹ * v i)) ∂signs (100 ^ 4) -
      ∫ v, min 1 (max 0 (∑ i, (√(100 ^ 4 : ℕ))⁻¹ * v i)) ∂gaussians (100 ^ 4)| ≤ 18 / 100 ∧
    (18 / 100 : ℝ) < 1 := by
  refine ⟨(abs_integral_clamp_normalizedSum_sub_le (100 ^ 4) (by norm_num)).trans_eq ?_,
    by norm_num⟩
  rw [Nat.cast_pow, ← inv_pow, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
  norm_num

/-- Corollary 11.68 for any laws satisfying Hypothesis 11.65, with the `1`-Lipschitz test `|·|`. -/
example (n k : ℕ) (μ ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (hμ : ∀ i, HasInvarianceMoments (μ i))
    (hν : ∀ i, HasInvarianceMoments (ν i)) (c : Finset (Fin n) → ℝ) (hc : ∀ S, k < #S → c S = 0)
    (hvar : ∑ S with S ≠ ∅, c S ^ 2 ≤ 1) (ε : ℝ) (hε₀ : 0 ≤ ε)
    (hε : ∀ t, multilinearInfluence c t ≤ ε) :
    |∫ z, |multilinearEval c z| ∂Measure.pi μ - ∫ z, |multilinearEval c z| ∂Measure.pi ν| ≤
      9 * 2 ^ k * ε ^ (1 / 4 : ℝ) := by
  simpa using abs_integral_comp_multilinearEval_sub_le_of_lipschitzWith μ ν hμ hν hc hvar hε₀ hε
    lipschitzWith_abs

/-- Inequality (11.31) with the clamp: for a function on the cube of degree at most `k`, variance
at most `1` and influences at most `ε`, the clamped values on the cube and at Gaussians have
expectations within `9 · 2ᵏ · ε^(1/4)`. -/
example (n k : ℕ) (f : (Fin n → Bool) → ℝ) (hf : totalDegree f ≤ k)
    (hvar : 𝔼 x, (f x - 𝔼 y, f y) ^ 2 ≤ 1) (ε : ℝ) (hε₀ : 0 ≤ ε)
    (hε : ∀ t, influence t f ≤ ε) :
    |𝔼 x, min 1 (max 0 (f x)) -
        ∫ v, min 1 (max 0 (multilinearEval (fourierCoeff f) v)) ∂gaussians n| ≤
      9 * 2 ^ k * ε ^ (1 / 4 : ℝ) := by
  simpa using abs_expect_comp_sub_integral_comp_multilinearEval_le_of_lipschitzWith _
    (fun _ => hasInvarianceMoments_gaussianReal) hf hvar hε₀ hε lipschitzWith_clamp

/-! ### Corollary 11.69: a high-degree tail and noisy functions -/

/-- The function `∑ aᵢ xᵢ` on the cube. -/
noncomputable def linearFun {n : ℕ} (a : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ S, linearForm a S * chi ℝ S x

/-- The Fourier coefficients of `∑ aᵢ xᵢ`. -/
theorem fourierCoeff_linearFun {n : ℕ} (a : Fin n → ℝ) :
    fourierCoeff (linearFun a) = linearForm a :=
  funext (fourierCoeff_sum_mul_chi _)

/-- Every stable influence of `∑ aᵢ xᵢ` at `i` is `aᵢ²`. -/
theorem stableInfluence_linearFun {n : ℕ} (a : Fin n → ℝ) (ρ : ℝ) (i : Fin n) :
    stableInfluence ρ i (linearFun a) = a i ^ 2 := by
  rw [stableInfluence_eq_sum, fourierCoeff_linearFun, ← multilinearInfluence_linearForm a i,
    multilinearInfluence_def]
  refine sum_congr rfl fun S _ => ?_
  by_cases h : #S = 1
  · simp [h]
  · simp [linearForm_eq_zero a h]

/-- Stable influences increase with the rate and do not increase under noise: for
`f = ∑ aᵢ xᵢ` and `0 ≤ ρ ≤ ρ'`, `Infᵢ^{(ρ)}[T_σ f] ≤ Infᵢ^{(ρ)}[f] = aᵢ² ≤ Infᵢ^{(ρ')}[f]` when
`|σ| ≤ 1`. -/
example {n : ℕ} (a : Fin n → ℝ) (i : Fin n) {ρ ρ' σ : ℝ} (hρ : 0 ≤ ρ) (hρρ' : ρ ≤ ρ')
    (hσ : |σ| ≤ 1) :
    stableInfluence ρ i (noiseOp σ (linearFun a)) ≤ a i ^ 2 ∧
      a i ^ 2 ≤ stableInfluence ρ' i (linearFun a) := by
  rw [← stableInfluence_linearFun a ρ i]
  exact ⟨stableInfluence_noiseOp_le hρ hσ i _, stableInfluence_mono hρ hρρ' i _⟩

/-- Inequality (11.32) for `f = ∑ aᵢ xᵢ + θ χ_{[n+2]}`, a linear form plus a scaled parity, with
`∑ aᵢ² + θ² ≤ 1`, `aᵢ² ≤ ε` and `k = 1`: both the low-degree term `9 · 2 · ε^(1/4)` and the tail
`2 |θ|` appear in the bound for the `1`-Lipschitz clamp. -/
example (n : ℕ) (a : Fin (n + 2) → ℝ) (θ : ℝ) (ha : ∑ i, a i ^ 2 + θ ^ 2 ≤ 1) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε : ∀ i, a i ^ 2 ≤ ε) :
    |𝔼 x, min 1 (max 0 (linearFun a x + θ * chi ℝ univ x)) -
        ∫ v, min 1 (max 0 (multilinearEval
          (fourierCoeff fun x => linearFun a x + θ * chi ℝ univ x) v)) ∂gaussians (n + 2)| ≤
      9 * 2 * ε ^ (1 / 4 : ℝ) + 2 * |θ| := by
  have hf : fourierCoeff (fun x => linearFun a x + θ * chi ℝ univ x) =
      fun S => linearForm a S + θ * if univ = S then 1 else 0 := funext fun S => by
    rw [fourierCoeff_add, fourierCoeff_linearFun, fourierCoeff_const_mul, fourierCoeff_chi]
  have hu : #(univ : Finset (Fin (n + 2))) = n + 2 := by simp
  have hlu : linearForm a univ = 0 := linearForm_eq_zero a (by omega)
  -- away from `univ` the coefficients are those of the linear form
  have hS {S : Finset (Fin (n + 2))} (hS : S ≠ univ) :
      fourierCoeff (fun x => linearFun a x + θ * chi ℝ univ x) S = linearForm a S := by
    simp [hf, Ne.symm hS]
  have h := abs_expect_comp_sub_integral_comp_multilinearEval_le_add_sqrt _
    (fun _ => hasInvarianceMoments_gaussianReal)
    (f := fun x => linearFun a x + θ * chi ℝ univ x) 1 ?_ hε₀ (fun t => ?_) lipschitzWith_clamp
  · have htail : ∑ S with 1 < #S,
        fourierCoeff (fun x => linearFun a x + θ * chi ℝ univ x) S ^ 2 = θ ^ 2 := by
      rw [sum_eq_single_of_mem univ (by simp [hu]) fun S hS' hSu => ?_]
      · simp [hf, hlu]
      · rw [hS hSu, linearForm_eq_zero a (by simp at hS'; omega)]
        simp
    rw [htail, Real.sqrt_sq_eq_abs] at h
    simpa using h
  · rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _).trans
      (le_of_eq_of_le ?_ ha)
    have hpt (S : Finset (Fin (n + 2))) :
        fourierCoeff (fun x => linearFun a x + θ * chi ℝ univ x) S ^ 2 =
          linearForm a S ^ 2 + if S = univ then θ ^ 2 else 0 := by
      by_cases hSu : S = univ
      · simp [hSu, hf, hlu]
      · simp [hS hSu, hSu]
    rw [sum_congr rfl fun S _ => hpt S, sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ _),
      sum_linearForm_sq]
  · refine le_trans ?_ ((multilinearInfluence_linearForm a t).le.trans (hε t))
    rw [multilinearInfluence_def, ← filter_filter]
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _).trans_eq'
      (sum_congr rfl fun S hS' => ?_)
    rw [hS fun h => by simp [h, hu] at hS']

/-- Corollary 11.69, second statement, for a linear form `∑ aᵢ xᵢ` with `∑ aᵢ² ≤ 1` and
`aᵢ² ≤ ε ≤ 1`: it has no `(ε, δ)`-notable coordinates, so for `δ ≤ 1/20` the clamp of
`T_{1-δ}` of it on the cube and at Gaussians have expectations within `15 ε^(δ/3)`. -/
theorem abs_expect_clamp_noiseOp_linearFun_sub_le {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 ≤ 1) (ε δ : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hε : ∀ i, a i ^ 2 ≤ ε)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ 1 / 20) :
    |𝔼 x, min 1 (max 0 (noiseOp (1 - δ) (linearFun a) x)) -
        ∫ v, min 1 (max 0 (multilinearEval (fourierCoeff (noiseOp (1 - δ) (linearFun a))) v))
          ∂gaussians n| ≤ 15 * ε ^ (δ / 3) := by
  have h := abs_expect_comp_noiseOp_sub_integral_comp_multilinearEval_le_of_lipschitzWith _
    (fun _ => hasInvarianceMoments_gaussianReal) ?_ hε₀ hε₁ hδ₀ hδ
    (fun i => (stableInfluence_linearFun a _ i).trans_le (hε i)) lipschitzWith_clamp
  · simpa using h
  · rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq, fourierCoeff_linearFun]
    exact (sum_ne_empty_linearForm_sq_le a).trans ha

/-- Corollary 11.69, second statement, for the normalized sum of `m = 100⁶⁰` signs with
`δ = 1/20`: every coordinate has `(1/20)`-stable influence `1/m`, and the bound
`15 (1/m)^(1/60) = 0.15` beats the trivial bound `1` for the clamp. -/
example : |𝔼 x, min 1 (max 0 (noiseOp (1 - 1 / 20)
      (linearFun fun _ : Fin (100 ^ 60) => (√(100 ^ 60 : ℕ))⁻¹) x)) -
    ∫ v, min 1 (max 0 (multilinearEval (fourierCoeff (noiseOp (1 - 1 / 20)
      (linearFun fun _ : Fin (100 ^ 60) => (√(100 ^ 60 : ℕ))⁻¹))) v))
        ∂gaussians (100 ^ 60)| ≤ 0.15 := by
  have hsq : ((√(100 ^ 60 : ℕ))⁻¹) ^ 2 = ((100 : ℝ) ^ 60)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_num
  refine (abs_expect_clamp_noiseOp_linearFun_sub_le _ ?_ ((100 : ℝ) ^ 60)⁻¹ (1 / 20) (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) (fun _ => hsq.le) (by norm_num)
    le_rfl).trans_eq ?_
  · simp
  · rw [← inv_pow, show (1 / 20 / 3 : ℝ) = ((60 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    norm_num

end CslibFrontierTests.InvarianceLipschitz
