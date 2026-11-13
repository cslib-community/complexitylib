/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Rademacher.Margin
public import Mathlib.Analysis.InnerProductSpace.Basic
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.BitString.Rademacher
import CslibFrontier.Probability.PMF.ToReal

/-!
# Rademacher complexity of bounded-norm linear predictors

For a feature map `φ : Z → E` into a real inner product space, `linearPredictors φ B` is the class
of linear predictors `z ↦ ⟪w, φ z⟫` with `‖w‖ ≤ B`. Its empirical Rademacher complexity on a
sample `S : Fin m → Z` is at most `B √(∑ i, ‖φ (S i)‖²) / m`, hence at most `B R / √m` when every
sample point has `‖φ (S i)‖ ≤ R` [MohriRostamizadehTalwalkar2018, Theorem 5.10]
[ShalevShwartzBenDavid2014, Lemma 26.10]. The proof is the textbook one: for a fixed sign vector
`σ`, Cauchy–Schwarz bounds the supremum over the ball by `B ‖∑ i, σ_i φ (S i)‖`; Jensen's
inequality moves the average inside a square root; and distinct Rademacher signs are uncorrelated
(`Cslib.BitString.expect_norm_sum_signVal_smul_sq`). The bound does not depend on the dimension of
`E`; taking `φ = id` gives the class `{x ↦ ⟪w, x⟫ : ‖w‖ ≤ B}` of the sources.

Combined with the fixed-margin bounds of `CslibFrontier.MachineLearning.Rademacher.Margin`, this
gives the margin bound for linear classifiers [MohriRostamizadehTalwalkar2018, Corollary 5.11,
(5.44)]: with probability at least `1 - δ`, every `w` with `‖w‖ ≤ B` has
`Pr_D[signVal y * ⟪w, φ x⟫ ≤ 0] ≤ R̂_{S, ρ}(w) + 2 B R / (ρ √m) + √(log (1 / δ) / (2 m))`.

The Rademacher API works on finite domains, so the population statements assume `Z` finite (the
sources allow any distribution supported on the ball of radius `R`); `φ` and `E` are arbitrary.
Labels follow `Rademacher/Margin`: the signed margin of `(x, y)` is `signVal y * h x`.

## Main definitions

* `Cslib.MachineLearning.linearPredictors`: the predictors `z ↦ ⟪w, φ z⟫` with `‖w‖ ≤ B`.

## Main results

* `Cslib.MachineLearning.empiricalRademacherComplexity_linearPredictors_le_sqrt`: the bound
  `B √(∑ i, ‖φ (S i)‖²) / m`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_linearPredictors_le`: the bound
  `B R / √m` [MohriRostamizadehTalwalkar2018, Theorem 5.10].
* `Cslib.MachineLearning.rademacherComplexity_linearPredictors_le`: the population form.
* `Cslib.MachineLearning.linearPredictors_margin_bound`: the margin bound
  [MohriRostamizadehTalwalkar2018, Corollary 5.11].
* `Cslib.MachineLearning.linearPredictors_empirical_margin_bound`: the data-dependent margin bound,
  with `2 B √(∑ i, ‖φ (S i).1‖²) / (ρ m)` and the confidence term of
  [MohriRostamizadehTalwalkar2018, Theorem 5.8, (5.40)].

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Section 5.4, Theorem 5.10 and Corollary 5.11
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Section 26.2, Lemma 26.10
-/

public section

open Finset
open scoped BigOperators RealInnerProductSpace

namespace Cslib.MachineLearning

open Cslib.BitString

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Z : Type*}

/-- The class of **linear predictors** `z ↦ ⟪w, φ z⟫` with weight vector of norm at most `B`, for a
feature map `φ : Z → E` into a real inner product space. -/
def linearPredictors (φ : Z → E) (B : ℝ) : Set (Z → ℝ) :=
  (fun w : E => fun z => ⟪w, φ z⟫) '' Metric.closedBall 0 B

theorem mem_linearPredictors {φ : Z → E} {B : ℝ} {h : Z → ℝ} :
    h ∈ linearPredictors φ B ↔ ∃ w : E, ‖w‖ ≤ B ∧ (fun z => ⟪w, φ z⟫) = h := by
  simp only [linearPredictors, Set.mem_image, Metric.mem_closedBall, dist_zero_right]

/-- A linear predictor with `‖w‖ ≤ B` on features of norm at most `R` is bounded by `B R`. -/
theorem abs_le_of_mem_linearPredictors {φ : Z → E} {B R : ℝ} (hφ : ∀ z, ‖φ z‖ ≤ R)
    {h : Z → ℝ} (hh : h ∈ linearPredictors φ B) (z : Z) : |h z| ≤ B * R := by
  obtain ⟨w, hw, rfl⟩ := mem_linearPredictors.1 hh
  exact (abs_real_inner_le_norm w (φ z)).trans
    (mul_le_mul hw (hφ z) (norm_nonneg _) ((norm_nonneg w).trans hw))

/-- **Rademacher complexity of bounded-norm linear predictors**, trace form: for `B ≥ 0`, the
empirical Rademacher complexity of `linearPredictors φ B` on `S` is at most
`B √(∑ i, ‖φ (S i)‖²) / m`. This is the intermediate bound in the proof of
[MohriRostamizadehTalwalkar2018, Theorem 5.10]. -/
theorem empiricalRademacherComplexity_linearPredictors_le_sqrt (φ : Z → E) {B : ℝ}
    (hB : 0 ≤ B) {m : ℕ} (S : Fin m → Z) :
    empiricalRademacherComplexity (linearPredictors φ B) S ≤
      B * √(∑ i, ‖φ (S i)‖ ^ 2) / m := by
  classical
  have hne : Nonempty (linearPredictors φ B) :=
    ⟨⟨fun z => ⟪0, φ z⟫, mem_linearPredictors.2 ⟨0, by simpa using hB, rfl⟩⟩⟩
  rw [empiricalRademacherComplexity_def, rademacherAverage_eq_expect_ciSup_sum_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg m)
  calc 𝔼 σ : Fin m → Bool, ⨆ h : linearPredictors φ B, ∑ i, (h : Z → ℝ) (S i) * signVal (σ i)
      ≤ 𝔼 σ : Fin m → Bool, B * ‖∑ i, signVal (σ i) • φ (S i)‖ := by
        refine Finset.expect_le_expect fun σ _ => ciSup_le fun h => ?_
        obtain ⟨w, hw, hwh⟩ := mem_linearPredictors.1 h.2
        rw [← hwh]
        calc ∑ i, ⟪w, φ (S i)⟫ * signVal (σ i) = ⟪w, ∑ i, signVal (σ i) • φ (S i)⟫ := by
              rw [inner_sum]
              exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right, mul_comm]
          _ ≤ ‖w‖ * ‖∑ i, signVal (σ i) • φ (S i)‖ := real_inner_le_norm _ _
          _ ≤ B * ‖∑ i, signVal (σ i) • φ (S i)‖ :=
              mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = B * 𝔼 σ : Fin m → Bool, ‖∑ i, signVal (σ i) • φ (S i)‖ := by rw [Finset.mul_expect]
    _ ≤ B * √(∑ i, ‖φ (S i)‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hB
        refine ((le_abs_self _).trans
          (Real.abs_le_sqrt (Finset.sq_expect_le_expect_sq _ _))).trans_eq ?_
        rw [expect_norm_sum_signVal_smul_sq]

/-- **Rademacher complexity of bounded-norm linear predictors**
[MohriRostamizadehTalwalkar2018, Theorem 5.10] [ShalevShwartzBenDavid2014, Lemma 26.10]: for
`B ≥ 0` and a sample whose features have norm at most `R`, the empirical Rademacher complexity of
`linearPredictors φ B` is at most `B R / √m`. -/
theorem empiricalRademacherComplexity_linearPredictors_le (φ : Z → E) {B R : ℝ}
    (hB : 0 ≤ B) {m : ℕ} (S : Fin m → Z) (hS : ∀ i, ‖φ (S i)‖ ≤ R) :
    empiricalRademacherComplexity (linearPredictors φ B) S ≤ B * R / √m := by
  refine (empiricalRademacherComplexity_linearPredictors_le_sqrt φ hB S).trans ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hR : 0 ≤ R := (norm_nonneg _).trans (hS ⟨0, hm⟩)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsum : √(∑ i, ‖φ (S i)‖ ^ 2) ≤ √m * R := by
    rw [Real.sqrt_le_left (by positivity)]
    calc ∑ i, ‖φ (S i)‖ ^ 2 ≤ ∑ _i : Fin m, R ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hS i) 2
      _ = (√m * R) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow,
            Real.sq_sqrt hm'.le]
  calc B * √(∑ i, ‖φ (S i)‖ ^ 2) / m ≤ B * (√m * R) / m := by gcongr
    _ = B * R / √m := by
        have hs : (0 : ℝ) < √m := Real.sqrt_pos.2 hm'
        field_simp
        rw [Real.sq_sqrt hm'.le]
        ring

/-- The Rademacher complexity of `linearPredictors φ B` on a finite domain whose features have norm
at most `R` is at most `B R / √m`. -/
theorem rademacherComplexity_linearPredictors_le [Fintype Z] (D : PMF Z) (φ : Z → E) {B R : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ R) (m : ℕ) :
    rademacherComplexity D (linearPredictors φ B) m ≤ B * R / √m :=
  rademacherComplexity_le D fun S =>
    empiricalRademacherComplexity_linearPredictors_le φ hB S fun i => hφ (S i)

/-- **Margin bound for linear classifiers** [MohriRostamizadehTalwalkar2018, Corollary 5.11,
(5.44)]: on a finite domain with features `φ` of norm at most `R`, for `B ≥ 0`, margin `ρ > 0`
and `m > 0` independent draws from `D : PMF (Z × Bool)`, with probability at least `1 - δ` every
weight vector with `‖w‖ ≤ B` satisfies
`Pr_D[signVal y * ⟪w, φ x⟫ ≤ 0] ≤ R̂_{S, ρ}(w) + 2 B R / (ρ √m) + √(log (1 / δ) / (2 m))`. -/
theorem linearPredictors_margin_bound [Finite Z] (D : PMF (Z × Bool)) {m : ℕ} (hm : 0 < m)
    (φ : Z → E) {B R : ℝ} (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ R) {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ}
    (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ w : E, ‖w‖ ≤ B ∧ empiricalMarginLoss ρ (fun z => ⟪w, φ z⟫) S +
        2 * B * R / (ρ * √m) + √(Real.log (1 / δ) / (2 * m)) <
          (D.toOuterMeasure {p | signVal p.2 * ⟪w, φ p.1⟫ ≤ 0}).toReal}).toReal ≤ δ := by
  have := Fintype.ofFinite Z
  have hR := rademacherComplexity_linearPredictors_le (D.map Prod.fst) φ hB hφ m
  refine le_trans (Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (rademacherComplexity_margin_bound D hm (H := linearPredictors φ B)
      (fun h hh z => abs_le_of_mem_linearPredictors hφ hh z) hρ hδ)
  rintro S ⟨w, hw, hlt⟩
  refine ⟨fun z => ⟪w, φ z⟫, mem_linearPredictors.2 ⟨w, hw, rfl⟩, ?_⟩
  have hmul : 2 / ρ * rademacherComplexity (D.map Prod.fst) (linearPredictors φ B) m ≤
      2 * B * R / (ρ * √m) := by
    calc 2 / ρ * rademacherComplexity (D.map Prod.fst) (linearPredictors φ B) m
        ≤ 2 / ρ * (B * R / √m) := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = 2 * B * R / (ρ * √m) := by ring
  exact lt_of_le_of_lt (by linarith) hlt

/-- **Data-dependent margin bound for linear classifiers**: on a finite domain, for `B ≥ 0`,
margin `ρ > 0` and `m > 0` independent draws from `D : PMF (Z × Bool)`, with probability at least
`1 - δ` every weight vector with `‖w‖ ≤ B` satisfies
`Pr_D[signVal y * ⟪w, φ x⟫ ≤ 0] ≤ R̂_{S, ρ}(w) + 2 B √(∑ i, ‖φ (S i).1‖²) / (ρ m)
  + 3 √(log (2 / δ) / (2 m))`.
This combines the trace form of [MohriRostamizadehTalwalkar2018, Theorem 5.10] with (5.40) of
their Theorem 5.8; no bound `R` on the features is assumed. -/
theorem linearPredictors_empirical_margin_bound [Finite Z] (D : PMF (Z × Bool)) {m : ℕ}
    (hm : 0 < m) (φ : Z → E) {B : ℝ} (hB : 0 ≤ B) {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ w : E, ‖w‖ ≤ B ∧ empiricalMarginLoss ρ (fun z => ⟪w, φ z⟫) S +
        2 * B * √(∑ i, ‖φ (S i).1‖ ^ 2) / (ρ * m) + 3 * √(Real.log (2 / δ) / (2 * m)) <
          (D.toOuterMeasure {p | signVal p.2 * ⟪w, φ p.1⟫ ≤ 0}).toReal}).toReal ≤ δ := by
  obtain ⟨R, hR⟩ := (Set.finite_range fun z => ‖φ z‖).bddAbove
  have hφ : ∀ z, ‖φ z‖ ≤ R := fun z => hR ⟨z, rfl⟩
  refine le_trans (Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (empiricalRademacherComplexity_margin_bound D hm (H := linearPredictors φ B)
      (fun h hh z => abs_le_of_mem_linearPredictors hφ hh z) hρ hδ)
  rintro S ⟨w, hw, hlt⟩
  refine ⟨fun z => ⟪w, φ z⟫, mem_linearPredictors.2 ⟨w, hw, rfl⟩, ?_⟩
  have hmul : 2 / ρ * empiricalRademacherComplexity (linearPredictors φ B) (fun i => (S i).1) ≤
      2 * B * √(∑ i, ‖φ (S i).1‖ ^ 2) / (ρ * m) := by
    calc 2 / ρ * empiricalRademacherComplexity (linearPredictors φ B) (fun i => (S i).1)
        ≤ 2 / ρ * (B * √(∑ i, ‖φ (S i).1‖ ^ 2) / m) :=
          mul_le_mul_of_nonneg_left
            (empiricalRademacherComplexity_linearPredictors_le_sqrt φ hB _) (by positivity)
      _ = 2 * B * √(∑ i, ‖φ (S i).1‖ ^ 2) / (ρ * m) := by ring
  exact lt_of_le_of_lt (by linarith) hlt

end Cslib.MachineLearning
