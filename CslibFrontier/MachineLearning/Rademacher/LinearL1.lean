/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Rademacher.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import CslibFrontier.Probability.BitString.Massart

/-!
# Rademacher complexity of ℓ₁-bounded linear predictors

For a feature map `φ : Z → Fin n → ℝ`, `l1LinearPredictors φ B` is the class of linear predictors
`z ↦ w ⬝ᵥ φ z` whose weight vector has ℓ₁ norm `∑ j, |w j| ≤ B`. If every coordinate of every
sample feature is at most `R` in absolute value, its empirical Rademacher complexity on `m` points
is at most `B R √(2 log (2 n) / m)` [ShalevShwartzBenDavid2014, Lemma 26.11].

The proof is the textbook one. For a fixed sign vector `σ`, Hölder's inequality bounds the
correlation of `w` with `σ` by `B maxⱼ |cⱼ|`, where `cⱼ` is the correlation of coordinate `j` of
the features with `σ`; this maximum is attained by one of the `2 n` vertices `± B eⱼ` of the
ℓ₁ ball. Massart's lemma (`rademacherAverage_le_mul_sqrt`) bounds the Rademacher average of these
`2 n` vectors, whose entries are at most `B R` in absolute value.

Compared with the ℓ₂ bound of `CslibFrontier.MachineLearning.Rademacher.Linear`, the ℓ₁
constraint on `w` is stronger and the ℓ∞ assumption on the features weaker, at the price of a
`√(log n)` factor. The population form assumes `Z` finite, as the Rademacher API does.

## Main definitions

* `Cslib.MachineLearning.l1LinearPredictors`: the predictors `z ↦ w ⬝ᵥ φ z` with
  `∑ j, |w j| ≤ B`.

## Main results

* `Cslib.MachineLearning.empiricalRademacherComplexity_l1LinearPredictors_le`: the bound
  `B R √(2 log (2 n) / m)` [ShalevShwartzBenDavid2014, Lemma 26.11].
* `Cslib.MachineLearning.rademacherComplexity_l1LinearPredictors_le`: the population form.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Section 26.2, Lemma 26.11
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.MachineLearning

open Cslib.BitString

variable {Z : Type*} {n : ℕ}

/-- The class of **ℓ₁-bounded linear predictors** `z ↦ w ⬝ᵥ φ z` with `∑ j, |w j| ≤ B`, for a
feature map `φ : Z → Fin n → ℝ`. -/
def l1LinearPredictors (φ : Z → Fin n → ℝ) (B : ℝ) : Set (Z → ℝ) :=
  (fun w : Fin n → ℝ => fun z => w ⬝ᵥ φ z) '' {w | ∑ j, |w j| ≤ B}

theorem mem_l1LinearPredictors {φ : Z → Fin n → ℝ} {B : ℝ} {h : Z → ℝ} :
    h ∈ l1LinearPredictors φ B ↔ ∃ w : Fin n → ℝ, ∑ j, |w j| ≤ B ∧ (fun z => w ⬝ᵥ φ z) = h := by
  rw [l1LinearPredictors, Set.mem_image]
  rfl

/-- **Rademacher complexity of ℓ₁-bounded linear predictors** [ShalevShwartzBenDavid2014,
Lemma 26.11]: for `B ≥ 0` and a sample whose features have coordinates at most `R` in absolute
value, the empirical Rademacher complexity of `l1LinearPredictors φ B` is at most
`B R √(2 log (2 n) / m)`. -/
theorem empiricalRademacherComplexity_l1LinearPredictors_le (φ : Z → Fin n → ℝ) {B R : ℝ}
    (hB : 0 ≤ B) {m : ℕ} (S : Fin m → Z) (hS : ∀ i j, |φ (S i) j| ≤ R) :
    empiricalRademacherComplexity (l1LinearPredictors φ B) S ≤
      B * R * √(2 * Real.log (2 * n) / m) := by
  classical
  -- The `2 n` vertices `± B eⱼ` of the ℓ₁ ball, restricted to the sample.
  obtain ⟨v, hv⟩ : ∃ v : Bool × Fin n → Fin m → ℝ,
      ∀ p i, v p i = B * (signVal p.1 * φ (S i) p.2) := ⟨_, fun _ _ => rfl⟩
  have hv_le : ∀ p i, |v p i| ≤ B * max R 0 := fun p i => by
    rw [hv, abs_mul, abs_mul, abs_signVal, one_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left ((hS i p.2).trans (le_max_left _ _)) hB
  have hmassart := rademacherAverage_le_mul_sqrt v (mul_nonneg hB (le_max_right _ _)) hv_le
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    at hmassart
  have hne : Nonempty (l1LinearPredictors φ B) :=
    ⟨⟨fun z => (0 : Fin n → ℝ) ⬝ᵥ φ z, mem_l1LinearPredictors.2 ⟨0, by simpa using hB, rfl⟩⟩⟩
  have hcmp : empiricalRademacherComplexity (l1LinearPredictors φ B) S ≤
      rademacherAverage v := by
    rw [empiricalRademacherComplexity_def, rademacherAverage_def, rademacherAverage_def]
    refine Finset.expect_le_expect fun σ _ => ciSup_le fun h => ?_
    obtain ⟨w, hw, hwh⟩ := mem_l1LinearPredictors.1 h.2
    obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, ∀ j, c j = 𝔼 i, signVal (σ i) * φ (S i) j :=
      ⟨_, fun _ => rfl⟩
    have hlin : 𝔼 i, signVal (σ i) * (h : Z → ℝ) (S i) = ∑ j, w j * c j := by
      rw [← hwh]
      simp only [hc, dotProduct, Finset.mul_sum, Finset.mul_expect]
      rw [Finset.expect_sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.expect_congr rfl fun i _ => by ring
    rw [hlin]
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · simp [Finset.univ_eq_empty]
    obtain ⟨j₀, -, hj₀⟩ :=
      Finset.exists_max_image Finset.univ (fun j => |c j|) Finset.univ_nonempty
    have hvert : 𝔼 i, signVal (σ i) * v (decide (c j₀ < 0), j₀) i = B * |c j₀| := by
      have hexp : 𝔼 i, signVal (σ i) * v (decide (c j₀ < 0), j₀) i =
          B * (signVal (decide (c j₀ < 0)) * c j₀) := by
        rw [hc, Finset.mul_expect, Finset.mul_expect]
        exact Finset.expect_congr rfl fun i _ => by rw [hv]; ring
      rw [hexp]
      by_cases hneg : c j₀ < 0
      · rw [decide_eq_true hneg, signVal_true, abs_of_neg hneg]
        ring
      · rw [decide_eq_false hneg, signVal_false, one_mul, abs_of_nonneg (not_lt.1 hneg)]
    calc ∑ j, w j * c j ≤ ∑ j, |w j| * |c j₀| := Finset.sum_le_sum fun j _ =>
          (le_abs_self _).trans (by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hj₀ j (Finset.mem_univ _)) (abs_nonneg _))
      _ = (∑ j, |w j|) * |c j₀| := by rw [Finset.sum_mul]
      _ ≤ B * |c j₀| := mul_le_mul_of_nonneg_right hw (abs_nonneg _)
      _ = 𝔼 i, signVal (σ i) * v (decide (c j₀ < 0), j₀) i := hvert.symm
      _ ≤ ⨆ p, 𝔼 i, signVal (σ i) * v p i :=
          le_ciSup (bddAbove_range_expect_signVal_mul v hv_le σ) _
  refine hcmp.trans (hmassart.trans_eq ?_)
  rcases lt_or_ge R 0 with hRneg | hR
  · -- A negative bound leaves no sample coordinates, so the square root vanishes.
    have h0 : m = 0 ∨ n = 0 := by
      by_contra hcon
      push Not at hcon
      exact absurd ((abs_nonneg _).trans (hS ⟨0, by omega⟩ ⟨0, by omega⟩)) (not_le.2 hRneg)
    rcases h0 with rfl | rfl <;> simp
  · rw [max_eq_left hR]

/-- The population form of `empiricalRademacherComplexity_l1LinearPredictors_le` on a finite
domain whose features have coordinates at most `R` in absolute value. -/
theorem rademacherComplexity_l1LinearPredictors_le [Fintype Z] (D : PMF Z)
    (φ : Z → Fin n → ℝ) {B R : ℝ} (hB : 0 ≤ B) (hφ : ∀ z j, |φ z j| ≤ R) (m : ℕ) :
    rademacherComplexity D (l1LinearPredictors φ B) m ≤ B * R * √(2 * Real.log (2 * n) / m) :=
  rademacherComplexity_le D fun S =>
    empiricalRademacherComplexity_l1LinearPredictors_le φ hB S fun i => hφ (S i)

end Cslib.MachineLearning
