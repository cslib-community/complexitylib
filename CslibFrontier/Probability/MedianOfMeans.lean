/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finset.Median
public import CslibFrontier.Probability.MedianTrick
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.KWiseIndependent.SecondMoment
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The median-of-means estimator

Given an estimator `g : Ω → ℝ` of its mean `𝔼 g`, with sample `x` drawn uniformly from a finite
type `Ω`, the **median-of-means** estimator `Cslib.Probability.medianOfMeans g ω` draws `2 r`
groups of `k` independent samples `ω i l`, averages each group, and reports the median of the
`2 r` averages. An average of `k` samples has `k` times smaller variance
(`Cslib.Probability.expect_expect_sub_sq`), so by Chebyshev's inequality at most a third of the
groups miss `𝔼 g` by more than `t` once the variance of `g` is at most `k t² / 3`; the median
misses only when at least half of the groups do, which happens for at most an `(8 / 9) ^ r`
fraction of the samples (`Cslib.Probability.dens_abs_medianOfMeans_sub_gt_le`). This is the
amplification step of the frequency moment estimators of Alon, Matias and Szegedy
[AlonMatiasSzegedy1999, Theorem 2.2]. Probabilities over the samples are densities `Finset.dens`.

The last step is the **median trick** [Chakrabarti2025, Section 2.4]
(`Cslib.Probability.dens_abs_median_sub_gt_le`, in `CslibFrontier.Probability.MedianTrick`), which
holds for any estimate that misses by more than `t` with probability at most `1 / 3`, whatever its
distribution; the Count-Sketch uses it for estimates that are not averages.

## Main definitions

* `Cslib.Probability.medianOfMeans`: the median of `2 r` averages of `k` samples.

## Main results

* `Cslib.Probability.expect_expect_sub_sq`: the variance of an average of `k` independent samples.
* `Cslib.Probability.dens_abs_medianOfMeans_sub_gt_le`: the median of means misses the mean by
  more than `t` with probability at most `(8 / 9) ^ r`.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Theorem 2.2][AlonMatiasSzegedy1999]
* [A. Chakrabarti, *Data Stream Algorithms*, Section 2.4][Chakrabarti2025]
-/

public section

namespace Cslib.Probability

open Finset Fintype
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The **median-of-means** estimate from `2 r` groups of `k` samples of `g`: the median of the
`2 r` group averages. -/
@[expose] noncomputable def medianOfMeans {r k : ℕ} (g : Ω → ℝ) (ω : Fin (2 * r) → Fin k → Ω) : ℝ :=
  median fun i => 𝔼 l, g (ω i l)

/-- The average of `k` independent samples of `g` has `k` times smaller variance. -/
theorem expect_expect_sub_sq [Nonempty Ω] {k : ℕ} [NeZero k] (g : Ω → ℝ) :
    𝔼 ω : Fin k → Ω, (𝔼 l, g (ω l) - 𝔼 x, g x) ^ 2 = (𝔼 x, (g x - 𝔼 y, g y) ^ 2) / k := by
  classical
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne k)
  have key := (isKWiseIndependentHash_id (X := Fin k) (Y := Ω) 2).expect_sq_sum univ
    (fun _ y => (g y - 𝔼 x, g x) / k) fun l _ => by
      simp only [← expect_div, expect_sub_distrib, Fintype.expect_const, sub_self, zero_div]
  simp only [id] at key
  have hrw (ω : Fin k → Ω) : 𝔼 l, g (ω l) - 𝔼 x, g x = ∑ l, (g (ω l) - 𝔼 x, g x) / k := by
    rw [← sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Fintype.expect_eq_sum_div_card (fun l => g (ω l)), Fintype.card_fin]
    field_simp
  simp only [hrw, key, div_pow, ← expect_div, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Median of means** [AlonMatiasSzegedy1999, Theorem 2.2]: if `g` has variance at most
`k t² / 3`, the median of `2 r` averages of `k` independent samples of `g` is farther than `t` from
the mean of `g` for at most an `(8 / 9) ^ r` fraction of the samples. -/
theorem dens_abs_medianOfMeans_sub_gt_le [Nonempty Ω] {r k : ℕ} [NeZero k] (g : Ω → ℝ) {t : ℝ}
    (ht : 0 < t) (hvar : 3 * 𝔼 x, (g x - 𝔼 y, g y) ^ 2 ≤ k * t ^ 2) :
    (dens {ω : Fin (2 * r) → Fin k → Ω | t < |medianOfMeans g ω - 𝔼 x, g x|} : ℝ) ≤
      (8 / 9) ^ r := by
  classical
  set μ := 𝔼 x, g x
  have hk : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne k))
  -- Chebyshev: at most a third of the groups are bad.
  have hcheb : (dens {ω : Fin k → Ω | t ^ 2 ≤ (𝔼 l, g (ω l) - μ) ^ 2} : ℝ) * t ^ 2 ≤ t ^ 2 / 3 := by
    have := Fintype.mul_dens_filter_le_expect (f := fun ω : Fin k → Ω => (𝔼 l, g (ω l) - μ) ^ 2)
      (fun _ => sq_nonneg _) (t ^ 2)
    rw [expect_expect_sub_sq] at this
    calc _ = t ^ 2 * (dens {ω : Fin k → Ω | t ^ 2 ≤ (𝔼 l, g (ω l) - μ) ^ 2} : ℝ) := mul_comm _ _
      _ ≤ _ := this
      _ ≤ t ^ 2 / 3 := by
        rw [div_le_div_iff₀ hk (by norm_num)]
        linarith
  have hbad : (dens {ω : Fin k → Ω | t < |𝔼 l, g (ω l) - μ|} : ℝ) ≤ 1 / 3 := by
    have hsub : ({ω : Fin k → Ω | t < |𝔼 l, g (ω l) - μ|} : Finset _) ⊆
        ({ω : Fin k → Ω | t ^ 2 ≤ (𝔼 l, g (ω l) - μ) ^ 2} : Finset _) := fun ω hω => by
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      rw [← sq_abs (𝔼 l, g (ω l) - μ)]
      exact pow_le_pow_left₀ ht.le hω.le 2
    have h2 : (dens {ω : Fin k → Ω | t < |𝔼 l, g (ω l) - μ|} : ℝ) * t ^ 2 ≤ t ^ 2 / 3 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast dens_le_dens hsub) (sq_nonneg t)).trans hcheb
    have ht2 : 0 < t ^ 2 := by positivity
    rw [div_eq_mul_one_div (t ^ 2), mul_comm (t ^ 2)] at h2
    exact le_of_mul_le_mul_right h2 ht2
  exact dens_abs_median_sub_gt_le (fun ω : Fin k → Ω => 𝔼 l, g (ω l)) hbad r

end Cslib.Probability
