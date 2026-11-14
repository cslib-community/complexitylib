/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
public import Mathlib.Probability.Moments.Variance

/-!
# Majority from pairwise independence

Pairwise independent votes, each correct with probability at least `1 / 2 + ε`, fail to
have a strict majority with probability at most `1 / (4 * ε ^ 2 * m)`, where `m > 0`
is the number of votes. More generally the same bound holds for scores in `[0, 1]`
with these expectations. Ties are included in the failure event.

The proof uses Mathlib's variance bound for bounded random variables, additivity of variance
under pairwise independence, and Chebyshev's inequality. This is the concentration step in the
Goldreich–Levin subset-sum decoder. Adapted from the cslib `crypto` branch at `5ff69ca`.

## Main results

* `majority_error_bound`: pairwise-independent bounded scores concentrate above half.

## References

* [L. Trevisan, *CS276 Lecture 12: Goldreich–Levin*, Lemma 4][Trevisan2009GL]
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory

/-- Pairwise independent scores in `[0, 1]` with mean at least `1 / 2 + ε` have a
strict majority except with probability at most `1 / (4 * ε ^ 2 * m)`. -/
theorem majority_error_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι)
    (X : ι → Ω → ℝ) (ε : ℝ) (hε : 0 < ε) (hs : s.Nonempty)
    (hm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1)
    (hi : Set.Pairwise (↑s : Set ι) (fun i j => IndepFun (X i) (X j) μ))
    (he : ∀ i ∈ s, 1 / 2 + ε ≤ ∫ ω, X i ω ∂μ) :
    μ {ω | ∑ i ∈ s, X i ω ≤ (s.card : ℝ) / 2} ≤
      ENNReal.ofReal (1 / (4 * ε ^ 2 * s.card)) := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hmem (i) (hi : i ∈ s) : MemLp (X i) 2 μ :=
    memLp_of_bounded (hb i hi) (hm i hi).aestronglyMeasurable 2
  let total : Ω → ℝ := ∑ i ∈ s, X i
  have htotal : MemLp total 2 μ := memLp_finsetSum' _ (fun i hi => hmem i hi)
  have hmean : (s.card : ℝ) * (1 / 2 + ε) ≤ ∫ ω, total ω ∂μ := by
    simp only [total, Finset.sum_apply]
    rw [integral_finsetSum]
    · simpa [mul_add] using Finset.sum_le_sum he
    · exact fun i hi => (hmem i hi).integrable (by norm_num)
  have hvar : variance total μ ≤ (s.card : ℝ) / 4 := by
    rw [show total = ∑ i ∈ s, X i from rfl, IndepFun.variance_sum hmem hi]
    calc
      _ ≤ ∑ _i ∈ s, (1 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        convert variance_le_sq_of_bounded (hb i hi) (hm i hi) using 1
        norm_num
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  calc
    μ {ω | ∑ i ∈ s, X i ω ≤ (s.card : ℝ) / 2} ≤
        μ {ω | ε * s.card ≤ |total ω - ∫ ω, total ω ∂μ|} := by
      apply measure_mono
      intro ω hω
      have hω' : total ω ≤ (s.card : ℝ) / 2 := by simpa [total] using hω
      have hneg : total ω - ∫ ω, total ω ∂μ ≤ 0 := by
        nlinarith [mul_pos hε hcard]
      change ε * s.card ≤ |total ω - ∫ ω, total ω ∂μ|
      rw [abs_of_nonpos hneg]
      nlinarith
    _ ≤ ENNReal.ofReal (variance total μ / (ε * s.card) ^ 2) :=
      meas_ge_le_variance_div_sq htotal (mul_pos hε hcard)
    _ ≤ ENNReal.ofReal (1 / (4 * ε ^ 2 * s.card)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((s.card : ℝ) / 4) / (ε * s.card) ^ 2 :=
          div_le_div_of_nonneg_right hvar (sq_nonneg _)
        _ = _ := by field_simp

end Cslib.Probability
