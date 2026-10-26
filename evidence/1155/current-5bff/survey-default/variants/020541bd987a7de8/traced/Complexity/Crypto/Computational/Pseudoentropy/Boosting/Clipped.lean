/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.UniformNat
public import Complexity.Foundations.Data.BitString.List.Vote
import Complexity.Probability.PMF.Event
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PPT
import Complexity.Probability.Quantile
import Complexity.Probability.PMF.Expect
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Floor.Semiring


import Diag1155.Measure
/-!
# Clipped randomized prediction from votes

The predictor returns true with probability `clippedProbability slope (listVoteMargin votes true)`.
Its implementation uses a natural numerator and an exact dyadic coin. The label is needed only
by the correctness statement, not by the predictor.

The lower-tail argument turns a positive margin on every dense soft set into a prediction
advantage. Its cutoff is only an analysis witness. Approximating its reciprocal by a finite
grid gives an efficiently representable candidate; empirical selection is a separate program.

## Main definitions

* `clippedProbability`, `clippedError`: the clipped affine law and its average error.
* `clippedPredict`: exact fair-bit prediction from a public vote list.

## Main results

* `eval_clippedPredict_correct`, `isPPTOn_clippedPredict`: semantics and strict PPT certificate.
* `exists_dyadic_clippedError_le`: a finite slope grid contains a good dense-margin predictor.

## References

[Holenstein2005], Lemma 2.4 and Claim 2.15. Fractional lower tails handle arbitrary finite
sources, and a finite slope grid permits exact fair-bit sampling.
Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/


diag1155_install
@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open ProbComp Probability BitString Turing.MultiTapeTM

/-- The clipped affine probability associated with a signed margin. -/
noncomputable def clippedProbability (slope margin : ℝ) : ℝ :=
  min 1 (max 0 ((1 + slope * margin) / 2))

/-- Clipping always gives a probability, including for arbitrary parameter values. -/
theorem clippedProbability_mem_Icc (slope margin : ℝ) :
    clippedProbability slope margin ∈ Set.Icc 0 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- A margin at the positive clipping threshold is predicted with certainty. -/
theorem clippedProbability_eq_one {slope margin : ℝ} (h : 1 ≤ slope * margin) :
    clippedProbability slope margin = 1 := by
  unfold clippedProbability
  exact min_eq_left ((by linarith : 1 ≤ (1 + slope * margin) / 2).trans (le_max_right _ _))

/-- Below the positive threshold, clipping can only increase the affine probability. -/
theorem le_clippedProbability {slope margin : ℝ} (h : slope * margin ≤ 1) :
    (1 + slope * margin) / 2 ≤ clippedProbability slope margin :=
  le_min (by linarith) (le_max_right _ _)

/-- A margin at the negative clipping threshold is predicted incorrectly with certainty. -/
theorem clippedProbability_eq_zero {slope margin : ℝ} (h : slope * margin ≤ -1) :
    clippedProbability slope margin = 0 := by
  simp [clippedProbability, max_eq_left (by linarith : (1 + slope * margin) / 2 ≤ 0)]

/-- Negating the signed margin complements the probability. -/
@[simp] theorem clippedProbability_neg (slope margin : ℝ) :
    clippedProbability slope (-margin) = 1 - clippedProbability slope margin := by
  by_cases hlo : slope * margin ≤ -1
  · rw [clippedProbability_eq_zero hlo, clippedProbability_eq_one (by nlinarith)]
    norm_num
  · by_cases hhi : 1 ≤ slope * margin
    · rw [clippedProbability_eq_one hhi, clippedProbability_eq_zero (by nlinarith)]
      norm_num
    · have hpos : (1 + slope * margin) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith
      have hneg : (1 + slope * -margin) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> nlinarith
      simp only [clippedProbability, max_eq_right hpos.1, max_eq_right hneg.1,
        min_eq_right hpos.2, min_eq_right hneg.2]
      ring

/-- Rounding the slope loses at most half the margin times the rounding error. -/
theorem clippedProbability_lipschitz (slope slope' margin : ℝ) :
    |clippedProbability slope margin - clippedProbability slope' margin| ≤
      |slope - slope'| * |margin| / 2 := by
  have hmin := abs_min_sub_min_le_max (1 : ℝ) (max 0 ((1 + slope * margin) / 2))
    1 (max 0 ((1 + slope' * margin) / 2))
  have hmax := abs_max_sub_max_le_max (0 : ℝ) ((1 + slope * margin) / 2)
    0 ((1 + slope' * margin) / 2)
  have hmaxabs (x : ℝ) : max 0 |x| = |x| := max_eq_right (abs_nonneg x)
  simp only [sub_self, abs_zero, hmaxabs] at hmin hmax
  calc
    _ ≤ |(1 + slope * margin) / 2 - (1 + slope' * margin) / 2| := hmin.trans hmax
    _ = _ := by
      rw [show (1 + slope * margin) / 2 - (1 + slope' * margin) / 2 =
        (slope - slope') * margin / 2 by ring, abs_div, abs_mul]
      norm_num

/-- Predict from the observable vote word with slope `numerator / dyadicSize bound`.
The larger dyadic range supplies the additional fair bit needed for the factor `1 / 2`. -/
noncomputable def clippedPredict (bound numerator : ℕ) (votes : List Bool) : ProbComp Bool :=
  sampleDyadicCoin (dyadicSize bound)
    (dyadicSize bound + numerator * (2 * votes.count true) - numerator * votes.length)

/-- The executable predictor realizes the clipped affine probability exactly. -/
theorem eval_clippedPredict_true (bound numerator : ℕ) (votes : List Bool) :
    (ProbComp.eval (clippedPredict bound numerator votes) true).toReal =
      clippedProbability (numerator / dyadicSize bound) (listVoteMargin votes true) := by
  have hd : (0 : ℝ) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  have hcast (a b : ℕ) : ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - b) := by
    by_cases h : b ≤ a
    · rw [Nat.cast_sub h, max_eq_right (sub_nonneg.mpr (by exact_mod_cast h))]
    · rw [Nat.sub_eq_zero_of_le (by lia), Nat.cast_zero,
        max_eq_left (sub_nonpos.mpr (by exact_mod_cast (show a ≤ b by lia)))]
  rw [clippedPredict, eval_sampleDyadicCoin_true_toReal, dyadicSize_dyadicSize,
    Nat.cast_min, hcast]
  push_cast
  rw [← min_div_div_right (by positivity), ← max_div_div_right (by positivity),
    div_self (by positivity : 2 * (dyadicSize bound : ℝ) ≠ 0), zero_div]
  unfold clippedProbability listVoteMargin
  congr 2
  field_simp
  ring

/-- Correctness is expressed using the signed margin for either label; the label is not an input. -/
theorem eval_clippedPredict_correct (bound numerator : ℕ) (votes : List Bool) (truth : Bool) :
    (ProbComp.eval (clippedPredict bound numerator votes) truth).toReal =
      clippedProbability (numerator / dyadicSize bound) (listVoteMargin votes truth) := by
  cases truth
  · rw [Cslib.Probability.PMF.toReal_false_eq_one_sub, eval_clippedPredict_true,
      show false = !true from rfl, listVoteMargin_not, clippedProbability_neg]
  · exact eval_clippedPredict_true bound numerator votes

/-- The opposite label has the complementary clipped probability. -/
theorem eval_clippedPredict_wrong (bound numerator : ℕ) (votes : List Bool) (truth : Bool) :
    (ProbComp.eval (clippedPredict bound numerator votes) (!truth)).toReal =
      1 - clippedProbability (numerator / dyadicSize bound) (listVoteMargin votes truth) := by
  rw [eval_clippedPredict_correct, listVoteMargin_not, clippedProbability_neg]

/-- Efficient parameters and votes give a strict PPT predictor through ordinary combinators. -/
theorem isPPTOn_clippedPredict {α : Type} {input : α ↪ List Bool}
    {bound numerator : α → ℕ} {votes : α → List Bool}
    (hbound : ComputableInPolyTime bound input encUnary)
    (hnumerator : ComputableInPolyTime numerator input encUnary)
    (hvotes : ComputableInPolyTime votes input encBits) :
    IsPPTOn input encBool (fun a => clippedPredict (bound a) (numerator a) (votes a)) := by
  unfold clippedPredict
  apply isPPTOn_sampleDyadicCoin
  · exact ComputableInPolyTime.unary_dyadicSize.comp hbound
  · exact (show ComputableInPolyTime
      (fun a => dyadicSize (bound a) + numerator a * (2 * (votes a).count true) -
        numerator a * (votes a).length) input encUnary by fun_prop)

attribute [program_certificate] isPPTOn_clippedPredict

section Error

variable {α : Type*} [Fintype α]

/-- The average error of clipped prediction on a finite source with signed margins. -/
noncomputable def clippedError (source : PMF α) (margin : α → ℝ) (slope : ℝ) : ℝ :=
  ∑ x, (source x).toReal * (1 - clippedProbability slope (margin x))

/-- The abstract error is exactly the source-averaged error of the executable dyadic predictor. -/
theorem clippedError_eq_error (source : PMF α) (votes : α → List Bool) (truth : α → Bool)
    (bound numerator : ℕ) :
    clippedError source (fun x => listVoteMargin (votes x) (truth x))
        (numerator / dyadicSize bound) =
      ∑ x, (source x).toReal * (ProbComp.eval (clippedPredict bound numerator (votes x))
        (!truth x)).toReal := by
  simp only [clippedError, eval_clippedPredict_wrong]

/-- A uniform bound on the margins controls the error caused by rounding the slope. -/
theorem clippedError_perturbation (source : PMF α) (margin : α → ℝ) {bound : ℝ}
    (hmargin : ∀ x, |margin x| ≤ bound) (slope slope' : ℝ) :
    clippedError source margin slope ≤
      clippedError source margin slope' + |slope - slope'| * bound / 2 := by
  have hpoint (x : α) : 1 - clippedProbability slope (margin x) ≤
      1 - clippedProbability slope' (margin x) + |slope - slope'| * bound / 2 := by
    have h := (abs_le.mp (clippedProbability_lipschitz slope slope' (margin x))).1
    have hb := mul_le_mul_of_nonneg_left (hmargin x) (abs_nonneg (slope - slope'))
    linarith
  simpa only [clippedError, one_mul, add_comm] using
    PMF.sum_le_affine source (a := |slope - slope'| * bound / 2) (b := 1)
      (fun x => by simpa only [one_mul, add_comm] using hpoint x)

/-- Positive average margin on every dense soft set gives a clipped predictor beating `δ / 2`.
The cutoff is an analysis witness; this theorem does not supply it as computational advice. -/
theorem exists_clippedError_le (source : PMF α) (margin : α → ℝ) {δ gap bound : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hgap : 0 < gap) (hmargin : ∀ x, margin x ≤ bound)
    (hdense : ∀ softSet : α → ℝ, (∀ x, softSet x ∈ Set.Icc 0 1) →
      δ ≤ (∑ x, (source x).toReal * softSet x) →
      (∑ x, (source x).toReal * softSet x) * gap ≤
        ∑ x, (source x).toReal * (softSet x * margin x)) :
    ∃ cutoff, gap ≤ cutoff ∧ cutoff ≤ bound ∧
      clippedError source margin (1 / cutoff) ≤ δ / 2 - δ * gap / (2 * bound) := by
  obtain ⟨cutoff, ⟨x, hx⟩, softSet, hsoftSet, hbelow, habove, hmass⟩ :=
    Cslib.Probability.PMF.exists_lowerTail source margin hδ.le hδone
  have hcutoff_bound : cutoff ≤ bound := hx ▸ hmargin x
  have hcorrelation := hdense softSet hsoftSet (by rw [hmass])
  rw [hmass] at hcorrelation
  have hupper : (∑ x, (source x).toReal * (softSet x * margin x)) ≤ δ * cutoff := by
    calc
      _ ≤ ∑ x, (source x).toReal * (softSet x * cutoff) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        by_cases h : margin x ≤ cutoff
        · exact mul_le_mul_of_nonneg_left h (hsoftSet x).1
        · simp [habove x (lt_of_not_ge h)]
      _ = δ * cutoff := by simp only [← mul_assoc, ← Finset.sum_mul, hmass]
  have hgap_cutoff : gap ≤ cutoff := by nlinarith
  have hcutoff : 0 < cutoff := hgap.trans_le hgap_cutoff
  have hpoint (x : α) : 1 - clippedProbability (1 / cutoff) (margin x) ≤
      softSet x * (1 - (1 / cutoff) * margin x) / 2 := by
    rcases lt_trichotomy (margin x) cutoff with hlt | heq | hgt
    · rw [hbelow x hlt]
      have hratio : (1 / cutoff) * margin x ≤ 1 := by
        rw [one_div_mul_eq_div]
        exact (div_le_one hcutoff).mpr hlt.le
      linarith [le_clippedProbability hratio]
    · have hratio : (1 / cutoff) * margin x = 1 := by rw [heq, one_div_mul_cancel hcutoff.ne']
      rw [clippedProbability_eq_one (le_of_eq hratio.symm), hratio]
      simp
    · have hratio : 1 ≤ (1 / cutoff) * margin x := by
        rw [one_div_mul_eq_div]
        exact (one_le_div hcutoff).mpr hgt.le
      rw [clippedProbability_eq_one hratio, habove x hgt]
      simp
  refine ⟨cutoff, hgap_cutoff, hcutoff_bound, ?_⟩
  calc
    clippedError source margin (1 / cutoff) ≤
        ∑ x, (source x).toReal * (softSet x * (1 - (1 / cutoff) * margin x) / 2) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) ENNReal.toReal_nonneg)
    _ = δ / 2 - (1 / cutoff) / 2 * ∑ x, (source x).toReal * (softSet x * margin x) := by
      rw [← hmass, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ δ / 2 - (1 / cutoff) / 2 * (δ * gap) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hcorrelation (by positivity)) _
    _ = δ / 2 - δ * gap / (2 * cutoff) := by ring
    _ ≤ δ / 2 - δ * gap / (2 * bound) := by
      apply sub_le_sub_left
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

private theorem exists_gridSlope (denominator : ℕ) (hd : 0 < denominator)
    {slope : ℝ} (hslope : slope ∈ Set.Icc 0 1) :
    ∃ numerator ≤ denominator, |(numerator : ℝ) / denominator - slope| ≤ 1 / denominator := by
  have hdreal : (0 : ℝ) < denominator := by exact_mod_cast hd
  have hnonneg : 0 ≤ (denominator : ℝ) * slope := mul_nonneg hdreal.le hslope.1
  refine ⟨⌊(denominator : ℝ) * slope⌋₊, Nat.floor_le_of_le ?_, ?_⟩
  · nlinarith [hslope.2]
  · rw [show (⌊(denominator : ℝ) * slope⌋₊ : ℝ) / denominator - slope =
        ((⌊(denominator : ℝ) * slope⌋₊ : ℝ) - denominator * slope) / denominator by field_simp,
      abs_div, abs_of_pos hdreal]
    exact div_le_div_of_nonneg_right (by
      simpa only [abs_sub_comm] using Nat.abs_sub_floor_le hnonneg) hdreal.le

/-- A finite dyadic grid contains a predictor with the lower-tail bound, up to explicit rounding
loss. This is an existence guarantee for subsequent empirical selection, not a choice of advice. -/
theorem exists_dyadic_clippedError_le (source : PMF α) (margin : α → ℝ)
    (precision : ℕ) {δ gap bound : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hgap : 1 ≤ gap)
    (hmargin : ∀ x, |margin x| ≤ bound)
    (hdense : ∀ softSet : α → ℝ, (∀ x, softSet x ∈ Set.Icc 0 1) →
      δ ≤ (∑ x, (source x).toReal * softSet x) →
      (∑ x, (source x).toReal * softSet x) * gap ≤
        ∑ x, (source x).toReal * (softSet x * margin x)) :
    ∃ numerator ≤ dyadicSize precision,
      clippedError source margin (numerator / dyadicSize precision) ≤
        δ / 2 - δ * gap / (2 * bound) + bound / (2 * dyadicSize precision) := by
  obtain ⟨cutoff, hgap_cutoff, hcutoff_bound, herror⟩ := exists_clippedError_le source margin
    hδ hδone (by linarith) (fun x => (le_abs_self _).trans (hmargin x)) hdense
  have hcutoff : 0 < cutoff := by linarith
  have hbound : 0 ≤ bound := by linarith
  obtain ⟨numerator, hnum, hclose⟩ := exists_gridSlope (dyadicSize precision)
    (dyadicSize_pos precision) (slope := 1 / cutoff)
    ⟨by positivity, (div_le_one hcutoff).mpr (by linarith)⟩
  refine ⟨numerator, hnum, ?_⟩
  have hperturb := clippedError_perturbation source margin hmargin
    (numerator / dyadicSize precision) (1 / cutoff)
  have hround := mul_le_mul_of_nonneg_right hclose hbound
  have heq : (1 / (dyadicSize precision : ℝ)) * bound / 2 =
      bound / (2 * dyadicSize precision) := by ring
  linarith

end Error

end Cslib.Crypto.Pseudoentropy.Boosting
