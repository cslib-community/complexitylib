/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Data.Fintype.Pi
public import CslibFrontier.Probability.BoundedDifferences
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Hoeffding's inequality for random bit strings

Fix real weights `a : ι → ℝ`. For all but a `2 exp (-2 t² / ∑ i, a i ^ 2)` fraction of the bit
strings `x : ι → Bool`, the centred weighted sum `∑ i, a i * (x i - 1 / 2)` has absolute value
less than `t` (`card_filter_le_abs_sum_mul_sub_half_le`). This is Hoeffding's inequality for a
weighted sum of independent unbiased bits, in counting form. With the weights `±1` on a finite set
`R` and `0` elsewhere, it bounds the binomial tail: for all but a `2 exp (-2 t² / |R|)` fraction of
the strings, the number of true coordinates of `x` in `R` is within `t` of `|R| / 2`
(`card_filter_le_abs_card_filter_sub_half_le`).

The tail bounds are McDiarmid's inequality (`Cslib.Probability.HasBoundedDifferences`) for the
sum of the coordinate scores `a i * (x i - 1 / 2)`, each varying by at most `|a i|` and of mean
`0` under independent uniform bits; the probability of an event under uniform bits is its
fraction of all strings. The exact exponential moment is recorded separately: the sum over all
strings of `exp (s ∑ i, a i (x i - 1 / 2))` factors over the coordinates, and equals
`2 ^ |ι| ∏ i, cosh (s a i / 2)` (`sum_exp_mul_sum_mul_sub_half`).

## Main results

* `Cslib.BitString.sum_exp_mul_sum_mul_sub_half`: the weighted exponential moment.
* `Cslib.BitString.card_filter_expect_add_le_le`: McDiarmid's inequality for functions of random bit
  strings with bounded differences, in counting form.
* `Cslib.BitString.card_filter_le_sum_mul_sub_half_le`: the weighted one-sided tail bound.
* `Cslib.BitString.card_filter_le_abs_sum_mul_sub_half_le`: Hoeffding's inequality for weighted
  bit sums.
* `Cslib.BitString.sum_exp_mul_card_filter_sub_half`: the exponential moment of a bit count.
* `Cslib.BitString.card_filter_le_card_filter_sub_half_le`: the one-sided tail bound for a bit
  count.
* `Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le`: Hoeffding's inequality for a bit
  count.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Theorem A.1.1][AlonSpencer2016]
* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
* [C. McDiarmid, *On the method of bounded differences*][McDiarmid1989], Lemma 1.2
-/

public section

namespace Cslib.BitString

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The weighted exponential moment.** Summed over all bit strings `x`, the exponential of `s`
times the centred weighted sum `∑ i, a i * (x i - 1 / 2)` is `2 ^ |ι| ∏ i, cosh (s a i / 2)`. -/
theorem sum_exp_mul_sum_mul_sub_half (a : ι → ℝ) (s : ℝ) :
    ∑ x : ι → Bool, exp (s * ∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)) =
      2 ^ Fintype.card ι * ∏ i, cosh (s * a i / 2) := by
  -- The term of a string is a product over the coordinates, and each coordinate contributes
  -- `2 cosh (s a i / 2)`.
  have hcoord (i : ι) :
      ∑ c : Bool, exp (s * (a i * ((c.toNat : ℝ) - 1 / 2))) = 2 * cosh (s * a i / 2) := by
    rw [Fintype.sum_bool, cosh_eq]
    simp only [Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero]
    ring_nf
  simp_rw [mul_sum, exp_sum]
  rw [← Fintype.prod_sum (fun i (c : Bool) => exp (s * (a i * ((c.toNat : ℝ) - 1 / 2)))),
    prod_congr rfl fun i _ => hcoord i, prod_mul_distrib, prod_const, card_univ]

/-- The fraction of bit strings in an event is its probability under independent uniform bits. -/
private theorem card_filter_eq_two_pow_mul_toOuterMeasure (P : (ι → Bool) → Prop)
    [DecidablePred P] :
    (#{x : ι → Bool | P x} : ℝ) = 2 ^ Fintype.card ι *
      ((Probability.PMF.pi fun _ : ι => Probability.PMF.uniformOfFintype Bool).toOuterMeasure
        {x | P x}).toReal := by
  rw [Probability.PMF.pi_uniformOfFintype,
    Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fun, Fintype.card_bool]
  have h : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  push_cast
  field_simp
  rfl

/-- **McDiarmid's inequality for random bit strings**, in counting form: if `f` has bounded
differences `c`, at most an `exp (-2 t² / ∑ i, c i ^ 2)` fraction of the bit strings `x` have
`f x ≥ 𝔼 y, f y + t`. This is `HasBoundedDifferences.pi_ge_mean_add` for independent uniform
bits. -/
theorem card_filter_expect_add_le_le {f : (ι → Bool) → ℝ} {c : ι → ℝ}
    (hf : Probability.HasBoundedDifferences (α := fun _ : ι => Bool) f c) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | (𝔼 y, f y) + t ≤ f x} : ℝ) ≤
      2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / ∑ i, c i ^ 2)) := by
  have h := hf.pi_ge_mean_add (fun _ => Probability.PMF.uniformOfFintype Bool) ht
  have hmean : ∑ y : ι → Bool,
      ((Probability.PMF.pi fun _ : ι => Probability.PMF.uniformOfFintype Bool) y).toReal * f y =
        𝔼 y, f y := by
    rw [Probability.PMF.pi_uniformOfFintype, Fintype.expect_eq_sum_div_card, sum_div]
    refine sum_congr rfl fun y _ => ?_
    rw [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring
  rw [hmean] at h
  simp only [neg_mul, neg_div] at h
  rw [card_filter_eq_two_pow_mul_toOuterMeasure]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The centred weighted bit sum has bounded differences `|a i|`. -/
private theorem hasBoundedDifferences_sum_mul_sub_half (a : ι → ℝ) :
    Probability.HasBoundedDifferences
      (fun x : ι → Bool => ∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)) fun i => |a i| :=
  Probability.hasBoundedDifferences_sum (α := fun _ => Bool)
    (score := fun i c => a i * ((c.toNat : ℝ) - 1 / 2)) (c := fun i => |a i|) fun i c d => by
    rw [← mul_sub, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    cases c <;> cases d <;> norm_num

/-- The centred weighted bit sum has mean `0` under independent uniform bits. -/
private theorem sum_pi_uniform_mul_sum_mul_sub_half (a : ι → ℝ) :
    ∑ y : ι → Bool,
      ((Probability.PMF.pi fun _ : ι => Probability.PMF.uniformOfFintype Bool) y).toReal *
        ∑ i, a i * (((y i).toNat : ℝ) - 1 / 2) = 0 := by
  rw [Probability.PMF.sum_pi_mul_sum (score := fun i (c : Bool) => a i * ((c.toNat : ℝ) - 1 / 2))]
  refine sum_eq_zero fun i _ => ?_
  simp only [Fintype.sum_bool, Probability.PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num

/-- **The weighted one-sided tail bound.** At most an `exp (-2 t² / ∑ i, a i ^ 2)` fraction of the
bit strings `x` have centred weighted sum `∑ i, a i * (x i - 1 / 2)` at least `t`. This is
McDiarmid's inequality `HasBoundedDifferences.pi_ge_mean_add` for independent uniform bits. -/
theorem card_filter_le_sum_mul_sub_half_le (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | t ≤ ∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)} : ℝ) ≤
      2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / ∑ i, a i ^ 2)) := by
  have h := (hasBoundedDifferences_sum_mul_sub_half a).pi_ge_mean_add
    (fun _ => Probability.PMF.uniformOfFintype Bool) ht
  rw [sum_pi_uniform_mul_sum_mul_sub_half, zero_add] at h
  simp only [sq_abs, neg_mul, neg_div] at h
  rw [card_filter_eq_two_pow_mul_toOuterMeasure]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **Hoeffding's inequality for weighted bit sums.** At most a `2 exp (-2 t² / ∑ i, a i ^ 2)`
fraction of the bit strings `x` have a centred weighted sum `∑ i, a i * (x i - 1 / 2)` of
absolute value at least `t`. This is `HasBoundedDifferences.pi_abs_sub_mean_ge`. -/
theorem card_filter_le_abs_sum_mul_sub_half_le (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | t ≤ |∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)|} : ℝ) ≤
      2 * 2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / ∑ i, a i ^ 2)) := by
  have h := (hasBoundedDifferences_sum_mul_sub_half a).pi_abs_sub_mean_ge
    (fun _ => Probability.PMF.uniformOfFintype Bool) ht
  rw [sum_pi_uniform_mul_sum_mul_sub_half] at h
  simp only [sub_zero, sq_abs, neg_mul, neg_div] at h
  rw [card_filter_eq_two_pow_mul_toOuterMeasure]
  nlinarith [exp_pos (-(2 * t ^ 2 / ∑ i, a i ^ 2)), (by positivity : (0 : ℝ) < 2 ^ Fintype.card ι)]

/-- The signed indicator weights of `R`: `1` (if `c = true`) or `-1` (if `c = false`) on `R`, and
`0` elsewhere. -/
private def signedIndicator (R : Finset ι) (c : Bool) (i : ι) : ℝ :=
  if i ∈ R then (if c then 1 else -1) else 0

/-- The signed indicator weights turn the centred weighted sum into the deviation of
`#{i ∈ R | x i = c}` from `|R| / 2`. -/
private theorem card_filter_sub_half_eq_sum (R : Finset ι) (c : Bool) (x : ι → Bool) :
    (#{i ∈ R | x i = c} : ℝ) - #R / 2 =
      ∑ i, signedIndicator R c i * (((x i).toNat : ℝ) - 1 / 2) := by
  simp only [signedIndicator, ite_mul, zero_mul, sum_ite_mem, univ_inter, card_filter, Nat.cast_sum]
  rw [div_eq_mul_inv, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  cases c <;> cases x i <;> norm_num

private theorem sum_sq_signed_indicator (R : Finset ι) (c : Bool) :
    ∑ i, signedIndicator R c i ^ 2 = #R := by
  cases c <;> simp [signedIndicator, ite_pow]

/-- **The exponential moment.** Summed over all bit strings `x`, the exponential of `s` times the
deviation of `#{i ∈ R | x i = c}` from `|R| / 2` is `2 ^ |ι| cosh (s / 2) ^ |R|`. -/
theorem sum_exp_mul_card_filter_sub_half (R : Finset ι) (c : Bool) (s : ℝ) :
    ∑ x : ι → Bool, exp (s * ((#{i ∈ R | x i = c} : ℝ) - #R / 2)) =
      2 ^ Fintype.card ι * cosh (s / 2) ^ #R := by
  have hcosh (i : ι) : cosh (s * signedIndicator R c i / 2) =
      if i ∈ R then cosh (s / 2) else 1 := by
    unfold signedIndicator
    split_ifs <;> simp [neg_div]
  simp_rw [card_filter_sub_half_eq_sum R c]
  rw [sum_exp_mul_sum_mul_sub_half, prod_congr rfl fun i _ => hcosh i, prod_ite_mem, univ_inter,
    prod_const]

/-- **The one-sided tail bound.** At most an `exp (-2 t² / |R|)` fraction of the bit strings `x`
have at least `|R| / 2 + t` coordinates in `R` equal to `c`. -/
theorem card_filter_le_card_filter_sub_half_le (R : Finset ι) (c : Bool) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | t ≤ (#{i ∈ R | x i = c} : ℝ) - #R / 2} : ℝ) ≤
      2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / #R)) := by
  simpa only [← card_filter_sub_half_eq_sum R c, sum_sq_signed_indicator R c] using
    card_filter_le_sum_mul_sub_half_le (signedIndicator R c) ht

/-- **Hoeffding's inequality.** At most a `2 exp (-2 t² / |R|)` fraction of the bit strings `x`
have a number of true coordinates in `R` that differs from `|R| / 2` by at least `t`. -/
theorem card_filter_le_abs_card_filter_sub_half_le (R : Finset ι) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | t ≤ |(#{i ∈ R | x i = true} : ℝ) - #R / 2|} : ℝ) ≤
      2 * 2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / #R)) := by
  simpa only [← card_filter_sub_half_eq_sum R true, sum_sq_signed_indicator R true] using
    card_filter_le_abs_sum_mul_sub_half_le (signedIndicator R true) ht

end Cslib.BitString
