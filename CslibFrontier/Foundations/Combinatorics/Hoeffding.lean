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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Hoeffding's inequality for random bit strings

Fix real weights `a : ι → ℝ`. For all but a `2 exp (-2 t² / ∑ i, a i ^ 2)` fraction of the bit
strings `x : ι → Bool`, the centred weighted sum `∑ i, a i * (x i - 1 / 2)` has absolute value
less than `t` (`card_filter_le_abs_sum_mul_sub_half_le`). This is Hoeffding's inequality for a
weighted sum of independent unbiased bits, in counting form. With the weights `±1` on a finite set
`R` and `0` elsewhere, it bounds the binomial tail: for all but a `2 exp (-2 t² / |R|)` fraction of
the strings, the number of true coordinates of `x` in `R` is within `t` of `|R| / 2`
(`card_filter_le_abs_card_filter_sub_half_le`).

The proof is the exponential-moment argument with the probabilities multiplied out. The sum over
all strings of `exp (s ∑ i, a i (x i - 1 / 2))` factors over the coordinates, and equals
`2 ^ |ι| ∏ i, cosh (s a i / 2)` (`sum_exp_mul_sum_mul_sub_half`). As `cosh u ≤ exp (u² / 2)`,
Markov's inequality with `s = 4 t / ∑ i, a i ^ 2` bounds each tail.

## Main results

* `Cslib.BitString.sum_exp_mul_sum_mul_sub_half`: the weighted exponential moment.
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
-/

public section

namespace Cslib.BitString

open Finset Real

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

/-- **The weighted one-sided tail bound.** At most an `exp (-2 t² / ∑ i, a i ^ 2)` fraction of the
bit strings `x` have centred weighted sum `∑ i, a i * (x i - 1 / 2)` at least `t`. -/
theorem card_filter_le_sum_mul_sub_half_le (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | t ≤ ∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)} : ℝ) ≤
      2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / ∑ i, a i ^ 2)) := by
  set D : (ι → Bool) → ℝ := fun x => ∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)
  set σ : ℝ := ∑ i, a i ^ 2
  have hall : (#{x : ι → Bool | t ≤ D x} : ℝ) ≤ 2 ^ Fintype.card ι := by
    have := card_filter_le (univ : Finset (ι → Bool)) fun x => t ≤ D x
    rw [card_univ, Fintype.card_fun, Fintype.card_bool] at this
    exact_mod_cast this
  rcases (sum_nonneg fun i _ => sq_nonneg (a i) : 0 ≤ σ).eq_or_lt with hσ | hσ
  · rw [show σ = 0 from hσ.symm, div_zero, neg_zero, exp_zero, mul_one]
    exact hall
  -- Markov's inequality for `exp (s D)` with `s = 4 t / σ`.
  set s : ℝ := 4 * t / σ
  have hmarkov : (#{x : ι → Bool | t ≤ D x} : ℝ) * exp (s * t) ≤
      2 ^ Fintype.card ι * ∏ i, cosh (s * a i / 2) := by
    rw [← sum_exp_mul_sum_mul_sub_half a s, ← nsmul_eq_mul, ← sum_const]
    refine (sum_le_sum fun x hx => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => (exp_pos _).le)
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mem_filter.mp hx).2 (by positivity))
  have hcosh : ∏ i, cosh (s * a i / 2) ≤ exp (2 * t ^ 2 / σ) := by
    calc ∏ i, cosh (s * a i / 2) ≤ ∏ i, exp ((s * a i / 2) ^ 2 / 2) := by
          gcongr with i
          exact cosh_le_exp_half_sq _
      _ = exp (2 * t ^ 2 / σ) := by
          rw [← exp_sum]
          congr 1
          calc ∑ i, (s * a i / 2) ^ 2 / 2 = ∑ i, s ^ 2 / 8 * a i ^ 2 :=
                sum_congr rfl fun i _ => by ring
            _ = s ^ 2 / 8 * σ := (mul_sum _ _ _).symm
            _ = 2 * t ^ 2 / σ := by
                simp only [s]
                field_simp
                ring
  have hexp : exp (s * t) = exp (2 * t ^ 2 / σ) * exp (2 * t ^ 2 / σ) := by
    rw [← exp_add]
    congr 1
    simp only [s]
    field_simp
    ring
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  rw [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]
  have := hmarkov.trans (mul_le_mul_of_nonneg_left hcosh h2.le)
  rw [hexp] at this
  nlinarith [exp_pos (2 * t ^ 2 / σ)]

/-- **Hoeffding's inequality for weighted bit sums.** At most a `2 exp (-2 t² / ∑ i, a i ^ 2)`
fraction of the bit strings `x` have a centred weighted sum `∑ i, a i * (x i - 1 / 2)` of
absolute value at least `t`. -/
theorem card_filter_le_abs_sum_mul_sub_half_le (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | t ≤ |∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)|} : ℝ) ≤
      2 * 2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / ∑ i, a i ^ 2)) := by
  -- The upper tail of `-a` is the lower tail of `a`.
  have hneg := card_filter_le_sum_mul_sub_half_le (fun i => -a i) ht
  simp only [neg_mul, sum_neg_distrib, neg_sq] at hneg
  have hsub : ({x : ι → Bool | t ≤ |∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)|} : Finset _) ⊆
      ({x : ι → Bool | t ≤ ∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)} : Finset _) ∪
        ({x : ι → Bool | t ≤ -∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)} : Finset _) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    exact le_abs'.mp hx |>.symm.imp id fun h => by linarith
  calc (#{x : ι → Bool | t ≤ |∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)|} : ℝ)
      ≤ (#{x : ι → Bool | t ≤ ∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)} : ℝ) +
          #{x : ι → Bool | t ≤ -∑ i, a i * (((x i).toNat : ℝ) - 1 / 2)} := by
        exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ 2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / ∑ i, a i ^ 2)) +
          2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / ∑ i, a i ^ 2)) :=
        add_le_add (card_filter_le_sum_mul_sub_half_le a ht) hneg
    _ = 2 * 2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / ∑ i, a i ^ 2)) := by ring

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
