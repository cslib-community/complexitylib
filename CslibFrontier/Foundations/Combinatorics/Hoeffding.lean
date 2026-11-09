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

Fix a finite set `R` of coordinates. For all but a `2 exp (-2 t² / |R|)` fraction of the bit
strings `x : ι → Bool`, the number of true coordinates of `x` in `R` is within `t` of `|R| / 2`
(`card_filter_le_abs_card_filter_sub_half_le`). This is Hoeffding's inequality for a sum of
independent unbiased bits, a tail bound for the binomial distribution, in counting form.

The proof is the exponential-moment argument with the probabilities multiplied out. The sum over
all strings of `exp (s (#{i ∈ R | x i = c} - |R| / 2))` factors over the coordinates, and equals
`2 ^ |ι| cosh (s / 2) ^ |R|` (`sum_exp_mul_card_filter_sub_half`). As `cosh u ≤ exp (u² / 2)`,
Markov's inequality with `s = 4 t / |R|` bounds each tail.

## Main results

* `Cslib.BitString.sum_exp_mul_card_filter_sub_half`: the exponential moment.
* `Cslib.BitString.card_filter_le_card_filter_sub_half_le`: the one-sided tail bound.
* `Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le`: Hoeffding's inequality.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Theorem A.1.1][AlonSpencer2016]
* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The exponential moment.** Summed over all bit strings `x`, the exponential of `s` times the
deviation of `#{i ∈ R | x i = c}` from `|R| / 2` is `2 ^ |ι| cosh (s / 2) ^ |R|`. -/
theorem sum_exp_mul_card_filter_sub_half (R : Finset ι) (c : Bool) (s : ℝ) :
    ∑ x : ι → Bool, exp (s * ((#{i ∈ R | x i = c} : ℝ) - #R / 2)) =
      2 ^ Fintype.card ι * cosh (s / 2) ^ #R := by
  -- The term of a string is a product over the coordinates.
  set F : ι → Bool → ℝ := fun i b => if i ∈ R then exp (s * ((if b = c then 1 else 0) - 1 / 2))
    else 1
  have hterm (x : ι → Bool) :
      exp (s * ((#{i ∈ R | x i = c} : ℝ) - #R / 2)) = ∏ i, F i (x i) := by
    rw [Finset.prod_ite_mem, univ_inter, ← exp_sum, ← mul_sum, sum_sub_distrib, sum_boole,
      sum_const, nsmul_eq_mul]
    congr 2
    ring
  -- Each coordinate contributes `2 cosh (s / 2)` if it lies in `R`, and `2` otherwise.
  have hcosh : exp (s * (1 - 1 / 2)) + exp (s * (0 - 1 / 2)) = 2 * cosh (s / 2) := by
    rw [cosh_eq]
    ring_nf
  have hcoord (i : ι) : ∑ b, F i b = 2 * if i ∈ R then cosh (s / 2) else 1 := by
    by_cases hi : i ∈ R
    · cases c
      · simpa [F, hi, add_comm] using hcosh
      · simpa [F, hi] using hcosh
    · simp only [F, Fintype.sum_bool, hi, ite_false]
      norm_num
  simp_rw [hterm]
  rw [← Fintype.prod_sum, Finset.prod_congr rfl fun i _ => hcoord i, prod_mul_distrib, prod_const,
    card_univ, Finset.prod_ite_mem, univ_inter, prod_const]

/-- **The one-sided tail bound.** At most an `exp (-2 t² / |R|)` fraction of the bit strings `x`
have at least `|R| / 2 + t` coordinates in `R` equal to `c`. -/
theorem card_filter_le_card_filter_sub_half_le (R : Finset ι) (c : Bool) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | t ≤ (#{i ∈ R | x i = c} : ℝ) - #R / 2} : ℝ) ≤
      2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / #R)) := by
  set D : (ι → Bool) → ℝ := fun x => (#{i ∈ R | x i = c} : ℝ) - #R / 2
  have hall : (#{x : ι → Bool | t ≤ D x} : ℝ) ≤ 2 ^ Fintype.card ι := by
    have := card_filter_le (univ : Finset (ι → Bool)) fun x => t ≤ D x
    rw [card_univ, Fintype.card_fun, Fintype.card_bool] at this
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos #R with hR | hR
  · exact hall.trans_eq (by simp [hR])
  set m : ℝ := (#R : ℝ)
  have hm : 0 < m := Nat.cast_pos.mpr hR
  -- Markov's inequality for `exp (s D)` with `s = 4 t / m`.
  set s : ℝ := 4 * t / m
  have hmarkov : (#{x : ι → Bool | t ≤ D x} : ℝ) * exp (s * t) ≤
      2 ^ Fintype.card ι * cosh (s / 2) ^ #R := by
    rw [← sum_exp_mul_card_filter_sub_half R c s, ← nsmul_eq_mul, ← sum_const]
    refine (sum_le_sum fun x hx => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => (exp_pos _).le)
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mem_filter.mp hx).2 (by positivity))
  have hcosh : cosh (s / 2) ^ #R ≤ exp (2 * t ^ 2 / m) := by
    calc cosh (s / 2) ^ #R ≤ exp ((s / 2) ^ 2 / 2) ^ #R :=
          pow_le_pow_left₀ (cosh_pos _).le (cosh_le_exp_half_sq _) _
      _ = exp (2 * t ^ 2 / m) := by
          rw [← exp_nat_mul]
          congr 1
          simp only [s, m]
          field_simp
          ring
  have hexp : exp (s * t) = exp (2 * t ^ 2 / m) * exp (2 * t ^ 2 / m) := by
    rw [← exp_add]
    congr 1
    simp only [s]
    field_simp
    ring
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  rw [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)]
  have := hmarkov.trans (mul_le_mul_of_nonneg_left hcosh h2.le)
  rw [hexp] at this
  nlinarith [exp_pos (2 * t ^ 2 / m)]

/-- **Hoeffding's inequality.** At most a `2 exp (-2 t² / |R|)` fraction of the bit strings `x`
have a number of true coordinates in `R` that differs from `|R| / 2` by at least `t`. -/
theorem card_filter_le_abs_card_filter_sub_half_le (R : Finset ι) {t : ℝ} (ht : 0 ≤ t) :
    (#{x : ι → Bool | t ≤ |(#{i ∈ R | x i = true} : ℝ) - #R / 2|} : ℝ) ≤
      2 * 2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / #R)) := by
  -- The true and false coordinates in `R` deviate from `|R| / 2` by opposite amounts.
  have hsplit (x : ι → Bool) :
      (#{i ∈ R | x i = false} : ℝ) - #R / 2 = -((#{i ∈ R | x i = true} : ℝ) - #R / 2) := by
    have := card_filter_add_card_filter_not (s := R) fun i => x i = true
    simp only [Bool.not_eq_true] at this
    rw [← this]
    push_cast
    ring
  have hsub : ({x : ι → Bool | t ≤ |(#{i ∈ R | x i = true} : ℝ) - #R / 2|} : Finset _) ⊆
      ({x : ι → Bool | t ≤ (#{i ∈ R | x i = true} : ℝ) - #R / 2} : Finset _) ∪
        ({x : ι → Bool | t ≤ (#{i ∈ R | x i = false} : ℝ) - #R / 2} : Finset _) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    rw [hsplit]
    rcases le_abs'.mp hx with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl h
  calc (#{x : ι → Bool | t ≤ |(#{i ∈ R | x i = true} : ℝ) - #R / 2|} : ℝ)
      ≤ (#{x : ι → Bool | t ≤ (#{i ∈ R | x i = true} : ℝ) - #R / 2} : ℝ) +
          #{x : ι → Bool | t ≤ (#{i ∈ R | x i = false} : ℝ) - #R / 2} := by
        exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ 2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / #R)) +
          2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / #R)) :=
        add_le_add (card_filter_le_card_filter_sub_half_le R true ht)
          (card_filter_le_card_filter_sub_half_le R false ht)
    _ = 2 * 2 ^ Fintype.card ι * exp (-(2 * t ^ 2 / #R)) := by ring

end Cslib.BitString
