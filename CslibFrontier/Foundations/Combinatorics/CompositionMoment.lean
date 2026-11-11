/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, factorial moments of weak compositions)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Factorial moments of weak compositions

A weak composition of `t` into a nonempty finite set `S` of parts is a function `M` supported
in `S` with sum `t`. There are `multichoose r t` of them, where `r` is the number of parts. For
exponents `d` with sum `H` over `S`, the sum over all weak compositions of the product of
falling factorials `∏ i ∈ S, (M i).descFactorial (d i)` is
`(∏ i ∈ S, (d i)!) * choose (t + r - 1) (H + r - 1)`. This is the coefficient of `X ^ t` in
`∏ i ∈ S, X ^ d i / (1 - X) ^ (d i + 1)`.

Dividing by the number of compositions gives the factorial moment of a uniform weak composition,
`(∏ i, (d i)!) * ∏ j < H, (t - j) / (r + j)`. The corresponding moment of independent geometric
variables of mean `t / r` is `∏ i, (d i)! * (t / r) ^ d i`. The first is at most the second, and
at least `exp (-(H ^ 2 / t) - H ^ 2 / (2 * r))` times the second when `2 * H ≤ t`. These are the
two comparisons of the occupation-moment lemma of [OpenAI, §4][OpenAI2026DepthFive], stated for
one product of falling factorials and without probability theory.

## Main results

* `Finset.sum_finsuppAntidiag_prod_choose`: the sum of `∏ i ∈ S, (M i).choose (d i)`.
* `Finset.sum_finsuppAntidiag_prod_descFactorial`: the sum of
  `∏ i ∈ S, (M i).descFactorial (d i)`.
* `Finset.sum_finsuppAntidiag_prod_descFactorial_le`: the upper comparison.
* `Finset.le_sum_finsuppAntidiag_prod_descFactorial`: the lower comparison.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4, occupation-moment lemma (unrefereed preprint)
-/

public section

open PowerSeries Nat

namespace Finset

variable {ι : Type*} [DecidableEq ι] {S : Finset ι}

private theorem coeff_X_pow_mul_invOneSubPow (d j : ℕ) :
    coeff j (X ^ d * (invOneSubPow ℤ (d + 1)).val) = (j.choose d : ℤ) := by
  rw [coeff_X_pow_mul', invOneSubPow_val_succ_eq_mk_add_choose]
  split_ifs with h
  · rw [coeff_mk, Nat.add_sub_cancel' h]
  · rw [Nat.choose_eq_zero_of_lt (not_le.1 h), Nat.cast_zero]

/-- The sum over the weak compositions `M` of `t` of `∏ i ∈ S, (M i).choose (d i)`. -/
theorem sum_finsuppAntidiag_prod_choose (hS : S.Nonempty) (t : ℕ) (d : ι → ℕ) :
    ∑ M ∈ S.finsuppAntidiag t, ∏ i ∈ S, (M i).choose (d i) =
      (t + S.card - 1).choose (∑ i ∈ S, d i + S.card - 1) := by
  have hr := hS.card_pos
  have hprod : ∏ i ∈ S, (X ^ d i * (invOneSubPow ℤ (d i + 1)).val) =
      X ^ (∑ i ∈ S, d i) * (invOneSubPow ℤ (∑ i ∈ S, d i + S.card - 1 + 1)).val := by
    rw [prod_mul_distrib, prod_pow_eq_pow_sum, ← Units.coe_prod]
    congr 2
    simp_rw [invOneSubPow_eq_inv_one_sub_pow]
    rw [prod_pow_eq_pow_sum]
    congr 1
    rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
    omega
  have h := congrArg (coeff t) hprod
  rw [coeff_prod, coeff_X_pow_mul', invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk] at h
  simp_rw [coeff_X_pow_mul_invOneSubPow] at h
  rw [← Nat.cast_inj (R := ℤ)]
  simp only [Nat.cast_sum, Nat.cast_prod]
  rw [h]
  split_ifs with hH
  · congr 2
    omega
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- The sum over the weak compositions `M` of `t` of the product of falling factorials
`∏ i ∈ S, (M i).descFactorial (d i)`. It is zero when `∑ i ∈ S, d i > t`. -/
theorem sum_finsuppAntidiag_prod_descFactorial (hS : S.Nonempty) (t : ℕ) (d : ι → ℕ) :
    ∑ M ∈ S.finsuppAntidiag t, ∏ i ∈ S, (M i).descFactorial (d i) =
      (∏ i ∈ S, (d i)!) * (t + S.card - 1).choose (∑ i ∈ S, d i + S.card - 1) := by
  simp_rw [descFactorial_eq_factorial_mul_choose, prod_mul_distrib, ← mul_sum,
    sum_finsuppAntidiag_prod_choose hS]

private theorem choose_succ_mul {t r : ℕ} (hr : 0 < r) (H : ℕ) :
    (t + r - 1).choose (H + 1 + r - 1) * (r + H) = (t + r - 1).choose (H + r - 1) * (t - H) := by
  have h := Nat.choose_succ_right_eq (t + r - 1) (H + r - 1)
  have h₁ : H + 1 + r - 1 = H + r - 1 + 1 := by omega
  have h₂ : r + H = H + r - 1 + 1 := by omega
  have h₃ : t + r - 1 - (H + r - 1) = t - H := by omega
  rw [h₁, h₂, h, h₃]

private theorem choose_zero_eq {t r : ℕ} (hr : 0 < r) :
    (t + r - 1).choose (0 + r - 1) = r.multichoose t := by
  rw [multichoose_eq, zero_add, show r + t - 1 = t + r - 1 by omega]
  exact choose_symm_of_eq_add (by omega)

private theorem choose_le {t r : ℕ} (hr : 0 < r) (H : ℕ) :
    ((t + r - 1).choose (H + r - 1) : ℝ) ≤ r.multichoose t * ((t : ℝ) / r) ^ H := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  induction H with
  | zero => rw [choose_zero_eq hr, pow_zero, mul_one]
  | succ H ih =>
    have h : ((t + r - 1).choose (H + 1 + r - 1) : ℝ) * (r + H) =
        (t + r - 1).choose (H + r - 1) * (t - H : ℕ) := by exact_mod_cast choose_succ_mul hr H
    rw [eq_div_of_mul_eq (by positivity) h, pow_succ, ← mul_assoc]
    calc ((t + r - 1).choose (H + r - 1) : ℝ) * (t - H : ℕ) / (r + H)
        ≤ (t + r - 1).choose (H + r - 1) * t / r := by
          gcongr
          · exact_mod_cast Nat.sub_le t H
          · exact le_add_of_nonneg_right (Nat.cast_nonneg H)
      _ = (t + r - 1).choose (H + r - 1) * ((t : ℝ) / r) := by ring
      _ ≤ r.multichoose t * ((t : ℝ) / r) ^ H * ((t : ℝ) / r) := by gcongr

private theorem exp_step {t r H : ℝ} (ht : 0 < t) (hr : 0 < r) (hH : 0 ≤ H) (h : 2 * H ≤ t) :
    Real.exp (-((H + 1) ^ 2 / t) - (H + 1) ^ 2 / (2 * r)) * (t / r) ≤
      Real.exp (-(H ^ 2 / t) - H ^ 2 / (2 * r)) * ((t - H) / (r + H)) := by
  have hx : 0 ≤ H / t := by positivity
  have hx' : H / t ≤ 1 / 2 := by rw [div_le_iff₀ ht]; linarith
  have hy : 0 ≤ H / r := by positivity
  have h₁ : Real.exp (-(2 * (H / t))) ≤ 1 - H / t := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    nlinarith [Real.add_one_le_exp (2 * (H / t))]
  have h₂ : Real.exp (-(H / r)) ≤ (1 + H / r)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (H / r)])
  have h₃ : -((H + 1) ^ 2 / t) - (H + 1) ^ 2 / (2 * r) ≤
      (-(H ^ 2 / t) - H ^ 2 / (2 * r)) + (-(2 * (H / t)) + -(H / r)) := by
    have e₁ : (H + 1) ^ 2 / t = H ^ 2 / t + 2 * (H / t) + 1 / t := by field_simp; ring
    have e₂ : (H + 1) ^ 2 / (2 * r) = H ^ 2 / (2 * r) + H / r + 1 / (2 * r) := by
      field_simp; ring
    have : 0 < 1 / t := by positivity
    have : 0 < 1 / (2 * r) := by positivity
    linarith
  have h₄ : (t - H) / (r + H) = (1 - H / t) * (1 + H / r)⁻¹ * (t / r) := by
    field_simp
  calc Real.exp (-((H + 1) ^ 2 / t) - (H + 1) ^ 2 / (2 * r)) * (t / r)
      ≤ Real.exp ((-(H ^ 2 / t) - H ^ 2 / (2 * r)) + (-(2 * (H / t)) + -(H / r))) * (t / r) := by
        gcongr
    _ = Real.exp (-(H ^ 2 / t) - H ^ 2 / (2 * r)) *
          (Real.exp (-(2 * (H / t))) * Real.exp (-(H / r)) * (t / r)) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ Real.exp (-(H ^ 2 / t) - H ^ 2 / (2 * r)) *
          ((1 - H / t) * (1 + H / r)⁻¹ * (t / r)) := by
        have : 0 ≤ 1 - H / t := by linarith
        gcongr
    _ = _ := by rw [h₄]

private theorem le_choose {t r : ℕ} (hr : 0 < r) (H : ℕ) (hH : 2 * H ≤ t) :
    Real.exp (-((H : ℝ) ^ 2 / t) - (H : ℝ) ^ 2 / (2 * r)) *
      (r.multichoose t * ((t : ℝ) / r) ^ H) ≤ (t + r - 1).choose (H + r - 1) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  induction H with
  | zero => rw [choose_zero_eq hr]; simp
  | succ H ih =>
    have ht : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    have h : ((t + r - 1).choose (H + 1 + r - 1) : ℝ) * (r + H) =
        (t + r - 1).choose (H + r - 1) * (t - H : ℕ) := by exact_mod_cast choose_succ_mul hr H
    have hstep := exp_step ht hr' (Nat.cast_nonneg H)
      (by exact_mod_cast (by omega : 2 * H ≤ t))
    rw [eq_div_of_mul_eq (by positivity) h, Nat.cast_sub (by omega), Nat.cast_succ, pow_succ]
    calc Real.exp (-(((H : ℝ) + 1) ^ 2 / t) - ((H : ℝ) + 1) ^ 2 / (2 * r)) *
          (r.multichoose t * (((t : ℝ) / r) ^ H * ((t : ℝ) / r)))
        = r.multichoose t * ((t : ℝ) / r) ^ H *
            (Real.exp (-(((H : ℝ) + 1) ^ 2 / t) - ((H : ℝ) + 1) ^ 2 / (2 * r)) *
              ((t : ℝ) / r)) := by ring
      _ ≤ r.multichoose t * ((t : ℝ) / r) ^ H *
            (Real.exp (-((H : ℝ) ^ 2 / t) - (H : ℝ) ^ 2 / (2 * r)) *
              (((t : ℝ) - H) / (r + H))) := by gcongr
      _ = Real.exp (-((H : ℝ) ^ 2 / t) - (H : ℝ) ^ 2 / (2 * r)) *
            (r.multichoose t * ((t : ℝ) / r) ^ H) * (((t : ℝ) - H) / (r + H)) := by ring
      _ ≤ (t + r - 1).choose (H + r - 1) * (((t : ℝ) - H) / (r + H)) := by
          have : (0 : ℝ) ≤ (t : ℝ) - H := by
            have : (H : ℝ) ≤ t := by exact_mod_cast (by omega : H ≤ t)
            linarith
          gcongr
          exact ih (by omega)
      _ = _ := by ring

/-- **Upper comparison of factorial moments.** The sum over the weak compositions of `t` of a
product of falling factorials is at most the number of compositions times the corresponding
moment `∏ i ∈ S, (d i)! * (t / r) ^ d i` of independent geometric variables of mean `t / r`. -/
theorem sum_finsuppAntidiag_prod_descFactorial_le (hS : S.Nonempty) (t : ℕ) (d : ι → ℕ) :
    ((∑ M ∈ S.finsuppAntidiag t, ∏ i ∈ S, (M i).descFactorial (d i) : ℕ) : ℝ) ≤
      (S.card).multichoose t *
        ∏ i ∈ S, (((d i)! : ℝ) * ((t : ℝ) / S.card) ^ d i) := by
  rw [sum_finsuppAntidiag_prod_descFactorial hS, prod_mul_distrib, prod_pow_eq_pow_sum,
    Nat.cast_mul, Nat.cast_prod, mul_left_comm]
  gcongr
  exact choose_le hS.card_pos _

/-- **Lower comparison of factorial moments.** When the total order `H = ∑ i ∈ S, d i` is at
most `t / 2`, the sum over the weak compositions of `t` of a product of falling factorials is at
least `exp (-(H ^ 2 / t) - H ^ 2 / (2 * r))` times the bound of the upper comparison. -/
theorem le_sum_finsuppAntidiag_prod_descFactorial (hS : S.Nonempty) (t : ℕ) (d : ι → ℕ)
    (h : 2 * ∑ i ∈ S, d i ≤ t) :
    Real.exp (-(((∑ i ∈ S, d i : ℕ) : ℝ) ^ 2 / t) -
        ((∑ i ∈ S, d i : ℕ) : ℝ) ^ 2 / (2 * S.card)) *
      ((S.card).multichoose t *
        ∏ i ∈ S, (((d i)! : ℝ) * ((t : ℝ) / S.card) ^ d i)) ≤
      ((∑ M ∈ S.finsuppAntidiag t, ∏ i ∈ S, (M i).descFactorial (d i) : ℕ) : ℝ) := by
  rw [sum_finsuppAntidiag_prod_descFactorial hS, prod_mul_distrib, prod_pow_eq_pow_sum,
    Nat.cast_mul, Nat.cast_prod, mul_left_comm _ (∏ i ∈ S, ((d i)! : ℝ)),
    mul_left_comm _ (∏ i ∈ S, ((d i)! : ℝ))]
  gcongr
  exact le_choose hS.card_pos _ h

end Finset
