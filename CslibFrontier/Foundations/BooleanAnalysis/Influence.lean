/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.Flip
public import Mathlib.Data.Finset.Density
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Influences on the Boolean cube

The *derivative* of a real function `f` on the cube in coordinate `i` is half the difference
between its values at bit `i` equal to `false` (sign `1`) and to `true` (sign `-1`)
(`BitString.derivative`); it is
O'Donnell's `Dᵢ f` when bits are read as the signs `BitString.signVal`. The *influence* of
`i` on `f` is the mean square of this derivative (`BitString.influence`), and the *total
influence* of `f` is the sum of its influences (`BitString.totalInfluence`).

Differentiating in `i` removes `i` from the sets containing it and kills the others
(`BitString.fourierCoeff_derivative`), so the influence of `i` is the Fourier weight of `f` on the
sets containing `i` (`BitString.influence_eq_sum_fourierCoeff_sq`), and the total influence weighs
each squared coefficient by the size of its set
(`BitString.totalInfluence_eq_sum_card_mul_fourierCoeff_sq`). Since the variance is the weight on
the nonempty sets (`BitString.expect_sub_expect_sq_eq_sum_fourierCoeff_sq`), it is at most the
total influence (the **Poincaré inequality**, `BitString.expect_sub_expect_sq_le_totalInfluence`).

For a Boolean function read as signs, the derivative in `i` takes the values `0` and `±1`
(`BitString.sq_derivative_signVal`) and is nonzero exactly where flipping bit `i` changes the value
(`BitString.derivative_signVal_ne_zero_iff`). So the influence of `i` is the probability that
flipping bit `i` changes the value (`BitString.influence_signVal`,
`BitString.influence_signVal_eq_dens`), it is nonzero exactly when some flip of bit `i` changes the
value (`BitString.influence_signVal_ne_zero_iff`), and the total influence is the expected number
of bits whose flip changes the value, the *average sensitivity* (`BitString.totalInfluence_signVal`)
[O'Donnell, Sections 2.2 and 2.3][ODonnell2014].

## Main definitions

* `Cslib.BitString.derivative`: the derivative in a coordinate.
* `Cslib.BitString.influence`: the influence of a coordinate.
* `Cslib.BitString.totalInfluence`: the total influence.

## Main results

* `Cslib.BitString.derivative_chi`, `Cslib.BitString.fourierCoeff_derivative`: the derivative of
  a character, and the Fourier coefficients of a derivative.
* `Cslib.BitString.influence_eq_sum_fourierCoeff_sq`: the influence of `i` is the Fourier weight
  on the sets containing `i`.
* `Cslib.BitString.influence_signVal`, `Cslib.BitString.influence_signVal_eq_dens`: the influence
  on a Boolean function is the probability that a flip changes its value.
* `Cslib.BitString.influence_signVal_ne_zero_iff`: a coordinate has nonzero influence on a Boolean
  function exactly when flipping it changes the value on some input.
* `Cslib.BitString.totalInfluence_eq_sum_card_mul_fourierCoeff_sq`: the spectral formula for the
  total influence.
* `Cslib.BitString.totalInfluence_signVal`: the total influence of a Boolean function is the
  expected number of sensitive coordinates, for an arbitrary finite coordinate type.
* `Cslib.BitString.expect_sub_expect_sq_eq_sum_fourierCoeff_sq`: the variance is the Fourier
  weight on the nonempty sets.
* `Cslib.BitString.expect_sub_expect_sq_le_totalInfluence`: the Poincaré inequality.
* `Cslib.BitString.influence_chi`, `Cslib.BitString.totalInfluence_chi`: the influences of a
  character.
* `Cslib.BitString.totalInfluence_le_mul_expect_sq`: the total influence is at most the number of
  coordinates times the mean square.
* `Cslib.BitString.expect_sub_expect_sq_signVal_le_one`,
  `Cslib.BitString.influence_signVal_le_one`: a Boolean function read as signs has variance and
  influences at most one.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- The derivative of `f` in coordinate `i`: half the difference between the values of `f` at
bit `i` equal to `false`, of sign `1`, and to `true`, of sign `-1`. -/
noncomputable def derivative (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  (f (update x i false) - f (update x i true)) / 2

/-- The derivative in `i` does not depend on bit `i`. -/
@[simp] theorem derivative_update (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) (b : Bool) :
    derivative i f (update x i b) = derivative i f x := by
  simp only [derivative, update_idem]

/-- The derivative of a character: differentiating in `i` removes `i` from a set containing it,
and kills the characters of the other sets. -/
theorem derivative_chi (i : ι) (S : Finset ι) (x : ι → Bool) :
    derivative i (chi ℝ S) x = if i ∈ S then chi ℝ (S.erase i) x else 0 := by
  split_ifs with hi
  · rw [derivative, chi_update_of_mem hi, chi_update_of_mem hi]
    simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one]
    ring
  · rw [derivative, chi_update_of_notMem hi, chi_update_of_notMem hi, sub_self, zero_div]

/-- Changing bit `i` of `x` gives the two points with bit `i` set to `false` and to `true`. -/
private theorem update_false_true_eq (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) :
    (f (update x i false) = f (update x i true)) ↔ f (update x i !x i) = f x := by
  cases h : x i
  · rw [show update x i false = x from update_eq_self_iff.2 h.symm, Bool.not_false, eq_comm]
  · rw [show update x i true = x from update_eq_self_iff.2 h.symm, Bool.not_true]

/-- The derivative of a Boolean function read as signs takes the values `0` and `±1`, so its
square is its absolute value. -/
theorem sq_derivative_signVal (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) :
    derivative i (fun x => signVal (f x)) x ^ 2 = |derivative i (fun x => signVal (f x)) x| := by
  simp only [derivative]
  cases f (update x i false) <;> cases f (update x i true) <;> norm_num

/-- The derivative in `i` of a Boolean function read as signs is nonzero exactly where flipping
bit `i` changes the value. -/
theorem derivative_signVal_ne_zero_iff (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) :
    derivative i (fun x => signVal (f x)) x ≠ 0 ↔ f (update x i !x i) ≠ f x := by
  rw [ne_eq, ne_eq, ← update_false_true_eq, derivative]
  cases f (update x i false) <;> cases f (update x i true) <;> norm_num

variable [Fintype ι]

/-- **The Fourier expansion of a derivative**: differentiating in `i` keeps the sets containing
`i`, with `i` removed. -/
theorem derivative_eq_sum (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    derivative i f x = ∑ S with i ∈ S, fourierCoeff f S * chi ℝ (S.erase i) x := by
  rw [derivative, ← sum_fourierCoeff_mul_chi f, ← sum_fourierCoeff_mul_chi f, ← sum_sub_distrib,
    sum_div, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  rw [← mul_sub, mul_div_assoc]
  change fourierCoeff f S * derivative i (chi ℝ S) x = _
  rw [derivative_chi, mul_ite, mul_zero]

/-- **The Fourier coefficients of a derivative**: the coefficient of the derivative in `i` on a
set avoiding `i` is the coefficient of `f` on the set with `i` added, and it vanishes on the sets
containing `i` [O'Donnell, Section 2.2][ODonnell2014]. -/
theorem fourierCoeff_derivative (i : ι) (f : (ι → Bool) → ℝ) (T : Finset ι) :
    fourierCoeff (derivative i f) T = if i ∈ T then 0 else fourierCoeff f (insert i T) := by
  have h : derivative i f =
      fun x => ∑ U, (if i ∈ U then 0 else fourierCoeff f (insert i U)) * chi ℝ U x := by
    funext x
    rw [derivative_eq_sum, sum_filter_mem_eq_sum_filter_notMem i, sum_filter]
    refine sum_congr rfl fun U _ => ?_
    split_ifs with hU
    · rw [zero_mul]
    · rw [erase_insert hU]
  rw [h, fourierCoeff_sum_mul_chi]

/-- The influence of coordinate `i` on `f`: the mean square of the derivative of `f` in `i`. -/
noncomputable def influence (i : ι) (f : (ι → Bool) → ℝ) : ℝ :=
  𝔼 x, derivative i f x ^ 2

/-- Influences are nonnegative. -/
theorem influence_nonneg (i : ι) (f : (ι → Bool) → ℝ) : 0 ≤ influence i f :=
  expect_nonneg fun _ _ => sq_nonneg _

/-- **The influence of `i` is the Fourier weight on the sets containing `i`**
[O'Donnell, Section 2.2][ODonnell2014]. -/
theorem influence_eq_sum_fourierCoeff_sq (i : ι) (f : (ι → Bool) → ℝ) :
    influence i f = ∑ S with i ∈ S, fourierCoeff f S ^ 2 := by
  rw [influence, expect_sq_eq_sum_fourierCoeff_sq, sum_filter_mem_eq_sum_filter_notMem i,
    sum_filter]
  refine sum_congr rfl fun T _ => ?_
  rw [fourierCoeff_derivative]
  split_ifs <;> simp

/-- The influence of a coordinate is at most the mean square. -/
theorem influence_le_expect_sq (i : ι) (f : (ι → Bool) → ℝ) :
    influence i f ≤ 𝔼 x, f x ^ 2 := by
  rw [influence_eq_sum_fourierCoeff_sq, expect_sq_eq_sum_fourierCoeff_sq]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- The influence of `i` on a character is one if `i` is in its set, and zero otherwise. -/
theorem influence_chi (i : ι) (S : Finset ι) :
    influence i (chi ℝ S) = if i ∈ S then 1 else 0 := by
  have h (x : ι → Bool) : chi ℝ (S.erase i) x ^ 2 = 1 := by
    rw [sq, chi_mul_chi, symmDiff_self, bot_eq_empty, chi_empty]
  simp only [influence, derivative_chi]
  split_ifs
  · simp only [h, expect_const univ_nonempty]
  · simp

/-- **The influence on a Boolean function** read as signs is the probability that flipping bit
`i` changes the value [O'Donnell, Section 2.2][ODonnell2014]. -/
theorem influence_signVal (i : ι) (f : (ι → Bool) → Bool) :
    influence i (fun x => signVal (f x)) =
      𝔼 x, if f (update x i !x i) = f x then 0 else 1 := by
  refine expect_congr rfl fun x _ => ?_
  rw [derivative, ← if_congr (update_false_true_eq f i x) rfl rfl]
  cases f (update x i false) <;> cases f (update x i true) <;> norm_num

/-- The influence of `i` on a Boolean function read as signs is the density of the points where
its derivative in `i` is nonzero. -/
theorem influence_signVal_eq_dens (f : (ι → Bool) → Bool) (i : ι) :
    influence i (fun x => signVal (f x)) =
      (dens {x | derivative i (fun x => signVal (f x)) x ≠ 0} : ℝ) := by
  rw [influence_signVal, ← Fintype.expect_boole]
  refine expect_congr rfl fun x _ => ?_
  simp only [derivative_signVal_ne_zero_iff, ne_eq, ite_not]

/-- **Relevant coordinates**: a coordinate has nonzero influence on a Boolean function read as
signs exactly when flipping it changes the value of the function on some input. -/
theorem influence_signVal_ne_zero_iff (f : (ι → Bool) → Bool) (i : ι) :
    influence i (fun x => signVal (f x)) ≠ 0 ↔ ∃ x, f (update x i !x i) ≠ f x := by
  rw [influence_signVal_eq_dens, ne_eq, NNRat.cast_eq_zero, ← ne_eq, dens_ne_zero,
    filter_nonempty_iff]
  simp only [mem_univ, true_and, derivative_signVal_ne_zero_iff]

/-- The total influence of `f`: the sum of the influences of the coordinates. -/
noncomputable def totalInfluence (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ i, influence i f

/-- The total influence is nonnegative. -/
theorem totalInfluence_nonneg (f : (ι → Bool) → ℝ) : 0 ≤ totalInfluence f :=
  sum_nonneg fun i _ => influence_nonneg i f

/-- The influence of a coordinate is at most the total influence. -/
theorem influence_le_totalInfluence (i : ι) (f : (ι → Bool) → ℝ) :
    influence i f ≤ totalInfluence f :=
  single_le_sum (fun j _ => influence_nonneg j f) (mem_univ i)

/-- **The spectral formula for the total influence**: each squared Fourier coefficient counts as
many times as its set has elements [O'Donnell, Section 2.3][ODonnell2014]. -/
theorem totalInfluence_eq_sum_card_mul_fourierCoeff_sq (f : (ι → Bool) → ℝ) :
    totalInfluence f = ∑ S, (#S : ℝ) * fourierCoeff f S ^ 2 := by
  simp only [totalInfluence, influence_eq_sum_fourierCoeff_sq, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]

/-- **The total influence of a Boolean function** read as signs is its *average sensitivity*: the
expected number of bits whose flip changes the value [O'Donnell, Section 2.3][ODonnell2014]. -/
theorem totalInfluence_signVal (f : (ι → Bool) → Bool) :
    totalInfluence (fun x => signVal (f x)) =
      𝔼 x, (#{i | f (Function.update x i (!x i)) ≠ f x} : ℝ) := by
  simp only [totalInfluence, influence_signVal, natCast_card_filter, ite_not]
  exact (expect_sum_comm _ _ _).symm

/-- A character has total influence the size of its set. -/
theorem totalInfluence_chi (S : Finset ι) : totalInfluence (chi ℝ S) = #S := by
  simp [totalInfluence, influence_chi]

/-- **The variance is the Fourier weight on the nonempty sets**
[O'Donnell, Section 1.4][ODonnell2014]. -/
theorem expect_sub_expect_sq_eq_sum_fourierCoeff_sq (f : (ι → Bool) → ℝ) :
    𝔼 x, (f x - 𝔼 y, f y) ^ 2 = ∑ S with S ≠ ∅, fourierCoeff f S ^ 2 := by
  rw [expect_sq_eq_sum_fourierCoeff_sq, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_sub, fourierCoeff_const, ← fourierCoeff_empty]
  by_cases hS : S = ∅ <;> simp [hS]

/-- **The Poincaré inequality**: the variance is at most the total influence
[O'Donnell, Section 2.3][ODonnell2014]. -/
theorem expect_sub_expect_sq_le_totalInfluence (f : (ι → Bool) → ℝ) :
    𝔼 x, (f x - 𝔼 y, f y) ^ 2 ≤ totalInfluence f := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq, totalInfluence_eq_sum_card_mul_fourierCoeff_sq,
    sum_filter]
  refine sum_le_sum fun S _ => ?_
  split_ifs with hS
  · exact le_mul_of_one_le_left (sq_nonneg _)
      (Nat.one_le_cast.2 (card_pos.2 (nonempty_iff_ne_empty.2 hS)))
  · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- The total influence is at most the number of coordinates times the mean square. -/
theorem totalInfluence_le_mul_expect_sq (f : (ι → Bool) → ℝ) :
    totalInfluence f ≤ Fintype.card ι * 𝔼 x, f x ^ 2 := by
  rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq, expect_sq_eq_sum_fourierCoeff_sq, mul_sum]
  refine sum_le_sum fun S _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact_mod_cast card_le_univ S

/-- The variance of a Boolean function read as signs is at most one. -/
theorem expect_sub_expect_sq_signVal_le_one (f : (ι → Bool) → Bool) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 ≤ 1 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq, ← sum_fourierCoeff_sq_signVal f]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- The influence of a coordinate on a Boolean function read as signs is at most one. -/
theorem influence_signVal_le_one (f : (ι → Bool) → Bool) (i : ι) :
    influence i (fun x => signVal (f x)) ≤ 1 := by
  refine (influence_le_expect_sq i _).trans_eq ?_
  simp only [sq, signVal_mul_self]
  exact expect_const univ_nonempty 1

end Cslib.BitString
