/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Sign
public import Complexity.Foundations.Data.BitString.Weight
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Balanced Boolean vectors

A Boolean vector `x : ι → Bool` is *balanced* when exactly half of its coordinates are true
(`Cslib.BitString.IsBalanced`): `2 · weight x = |ι|`. Balanced vectors are the "balanced" side of
the Deutsch–Jozsa promise ([de Wolf, §2.4.1][deWolf2019]).

The sum of the signs `(-1)^{x_i}` of a vector is `|ι| - 2 · weight x`
(`Cslib.BitString.sum_signVal_eq_card_sub_two_mul_weight`). So it vanishes exactly on the balanced
vectors (`Cslib.BitString.sum_signVal_eq_zero_iff`), and it is `±|ι|` on the constant ones. This
sum is, up to the factor `2^{-n}`, the amplitude of `|0ⁿ⟩` in the Deutsch–Jozsa algorithm.

## Main definitions

* `Cslib.BitString.IsBalanced`: exactly half of the coordinates are true.

## Main results

* `Cslib.BitString.sum_signVal_eq_card_sub_two_mul_weight`: `∑ᵢ (-1)^{x_i} = |ι| - 2 · weight x`.
* `Cslib.BitString.sum_signVal_eq_zero_iff`: the sum of the signs vanishes exactly on balanced
  vectors.
* `Cslib.BitString.isBalanced_iff_card_filter`: balanced means as many false as true coordinates.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], §2.4.1
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι]

/-- A Boolean vector is **balanced** when exactly half of its coordinates are true:
`2 · weight x = |ι|`. -/
def IsBalanced (x : ι → Bool) : Prop :=
  2 * weight x = Fintype.card ι

theorem isBalanced_iff {x : ι → Bool} : IsBalanced x ↔ 2 * weight x = Fintype.card ι :=
  Iff.rfl

instance (x : ι → Bool) : Decidable (IsBalanced x) :=
  inferInstanceAs (Decidable (2 * weight x = Fintype.card ι))

/-- A vector is balanced exactly when it has as many false as true coordinates. -/
theorem isBalanced_iff_card_filter {x : ι → Bool} :
    IsBalanced x ↔ #{i | x i = false} = #{i | x i = true} := by
  rw [isBalanced_iff, card_filter_eq_false_eq_card_sub_weight, ← weight]
  have := weight_le x
  omega

/-- A balanced vector has an even number of coordinates. -/
theorem IsBalanced.even_card {x : ι → Bool} (hx : IsBalanced x) : Even (Fintype.card ι) :=
  ⟨weight x, by rw [← hx]; ring⟩

/-- **The sum of the signs** of a Boolean vector: `∑ᵢ (-1)^{x_i} = |ι| - 2 · weight x`. -/
theorem sum_signVal_eq_card_sub_two_mul_weight (x : ι → Bool) :
    ∑ i, signVal (x i) = Fintype.card ι - 2 * (weight x : ℝ) := by
  simp only [signVal_eq_one_sub_two_mul_bitVal, sum_sub_distrib, sum_const, card_univ,
    nsmul_eq_mul, mul_one, ← mul_sum]
  congr 2
  rw [weight_eq_sum_toNat, Nat.cast_sum]
  exact sum_congr rfl fun i _ => by cases x i <;> simp

/-- The signs of a Boolean vector sum to zero exactly when it is balanced. -/
theorem sum_signVal_eq_zero_iff {x : ι → Bool} : ∑ i, signVal (x i) = 0 ↔ IsBalanced x := by
  rw [sum_signVal_eq_card_sub_two_mul_weight, sub_eq_zero, isBalanced_iff, eq_comm]
  exact_mod_cast Iff.rfl

/-- The signs of a balanced vector sum to zero. -/
theorem IsBalanced.sum_signVal_eq_zero {x : ι → Bool} (hx : IsBalanced x) :
    ∑ i, signVal (x i) = 0 :=
  sum_signVal_eq_zero_iff.mpr hx

end Cslib.BitString
