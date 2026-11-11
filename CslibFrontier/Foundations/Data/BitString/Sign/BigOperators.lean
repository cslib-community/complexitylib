/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/BitString.lean`)

public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Signs of sums of bits and sign correlations

In the two-element Boolean ring, where `a + b = (a ^^ b)`, the sign of a sum of bits is the product
of their signs (`BitString.signVal_sum`), and the value of a product of bits is the product of
their values (`BitString.bitVal_prod`).

The **sign correlation** `∑ x, signVal (f x) * signVal (g x)` of two words `f g : X → Bool` counts
the positions where they agree minus those where they differ. It is
`2 #{x | f x = g x} - |X|` (`BitString.sum_signVal_mul_signVal_eq_two_mul_card_sub`) and
`|X| - 2 d(f, g)` for the Hamming distance `d` (`BitString.sum_signVal_mul_signVal_eq_card_sub`)
[O'Donnell, Section 1.4][ODonnell2014]. So `f` agrees with `g` on at least a `1 / 2 + ε` fraction
of the positions exactly when their correlation is at least `2 ε |X|`.

## Main results

* `Cslib.BitString.signVal_sum`: the sign of a sum of bits is the product of their signs.
* `Cslib.BitString.bitVal_prod`: the value of a product of bits is the product of their values.
* `Cslib.BitString.sum_signVal_mul_signVal_eq_two_mul_card_sub`,
  `Cslib.BitString.sum_signVal_mul_signVal_eq_card_sub`: the sign correlation of two words by
  agreements and by Hamming distance.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset

/-- The sign of a sum in the two-element Boolean ring is the product of the signs. -/
theorem signVal_sum {α : Type*} (s : Finset α) (f : α → Bool) :
    signVal (∑ a ∈ s, f a) = ∏ a ∈ s, signVal (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, prod_empty]; rfl
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, Bool.add_eq_xor, signVal_xor, ih]

/-- Reading a product of bits as a real number gives the product of the readings. -/
theorem bitVal_prod {α : Type*} (s : Finset α) (f : α → Bool) :
    bitVal ℝ (∏ a ∈ s, f a) = ∏ a ∈ s, bitVal ℝ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, prod_empty]; rfl
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, ← ih, Bool.mul_eq_and]
    cases f a <;> simp

variable {X : Type*} [Fintype X]

/-- **Correlation counts agreements**: the sign correlation of two words is twice the number of
positions where they agree, minus the number of positions. -/
theorem sum_signVal_mul_signVal_eq_two_mul_card_sub (f g : X → Bool) :
    ∑ x, signVal (f x) * signVal (g x) = 2 * #{x | f x = g x} - Fintype.card X := by
  have h (x : X) : signVal (f x) * signVal (g x) = 2 * (if f x = g x then 1 else 0) - 1 := by
    rw [signVal_mul_signVal]
    split_ifs <;> norm_num
  simp only [h, sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_univ, nsmul_eq_mul,
    mul_one]

/-- **Correlation is the length minus twice the distance**: the sign correlation of two words is
the number of positions minus twice their Hamming distance. -/
theorem sum_signVal_mul_signVal_eq_card_sub (f g : X → Bool) :
    ∑ x, signVal (f x) * signVal (g x) = Fintype.card X - 2 * hammingDist f g := by
  rw [sum_signVal_mul_signVal_eq_two_mul_card_sub, ← card_filter_eq_add_hammingDist f g]
  push_cast
  ring

end Cslib.BitString
