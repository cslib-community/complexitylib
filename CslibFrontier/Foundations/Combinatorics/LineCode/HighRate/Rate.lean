/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# The dimension of the high-rate line code

The high-rate line code on `K ^ ℓ` is spanned by the monomials whose exponent matrices, with
`m` columns of `A` possible values each, have a zero column. There are
`retainedDimension A m = A ^ m - (A - 1) ^ m` of them (`card_exists_eq_retainedDimension`). By
Bernoulli's inequality this is at least a `P / (P + 1)` fraction of all `A ^ m` matrices once
`m ≥ P * (A - 1)` (`retainedDimension_rate`), so the rate of the code tends to one.

## Main definitions

* `Cslib.LineCode.HighRate.retainedDimension`: the number `A ^ m - (A - 1) ^ m`.

## Main results

* `Cslib.LineCode.HighRate.card_exists_eq_retainedDimension`: `retainedDimension (card α) m`
  words of length `m` over `α` contain a given letter.
* `Cslib.LineCode.HighRate.retainedDimension_pos`: the dimension is positive.
* `Cslib.LineCode.HighRate.retainedDimension_rate`: the denominator-free rate bound.

## References

* Adapted from MassProduction/HighRate/Rate.lean and MassProduction/HighRate/DigitMonomials.lean
  in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode.HighRate

open Finset

/-- The number `A ^ m - (A - 1) ^ m` of words of length `m` over an alphabet of `A` letters that
contain a given letter. -/
def retainedDimension (A m : ℕ) : ℕ :=
  A ^ m - (A - 1) ^ m

/-- Exactly `retainedDimension (Fintype.card α) m` words `w : Fin m → α` contain the letter
`a`. -/
theorem card_exists_eq_retainedDimension (α : Type*) [Fintype α] [DecidableEq α] (a : α)
    (m : ℕ) :
    Fintype.card {w : Fin m → α // ∃ j, w j = a} = retainedDimension (Fintype.card α) m := by
  have hcompl := Fintype.card_subtype_compl fun w : Fin m → α => ∃ j, w j = a
  have havoid : Fintype.card {w : Fin m → α // ¬∃ j, w j = a} = (Fintype.card α - 1) ^ m := by
    simp only [not_exists]
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ b => ¬b = a)), Fintype.card_pi,
      prod_const, card_univ, Fintype.card_fin, Fintype.card_subtype_compl fun b : α => b = a,
      Fintype.card_subtype_eq]
  rw [havoid, Fintype.card_fun, Fintype.card_fin] at hcompl
  have hle : Fintype.card {w : Fin m → α // ∃ j, w j = a} ≤ Fintype.card α ^ m := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using
      Fintype.card_subtype_le fun w : Fin m → α => ∃ j, w j = a
  rw [retainedDimension]
  omega

/-- The dimension `retainedDimension A m` is positive when `0 < A` and `0 < m`. -/
theorem retainedDimension_pos {A m : ℕ} (hA : 0 < A) (hm : 0 < m) : 0 < retainedDimension A m :=
  Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (Nat.sub_lt hA one_pos) hm.ne')

/-- **Rate bound.** If `0 < m` and `P * (A - 1) ≤ m`, then `retainedDimension A m` is at least a
`P / (P + 1)` fraction of `A ^ m`: `P * A ^ m ≤ (P + 1) * retainedDimension A m`. -/
theorem retainedDimension_rate (A m P : ℕ) (hm : 0 < m) (hmP : P * (A - 1) ≤ m) :
    P * A ^ m ≤ (P + 1) * retainedDimension A m := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp [zero_pow hm.ne']
  have hle : (A - 1) ^ m ≤ A ^ m := Nat.pow_le_pow_left (Nat.sub_le A 1) m
  -- Bernoulli's inequality: `(A - 1) ^ m + m * (A - 1) ^ (m - 1) ≤ A ^ m`.
  have hbern := pow_add_mul_le_add_pow (a := A - 1) (b := 1) (Nat.zero_le _) (Nat.zero_le _) m
  rw [mul_one, Nat.sub_add_cancel hA, Nat.cast_id] at hbern
  have hmiss : P * (A - 1) ^ m ≤ retainedDimension A m := by
    calc P * (A - 1) ^ m = P * (A - 1) * (A - 1) ^ (m - 1) := by
          rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]
      _ ≤ m * (A - 1) ^ (m - 1) := Nat.mul_le_mul_right _ hmP
      _ ≤ retainedDimension A m := by
          rw [retainedDimension]
          omega
  calc P * A ^ m = P * retainedDimension A m + P * (A - 1) ^ m := by
        rw [← mul_add, retainedDimension, Nat.sub_add_cancel hle]
    _ ≤ P * retainedDimension A m + retainedDimension A m := Nat.add_le_add_left hmiss _
    _ = (P + 1) * retainedDimension A m := by ring

end Cslib.LineCode.HighRate
