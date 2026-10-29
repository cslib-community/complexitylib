/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Data.BitString.Agree
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Uniformly random bits on a set of positions

The bits of a uniformly random word `ι → Bool` on a set `S` of positions all take a given value
with probability `2 ^ (-|S|)` (`BitString.expect_ite_forall_mem_eq`), by the count of words
agreeing off a set (`BitString.card_filter_forall_notMem_eq`).

## Main results

* `Cslib.BitString.expect_ite_forall_mem_eq`: a set of `k` uniformly random bits takes a given
  value with probability `2 ^ (-k)`.
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

/-- The bits of a set `S` of uniformly random bits are all equal to `b` with probability
`2 ^ (-|S|)`, for any decision procedure of the event. -/
theorem expect_ite_forall_mem_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (b : Bool) [DecidablePred fun x : ι → Bool => ∀ i ∈ S, x i = b] :
    𝔼 x : ι → Bool, (if ∀ i ∈ S, x i = b then (1 : ℝ) else 0) = 2⁻¹ ^ #S := by
  have hcard : #{x : ι → Bool | ∀ i ∈ S, x i = b} = 2 ^ #Sᶜ := by
    rw [← card_filter_forall_notMem_eq Sᶜ fun _ => b]
    refine congrArg card (filter_congr fun x _ => ?_)
    simp only [mem_compl, not_not]
  have hS : #S ≤ Fintype.card ι := card_le_univ S
  rw [expect_eq_sum_div_card, sum_boole, hcard, card_compl, card_univ, Fintype.card_fun,
    Fintype.card_bool]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hS
  rw [hm, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, pow_add, inv_pow,
    mul_comm, ← div_div, div_self (pow_ne_zero _ two_ne_zero), one_div]

end Cslib.BitString
