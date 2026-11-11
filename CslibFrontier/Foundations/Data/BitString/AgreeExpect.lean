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
import CslibFrontier.Foundations.Data.Fintype.AgreeOn
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Uniformly random bits on a set of positions

The bits of a uniformly random word `ι → Bool` on a set `S` of positions all take a given value
with probability `2 ^ (-|S|)` (`BitString.expect_ite_forall_mem_eq`), by the count of functions
agreeing on a set (`Fintype.card_filter_forall_mem_eq`); so some of them takes the other
value with probability `1 - 2 ^ (-|S|)` (`BitString.expect_ite_exists_mem_eq`).

## Main results

* `Cslib.BitString.expect_ite_forall_mem_eq`: a set of `k` uniformly random bits takes a given
  value with probability `2 ^ (-k)`.
* `Cslib.BitString.expect_ite_exists_mem_eq`: some of `k` uniformly random bits takes a given
  value with probability `1 - 2 ^ (-k)`.
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
    rw [Fintype.card_filter_forall_mem_eq S fun _ => b, Fintype.card_bool]
  have hS : #S ≤ Fintype.card ι := card_le_univ S
  rw [expect_eq_sum_div_card, sum_boole, hcard, card_compl, card_univ, Fintype.card_fun,
    Fintype.card_bool]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hS
  rw [hm, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, pow_add, inv_pow,
    mul_comm, ← div_div, div_self (pow_ne_zero _ two_ne_zero), one_div]

/-- Some bit of a set `S` of uniformly random bits equals `b` with probability `1 - 2 ^ (-|S|)`,
for any decision procedure of the event. -/
theorem expect_ite_exists_mem_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (b : Bool) [DecidablePred fun x : ι → Bool => ∃ i ∈ S, x i = b] :
    𝔼 x : ι → Bool, (if ∃ i ∈ S, x i = b then (1 : ℝ) else 0) = 1 - 2⁻¹ ^ #S := by
  have e (x : ι → Bool) : (if ∃ i ∈ S, x i = b then (1 : ℝ) else 0) =
      1 - if ∀ i ∈ S, x i = !b then 1 else 0 := by
    have : (∃ i ∈ S, x i = b) ↔ ¬∀ i ∈ S, x i = !b := by
      simp only [not_forall, Bool.eq_not, not_not, exists_prop]
    by_cases h : ∀ i ∈ S, x i = !b
    · rw [ite_eq_right (this.not_left.2 h), ite_eq_left h, sub_self]
    · rw [ite_eq_left (this.2 h), ite_eq_right h, sub_zero]
  rw [expect_congr rfl fun x _ => e x, expect_sub_distrib, Fintype.expect_const,
    expect_ite_forall_mem_eq]

end Cslib.BitString
