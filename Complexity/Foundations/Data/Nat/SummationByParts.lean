/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/BigOperators/Intervals.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Summation by parts (Abel summation) for natural-number sequences

Pure-`ℕ` summation by parts (Abel summation) for a non-increasing sequence `b : ℕ → ℕ`, avoiding
cast round-trips through `ℤ`.

## Main results

* `Nat.sum_mul_eq_sum_prefix_sub`: if `b (i + 1) ≤ b i` for all `i < m`, then
  `∑ i ∈ Finset.range (m + 1), a i * b i` equals
  `(∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), a j) * (b i - b (i + 1))) +`
  `(∑ j ∈ Finset.range (m + 1), a j) * b m`.
-/

public section

namespace Nat

open scoped BigOperators

/-- Pure-`ℕ` summation by parts (Abel summation) for a non-increasing sequence `b`. -/
theorem sum_mul_eq_sum_prefix_sub (a b : ℕ → ℕ) :
    ∀ m : ℕ, (∀ i < m, b (i + 1) ≤ b i) →
      ∑ i ∈ Finset.range (m + 1), a i * b i =
        (∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), a j) * (b i - b (i + 1))) +
          (∑ j ∈ Finset.range (m + 1), a j) * b m
  | 0, _ => by simp
  | m + 1, hmono => by
    have ih := sum_mul_eq_sum_prefix_sub a b m (fun i hi => hmono i (Nat.lt_succ_of_lt hi))
    have hbm : b (m + 1) ≤ b m := hmono m (Nat.lt_succ_self m)
    let S := ∑ j ∈ Finset.range (m + 1), a j
    have hstep : S * (b m - b (m + 1)) + (S + a (m + 1)) * b (m + 1) =
        S * b m + a (m + 1) * b (m + 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.add_mul, ← Nat.add_assoc,
        Nat.sub_add_cancel (Nat.mul_le_mul_left S hbm)]
    conv_lhs => rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ _ m, Finset.sum_range_succ a (m + 1)]
    change (∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), a j) * (b i - b (i + 1))) +
        S * b m + a (m + 1) * b (m + 1) =
      (∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), a j) * (b i - b (i + 1))) +
        S * (b m - b (m + 1)) + (S + a (m + 1)) * b (m + 1)
    rw [Nat.add_assoc, ← hstep, Nat.add_assoc]

end Nat
