/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.SqrtLog
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting the nodes of a recursion tree

A recursion whose calls at depth `d` have at most `b d` children, with at most `k` levels below
depth `d`, has at most `Nat.recursionBound b k d` nodes below and including a call at depth `d`:
one for the call, plus `b d` subtrees of one level less (`Nat.recursionBound_succ`). This is at
most `k + 1` times the product of the branching factors (`Nat.recursionBound_le`).

**Recursion trees of size `2 ^ O(n / √(log n))`.** If a call at depth `j` has at most
`2 ^ (c ⌊log₂ n⌋ + e j)` children, there are at most `⌊log₂ n⌋` levels, and the excess exponents
sum to `O(n / √⌊log₂ n⌋)`, then the tree has `2 ^ O(n / √⌊log₂ n⌋)` nodes
(`Nat.exists_recursionBound_le_two_pow_div_sqrt_log_two`), in the natural-number scale of
`Nat.exists_three_pow_mul_le_two_pow_div_sqrt_log_two`. The polynomial factors `2 ^ (c ⌊log₂ n⌋)`
contribute `2 ^ O(log² n)`, which the scale absorbs. Excess exponents halving with the depth sum to
at most twice the first one (`Nat.sum_div_two_pow_le`).

This is the call count in the proof of Theorem D.1 of [OpenAI2026ETH] (Appendix D.4.7, p. 64):
a call at depth `d` has `s ^ O(1) exp(O(s / √λ · (√2 / 8) ^ d))` children and there are
`O(log λ)` levels.

## Main definitions

* `Nat.recursionBound`: the node bound of a recursion tree with given branching factors.

## Main results

* `Nat.recursionBound_le`: at most `k + 1` times the product of the branching factors.
* `Nat.sum_div_two_pow_le`: `∑ j < D, x / 2 ^ j ≤ 2 x`.
* `Nat.exists_recursionBound_le_two_pow_div_sqrt_log_two`: recursion trees of size
  `2 ^ O(n / √⌊log₂ n⌋)`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Nat

open Finset

/-- The node bound of a recursion tree whose calls at depth `d` have at most `b d` children,
for a call at depth `d` with at most `k` levels below it. -/
@[expose] def recursionBound (b : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, d => 1 + b d * recursionBound b k (d + 1)

@[simp] theorem recursionBound_zero (b : ℕ → ℕ) (d : ℕ) : recursionBound b 0 d = 1 := rfl

/-- A call is one node above its children's subtrees. -/
theorem recursionBound_succ (b : ℕ → ℕ) (k d : ℕ) :
    recursionBound b (k + 1) d = 1 + b d * recursionBound b k (d + 1) := rfl

/-- **The node bound is at most `k + 1` times the product of the branching factors.** -/
theorem recursionBound_le (b : ℕ → ℕ) (k d : ℕ) :
    recursionBound b k d ≤ (k + 1) * ∏ j ∈ range k, max 1 (b (d + j)) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [recursionBound_succ, prod_range_succ']
    set P := ∏ j ∈ range k, max 1 (b (d + (j + 1)))
    have hP : 1 ≤ P := one_le_prod fun _ _ => le_max_left _ _
    have hm : 1 ≤ max 1 (b d) := le_max_left _ _
    have hb : b d ≤ max 1 (b d) := le_max_right _ _
    have ih' : recursionBound b k (d + 1) ≤ (k + 1) * P := by
      simpa only [Nat.add_assoc, Nat.add_comm 1] using ih (d + 1)
    simp only [Nat.add_zero]
    calc 1 + b d * recursionBound b k (d + 1) ≤ max 1 (b d) * P + max 1 (b d) * ((k + 1) * P) :=
          Nat.add_le_add (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
            (Nat.mul_le_mul hb ih')
      _ = (k + 1 + 1) * (P * max 1 (b d)) := by ring

/-- **Halving excess exponents**: `∑ j < D, x / 2 ^ j ≤ 2 x`. -/
theorem sum_div_two_pow_le (x D : ℕ) : ∑ j ∈ range D, x / 2 ^ j ≤ 2 * x := by
  induction D generalizing x with
  | zero => simp
  | succ D ih =>
    rw [sum_range_succ']
    have h : ∑ j ∈ range D, x / 2 ^ (j + 1) = ∑ j ∈ range D, x / 2 / 2 ^ j :=
      sum_congr rfl fun j _ => by rw [pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
    rw [h, pow_zero, Nat.div_one]
    have := ih (x / 2)
    have := Nat.div_mul_le_self x 2
    omega

/-- `L ^ 3 ≤ 8 * 2 ^ L`. -/
private theorem cube_le_eight_mul_two_pow (L : ℕ) : L ^ 3 ≤ 8 * 2 ^ L := by
  have hlarge : ∀ m : ℕ, (m + 9) ^ 3 ≤ 8 * 2 ^ (m + 9) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have h : (m + 1 + 9) ^ 3 ≤ 2 * (m + 9) ^ 3 := by ring_nf; nlinarith
      calc (m + 1 + 9) ^ 3 ≤ 2 * (m + 9) ^ 3 := h
        _ ≤ 2 * (8 * 2 ^ (m + 9)) := Nat.mul_le_mul_left 2 ih
        _ = 8 * 2 ^ (m + 1 + 9) := by ring
  rcases Nat.lt_or_ge L 9 with hL | hL
  · interval_cases L <;> norm_num
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hL
    exact hlarge m

/-- The square of the logarithm is `O(n / √⌊log₂ n⌋)`: `⌊log₂ n⌋ ^ 2 ≤ 16 (n / √⌊log₂ n⌋)` from
`n = 2` on, since `⌊log₂ n⌋ ^ 2 √⌊log₂ n⌋ ≤ ⌊log₂ n⌋ ^ 3 ≤ 8 n`. -/
theorem log_two_sq_le_div_sqrt_log_two {n : ℕ} (hn : 2 ≤ n) :
    log 2 n ^ 2 ≤ 16 * (n / sqrt (log 2 n)) := by
  set L := log 2 n
  have hr : 1 ≤ sqrt L := one_le_sqrt_log_two hn
  have hS : 1 ≤ n / sqrt L := one_le_div_sqrt_log_two hn
  have hcube : L ^ 2 * sqrt L ≤ 8 * n :=
    calc L ^ 2 * sqrt L ≤ L ^ 2 * L := Nat.mul_le_mul_left _ (sqrt_le_self L)
      _ = L ^ 3 := by ring
      _ ≤ 8 * 2 ^ L := cube_le_eight_mul_two_pow L
      _ ≤ 8 * n := Nat.mul_le_mul_left 8 (pow_log_le_self 2 (by omega))
  have h1 : L ^ 2 ≤ 8 * n / sqrt L := (Nat.le_div_iff_mul_le hr).2 hcube
  have h2 := mul_div_le_mul_div_add 8 n (sqrt L)
  omega

/-- **Recursion trees of size `2 ^ O(n / √⌊log₂ n⌋)`.** For constants `c` and `E` there is `K`
such that, from `n = 2` on: if a call at depth `j < D` has at most `2 ^ (c ⌊log₂ n⌋ + e j)`
children, `D ≤ ⌊log₂ n⌋`, and `∑ j < D, e j ≤ E (n / √⌊log₂ n⌋)`, then
`(D + 1) ∏ j < D, max 1 (b j) ≤ 2 ^ (K n / √⌊log₂ n⌋)`, which bounds the nodes of the recursion
tree by `recursionBound_le`. -/
theorem exists_recursionBound_le_two_pow_div_sqrt_log_two (c E : ℕ) :
    ∃ K, ∀ (n D : ℕ) (b e : ℕ → ℕ), 2 ≤ n → D ≤ log 2 n →
      (∀ j < D, b j ≤ 2 ^ (c * log 2 n + e j)) →
      ∑ j ∈ range D, e j ≤ E * (n / sqrt (log 2 n)) →
      (D + 1) * ∏ j ∈ range D, max 1 (b j) ≤ 2 ^ (K * n / sqrt (log 2 n)) := by
  refine ⟨1 + 16 * c + E, fun n D b e hn hD hb he => ?_⟩
  set L := log 2 n
  set S := n / sqrt L
  have hL : L ≤ S := log_two_le_div_sqrt_log_two n
  have hL2 : L ^ 2 ≤ 16 * S := log_two_sq_le_div_sqrt_log_two hn
  have hD1 : D + 1 ≤ 2 ^ L := (Nat.add_le_add_right hD 1).trans Nat.lt_two_pow_self
  have hprod : ∏ j ∈ range D, max 1 (b j) ≤ 2 ^ (D * (c * L) + ∑ j ∈ range D, e j) := by
    calc ∏ j ∈ range D, max 1 (b j) ≤ ∏ j ∈ range D, 2 ^ (c * L + e j) :=
          prod_le_prod fun j hj => max_le Nat.one_le_two_pow (hb j (mem_range.mp hj))
      _ = 2 ^ (∑ j ∈ range D, (c * L + e j)) := (Finset.prod_pow_eq_pow_sum _ _ _)
      _ = 2 ^ (D * (c * L) + ∑ j ∈ range D, e j) := by
          rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
  have hexp : L + (D * (c * L) + ∑ j ∈ range D, e j) ≤ (1 + 16 * c + E) * S := by
    have h1 : D * (c * L) ≤ c * (16 * S) :=
      calc D * (c * L) ≤ L * (c * L) := Nat.mul_le_mul_right _ hD
        _ = c * L ^ 2 := by ring
        _ ≤ c * (16 * S) := Nat.mul_le_mul_left _ hL2
    nlinarith
  calc (D + 1) * ∏ j ∈ range D, max 1 (b j)
      ≤ 2 ^ L * 2 ^ (D * (c * L) + ∑ j ∈ range D, e j) := Nat.mul_le_mul hD1 hprod
    _ = 2 ^ (L + (D * (c * L) + ∑ j ∈ range D, e j)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((1 + 16 * c + E) * S) := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ 2 ^ ((1 + 16 * c + E) * n / sqrt L) :=
        Nat.pow_le_pow_right (by norm_num) (mul_div_le_mul_div_assoc _ _ _)

end Nat
