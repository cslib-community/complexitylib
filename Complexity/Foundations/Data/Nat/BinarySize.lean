/-
Copyright (c) 2026 Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/-!
# Binary sizes of sums, products, powers, and factorials

These pure facts are moved unchanged from the binary arithmetic facade. They retain their
qualified names without depending on a machine calculus. The bounds `Nat.size_add_le`,
`Nat.size_add_le_max` and `Nat.size_le_self` on the binary lengths of sums and of a number itself
also serve the logarithmic terms of Kolmogorov complexity.
-/

@[expose] public section
namespace Nat

/-- The binary length of a product is at most the binary lengths of the factors together. -/
theorem size_mul_le (m n : ℕ) : (m * n).size ≤ m.size + n.size := by
  refine Nat.size_le.2 ?_
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self m) (Nat.lt_size_self n)

/-- The binary length of a power is at most the exponent times the binary length of the base,
plus one for the zeroth power. -/
theorem size_pow_le (m k : ℕ) : (m ^ k).size ≤ k * m.size + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := size_mul_le (m ^ k) m
    rw [Nat.pow_succ, Nat.succ_mul]
    lia

/-- The binary length of `n!` is at most `n * n.size + 1`. -/
theorem size_factorial_le (n : ℕ) : n.factorial.size ≤ n * n.size + 1 :=
  (Nat.size_le_size n.factorial_le_pow).trans (size_pow_le n n)

/-- The binary length of a sum is at most the binary lengths of the summands together, plus one. -/
theorem size_add_le (m n : ℕ) : (m + n).size ≤ m.size + n.size + 1 := by
  refine Nat.size_le.2 ?_
  have hm := Nat.lt_size_self m
  have hn := Nat.lt_size_self n
  have h₁ : 2 ^ m.size ≤ 2 ^ (m.size + n.size) := Nat.pow_le_pow_right (by lia) (by lia)
  have h₂ : 2 ^ n.size ≤ 2 ^ (m.size + n.size) := Nat.pow_le_pow_right (by lia) (by lia)
  rw [Nat.pow_succ]
  lia

/-- The binary length of a sum is at most one more than the longer binary length of the
summands. -/
theorem size_add_le_max (m n : ℕ) : (m + n).size ≤ max m.size n.size + 1 := by
  refine Nat.size_le.2 ?_
  have hm := (Nat.lt_size_self m).trans_le
    (Nat.pow_le_pow_right (by lia) (le_max_left m.size n.size))
  have hn := (Nat.lt_size_self n).trans_le
    (Nat.pow_le_pow_right (by lia) (le_max_right m.size n.size))
  rw [Nat.pow_succ]
  lia

/-- A binary length is at most the number itself. -/
theorem size_le_self (n : ℕ) : n.size ≤ n :=
  Nat.size_le.2 Nat.lt_two_pow_self

end Nat
