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
# Binary sizes of products, powers, and factorials

These pure facts are moved unchanged from the binary arithmetic facade. They retain their
qualified names without depending on a machine calculus.
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

end Nat
