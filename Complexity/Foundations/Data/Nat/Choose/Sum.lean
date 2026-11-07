/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Data/Nat/Choose/Sum.lean`)

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith

/-!
# Polynomial bounds on partial binomial sums

`∑_{i ≤ d} n ^ i ≤ (n + 1) ^ d` (`Cslib.sum_range_pow_le_add_one_pow`), hence
`∑_{i ≤ d} (n choose i) ≤ (n + 1) ^ d` (`Cslib.sum_range_choose_le_add_one_pow`). The second bound
counts the subsets of at most `d` of `n` points, as in Sauer's lemma and in low-degree polynomial
dimension counts. `Cslib.sum_choose_le_exp_one_mul_div_pow` gives the sharper `(e n / d) ^ d`.

## Main results

* `Cslib.sum_range_pow_le_add_one_pow`: `∑_{i ≤ d} n ^ i ≤ (n + 1) ^ d`.
* `Cslib.sum_range_choose_le_add_one_pow`: `∑_{i ≤ d} (n choose i) ≤ (n + 1) ^ d`.
-/

public section

open Finset

namespace Cslib

/-- `∑_{i ≤ d} n ^ i ≤ (n + 1) ^ d`. -/
theorem sum_range_pow_le_add_one_pow (n d : ℕ) :
    ∑ i ∈ range (d + 1), n ^ i ≤ (n + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, pow_succ (n + 1) d]
    have h : n ^ (d + 1) ≤ (n + 1) ^ d * n := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right n (Nat.pow_le_pow_left (Nat.le_succ n) d)
    linarith [mul_add ((n + 1) ^ d) n 1]

/-- `∑_{i ≤ d} (n choose i) ≤ (n + 1) ^ d`. -/
theorem sum_range_choose_le_add_one_pow (n d : ℕ) :
    ∑ i ∈ range (d + 1), n.choose i ≤ (n + 1) ^ d :=
  (sum_le_sum fun i _ => Nat.choose_le_pow n i).trans (sum_range_pow_le_add_one_pow n d)

end Cslib
