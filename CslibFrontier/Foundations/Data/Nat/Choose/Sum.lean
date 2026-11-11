/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Data/Nat/Choose/Sum.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial bounds on partial binomial sums

`∑_{i ≤ d} n ^ i ≤ (n + 1) ^ d` (`Cslib.sum_range_pow_le_add_one_pow`), hence
`∑_{i ≤ d} (n choose i) ≤ (n + 1) ^ d` (`Cslib.sum_range_choose_le_add_one_pow`). The second bound
counts the subsets of at most `d` of `n` points, as in Sauer's lemma and in low-degree polynomial
dimension counts. `Cslib.sum_choose_le_exp_one_mul_div_pow` gives the sharper `(e n / d) ^ d`.
Weighting by `a ^ ℓ` bounds the volume of a Hamming ball of radius `r`:
`(∑_{j ≤ r} C(ℓ, j)) * a ^ ℓ ≤ a ^ r * (a + 1) ^ ℓ` (`Cslib.sum_range_choose_mul_pow_le`).

## Main results

* `Cslib.sum_range_pow_le_add_one_pow`: `∑_{i ≤ d} n ^ i ≤ (n + 1) ^ d`.
* `Cslib.sum_range_choose_le_add_one_pow`: `∑_{i ≤ d} (n choose i) ≤ (n + 1) ^ d`.
* `Cslib.sum_range_choose_mul_pow_le`: `(∑_{j ≤ r} C(ℓ, j)) * a ^ ℓ ≤ a ^ r * (a + 1) ^ ℓ`.
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

/-- A binomial estimate for the volume of a Hamming ball:
`(∑_{j ≤ r} C(ℓ, j)) * a ^ ℓ ≤ a ^ r * (a + 1) ^ ℓ` for `1 ≤ a`, obtained from the
binomial expansion of `(1 + a) ^ ℓ`. -/
theorem sum_range_choose_mul_pow_le (a ℓ r : ℕ) (ha : 1 ≤ a := by omega) :
    (∑ j ∈ range (r + 1), ℓ.choose j) * a ^ ℓ ≤ a ^ r * (a + 1) ^ ℓ := by
  have hterm : ∀ j ∈ range (r + 1),
      ℓ.choose j * a ^ ℓ ≤ a ^ r * (1 ^ j * a ^ (ℓ - j) * ℓ.choose j) := by
    intro j hj
    rcases lt_or_ge ℓ j with hℓj | hjℓ
    · rw [Nat.choose_eq_zero_of_lt hℓj, zero_mul]
      exact Nat.zero_le _
    have hjr := Nat.lt_succ_iff.1 (mem_range.1 hj)
    calc ℓ.choose j * a ^ ℓ = ℓ.choose j * (a ^ j * a ^ (ℓ - j)) := by
          rw [← pow_add, Nat.add_sub_cancel' hjℓ]
      _ ≤ ℓ.choose j * (a ^ r * a ^ (ℓ - j)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right ha hjr))
      _ = a ^ r * (1 ^ j * a ^ (ℓ - j) * ℓ.choose j) := by ring
  have htail : ∑ j ∈ range (r + 1), 1 ^ j * a ^ (ℓ - j) * ℓ.choose j ≤ (a + 1) ^ ℓ := by
    calc ∑ j ∈ range (r + 1), 1 ^ j * a ^ (ℓ - j) * ℓ.choose j
        ≤ ∑ j ∈ range (ℓ + 1 + (r + 1)), 1 ^ j * a ^ (ℓ - j) * ℓ.choose j :=
          sum_le_sum_of_subset (range_subset_range.2 (by omega))
      _ = (a + 1) ^ ℓ := by
          have h0 : ∑ j ∈ range (r + 1), 1 ^ (ℓ + 1 + j) * a ^ (ℓ - (ℓ + 1 + j)) *
              ℓ.choose (ℓ + 1 + j) = 0 :=
            sum_eq_zero fun j _ => by rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
          rw [sum_range_add, h0, add_zero, show a + 1 = 1 + a by omega, add_pow]
          simp only [Nat.cast_id]
  calc (∑ j ∈ range (r + 1), ℓ.choose j) * a ^ ℓ
      = ∑ j ∈ range (r + 1), ℓ.choose j * a ^ ℓ := sum_mul _ _ _
    _ ≤ ∑ j ∈ range (r + 1), a ^ r * (1 ^ j * a ^ (ℓ - j) * ℓ.choose j) := sum_le_sum hterm
    _ = a ^ r * ∑ j ∈ range (r + 1), 1 ^ j * a ^ (ℓ - j) * ℓ.choose j := (mul_sum _ _ _).symm
    _ ≤ a ^ r * (a + 1) ^ ℓ := Nat.mul_le_mul_left _ htail

end Cslib
