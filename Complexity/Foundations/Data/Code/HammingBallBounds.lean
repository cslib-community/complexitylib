/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Elementary binary Hamming-ball bounds

Weighted binomial estimates for finite Hamming balls. These proofs by Samuel
Schlesinger are moved from `Code.Justesen` without changing their statements or
proofs; the small-radius bound is now public so that finite code existence can
reuse it without assuming finite fields or concatenated codes.
-/

public section

namespace Cslib.Code

open Finset

/-- **A binomial estimate** for the size of a Hamming ball: `V * 4 ^ ℓ ≤ 4 ^ r * 5 ^ ℓ` for
`V = ∑_{j ≤ r} C(ℓ, j)`, since `5 ^ ℓ = ∑_j C(ℓ, j) * 4 ^ (ℓ - j)`. -/
theorem sum_range_choose_mul_four_pow_le (ℓ r : ℕ) :
    (∑ j ∈ range (r + 1), ℓ.choose j) * 4 ^ ℓ ≤ 4 ^ r * 5 ^ ℓ := by
  have hterm : ∀ j ∈ range (r + 1),
      ℓ.choose j * 4 ^ ℓ ≤ 4 ^ r * (1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j) := by
    intro j hj
    rcases lt_or_ge ℓ j with hℓj | hjℓ
    · rw [Nat.choose_eq_zero_of_lt hℓj, zero_mul]
      exact Nat.zero_le _
    have hjr := Nat.lt_succ_iff.1 (mem_range.1 hj)
    calc ℓ.choose j * 4 ^ ℓ = ℓ.choose j * (4 ^ j * 4 ^ (ℓ - j)) := by
          rw [← pow_add, Nat.add_sub_cancel' hjℓ]
      _ ≤ ℓ.choose j * (4 ^ r * 4 ^ (ℓ - j)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hjr))
      _ = 4 ^ r * (1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j) := by ring
  -- the binomial expansion of `5 ^ ℓ`, whose terms beyond `ℓ` vanish
  have htail : ∑ j ∈ range (r + 1), 1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j ≤ 5 ^ ℓ := by
    calc ∑ j ∈ range (r + 1), 1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j
        ≤ ∑ j ∈ range (ℓ + 1 + (r + 1)), 1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j :=
          sum_le_sum_of_subset (range_subset_range.2 (by omega))
      _ = 5 ^ ℓ := by
          have h0 : ∑ j ∈ range (r + 1), 1 ^ (ℓ + 1 + j) * 4 ^ (ℓ - (ℓ + 1 + j)) *
              ℓ.choose (ℓ + 1 + j) = 0 :=
            sum_eq_zero fun j _ => by rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
          rw [sum_range_add, h0, add_zero, show (5 : ℕ) = 1 + 4 by rfl, add_pow]
          simp only [Nat.cast_id]
  calc (∑ j ∈ range (r + 1), ℓ.choose j) * 4 ^ ℓ
      = ∑ j ∈ range (r + 1), ℓ.choose j * 4 ^ ℓ := sum_mul _ _ _
    _ ≤ ∑ j ∈ range (r + 1), 4 ^ r * (1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j) := sum_le_sum hterm
    _ = 4 ^ r * ∑ j ∈ range (r + 1), 1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j := (mul_sum _ _ _).symm
    _ ≤ 4 ^ r * 5 ^ ℓ := Nat.mul_le_mul_left _ htail

/-- For `s ≥ 1`, the Hamming ball of radius `s` in `32 s` bits has at most `2 ^ (16 s - 2)`
words. -/
theorem sum_range_choose_two_mul_sixteen_mul_le {s : ℕ} (hs : 1 ≤ s) :
    ∑ j ∈ range (s + 1), (2 * (16 * s)).choose j ≤ 2 ^ (16 * s - 2) := by
  have h := sum_range_choose_mul_four_pow_le (2 * (16 * s)) s
  have hconst : 4 * (4 * 5 ^ 32) ≤ 2 ^ 80 := by norm_num
  have hlhs : 4 * (4 ^ s * 5 ^ (2 * (16 * s))) ≤ 2 ^ (80 * s) := by
    calc 4 * (4 ^ s * 5 ^ (2 * (16 * s))) ≤ 4 ^ s * (4 ^ s * 5 ^ (2 * (16 * s))) :=
          Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 4)
      _ = (4 * (4 * 5 ^ 32)) ^ s := by
          rw [show 2 * (16 * s) = 32 * s by ring, pow_mul, mul_pow, mul_pow]
      _ ≤ (2 ^ 80) ^ s := Nat.pow_le_pow_left hconst s
      _ = 2 ^ (80 * s) := (pow_mul _ _ _).symm
  have h4 : 4 ^ (2 * (16 * s)) * 2 ^ (16 * s - 2) * 4 = 2 ^ (80 * s) := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, mul_assoc, ← pow_add, ← pow_add]
    congr 1
    omega
  have h4pos : 0 < 4 ^ (2 * (16 * s)) := by positivity
  nlinarith

end Cslib.Code
