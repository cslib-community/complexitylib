/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Choose.Sum
import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Elementary binary Hamming-ball bounds

Weighted binomial estimates for finite Hamming balls, moved from `Code.Justesen` without
changing their statements; the small-radius bound is now public so that finite code existence
can reuse it without assuming finite fields or concatenated codes.
-/

public section

namespace Cslib.Code

open Finset

/-- **A binomial estimate** for the size of a Hamming ball: `V * 4 ^ ℓ ≤ 4 ^ r * 5 ^ ℓ` for
`V = ∑_{j ≤ r} C(ℓ, j)`, derived from `Cslib.sum_range_choose_mul_pow_le`. -/
theorem sum_range_choose_mul_four_pow_le (ℓ r : ℕ) :
    (∑ j ∈ range (r + 1), ℓ.choose j) * 4 ^ ℓ ≤ 4 ^ r * 5 ^ ℓ :=
  sum_range_choose_mul_pow_le 4 ℓ r

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
