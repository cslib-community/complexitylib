/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevOddErrors

/-! Checked examples for Lemma 6 and the truncated subcube vote (issue #4640, Milestone 2). -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold Finset

-- Hoeffding's inequality for weighted bit sums, on three bits with weights `2, -1, 1`.
example :
    (#{x : Fin 3 → Bool | (1 : ℝ) ≤
        |∑ i, ![2, -1, 1] i * (((x i).toNat : ℝ) - 1 / 2)|} : ℝ) ≤
      2 * 2 ^ 3 * Real.exp (-(2 * 1 ^ 2 / ∑ i, (![2, -1, 1] i : ℝ) ^ 2)) := by
  simpa using BitString.card_filter_le_abs_sum_mul_sub_half_le (![2, -1, 1] : Fin 3 → ℝ)
    (t := 1) (by norm_num)

-- The discrete Gaussian tail sum, for `c = 8`.
example (K : ℕ) :
    ∑ j ∈ Ioc 2 K, (2 * (j : ℝ) - 1) * Real.exp (-((j : ℝ) ^ 2 / 8)) ≤
      8 * Real.exp (-((2 : ℕ) : ℝ) ^ 2 / 8) := by
  simpa [neg_div] using sum_Ioc_two_mul_sub_one_mul_exp_le (by norm_num : (0 : ℝ) < 8) 2 K

-- Lemma 6 with `g(x) = x ^ 3` (odd) and `h(x) = x ^ 2`, for `k = 2` blocks of `m = 2` bits.
example :
    ∑ w : BitString (2 ^ 2 + 2 * 2),
      (andreevTableScore 2 2 {0} w : ℝ) ^ 3 * (andreevTableScore 2 2 {0, 1} w : ℝ) ^ 2 = 0 :=
  sum_mul_andreevTableScore_eq_zero_of_odd (by decide) (fun x => (x : ℝ) ^ 3)
    (fun x => (x : ℝ) ^ 2) fun x => by push_cast; ring

-- The truncated vote at `k = 2, m = 2, r = 1` with radius `R = 1` on two concrete inputs: table
-- `0110` with address parities `(1, 0)` (selected bit `x₁ = 1`) and table `0000`.
example :
    andreevTruncatedVote 2 2 1 1 (fun i => decide (i = 1 ∨ i = 2 ∨ i = 4)) = true ∧
      andreevTruncatedVote 2 2 1 1 (fun i => decide (i = 4)) = false := by
  decide

-- The truncation errors at `k = 2, m = 2, r = 2` are orthogonal, and the vote with radius
-- `R = andreevTruncationRadius 2 2 2 (1 / 4)` agrees with Andreev's function on at least
-- `3 / 4` of the inputs.
example :
    ∑ w : BitString (2 ^ 2 + 2 * 2),
        (andreevTruncationError 2 2 1 {0} w : ℝ) * andreevTruncationError 2 2 1 {1} w = 0 ∧
      (#{w : BitString (2 ^ 2 + 2 * 2) |
        andreevTruncatedVote 2 2 2 (andreevTruncationRadius 2 2 2 (1 / 4)) w ≠
          Boolean.andreev 2 2 w} : ℝ) ≤ 1 / 4 * 2 ^ (2 ^ 2 + 2 * 2) :=
  ⟨sum_andreevTruncationError_mul_eq_zero (by decide),
    card_andreevTruncatedVote_ne_andreev_le_of_radius 2 2 (by norm_num)⟩

-- Part 2 at the level of the vote: `k = 3`, `q = 2 ^ 2`, `ε = 1 / 8` (`32 ε² N = 4 ≤ q`).
example (m : ℕ) :
    (1 / 2 + 1 / 8) * 2 ^ (2 ^ 3 + 3 * m) ≤
      (#{w : BitString (2 ^ 3 + 3 * m) |
        andreevTruncatedVote 3 m 2 (andreevTruncationRadius 3 m 2 (1 / 8)) w =
          Boolean.andreev 3 m w} : ℝ) :=
  half_add_mul_le_card_andreevTruncatedVote_eq_andreev (by decide) m (by norm_num) (by norm_num)
