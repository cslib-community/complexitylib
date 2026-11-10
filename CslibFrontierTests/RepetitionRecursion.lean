/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PCP.ParallelRepetition.Recursion

/-! # The recursion of the parallel repetition theorem

The sequence `p_m = v^m` (independent play of an optimal strategy) satisfies the hypotheses of
Holenstein's recursion, so the conclusion applies to it. The exact bound `le_rpow_of_step` applies
with the constant `C = 27 / √2` that the library's Corollary 5.3 leads to.
-/

namespace CslibFrontierTests.RepetitionRecursion

open Cslib.PCP.ParallelRepetition

example {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    v ^ n ≤ ((1 + v) / 2) ^ ⌊(1 - v) ^ 2 * n / (13 * 15 ^ 2 * 1)⌋₊ :=
  le_pow_floor_of_step (C := 15) (L := 1) (p := fun m => v ^ m) hv hv1 (by norm_num) le_rfl
    (pow_zero v) (fun m => pow_nonneg hv m) (fun m => by
      simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg hv m) hv1)
    fun m _ => by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (pow_nonneg hv m)

-- The exponential form, for the same sequence.
example {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    v ^ n ≤ 2 * (1 - (1 - v) ^ 3 / (26 * 15 ^ 2)) ^ ((n : ℝ) / 1) :=
  le_two_mul_rpow_of_step (C := 15) (L := 1) (p := fun m => v ^ m) hv hv1 (by norm_num) le_rfl
    (pow_zero v) (fun m => pow_nonneg hv m) (fun m => by
      simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg hv m) hv1)
    fun m _ => by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (pow_nonneg hv m)

/-- `27 / √2 ≤ 21`, so `le_rpow_of_step` covers this constant. -/
private theorem twenty_seven_div_sqrt_two_le : 27 / Real.sqrt 2 ≤ 21 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

-- The exact bound of Theorem 2.5 for any sequence satisfying the step with `C = 27 / √2`.
example {v L : ℝ} {n : ℕ} {p : ℕ → ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) (hL : 1 ≤ L) (hp0 : p 0 = 1)
    (hnn : ∀ m, 0 ≤ p m) (hmono : ∀ m, p (m + 1) ≤ p m)
    (hstep : ∀ m < n, p (m + 1) ≤
      p m * (v + 27 / Real.sqrt 2 * Real.sqrt ((m * L + Real.log (1 / p m)) / (n - m)))) :
    p n ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / L) :=
  le_rpow_of_step hv hv1 (by positivity) twenty_seven_div_sqrt_two_le hL hp0 hnn hmono hstep

-- The exact bound for the concrete sequence `v^m`, with `C = 27 / √2` and `L = 2`.
example {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    v ^ n ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / 2) :=
  le_rpow_of_step (C := 27 / Real.sqrt 2) (L := 2) (p := fun m => v ^ m) hv hv1 (by positivity)
    twenty_seven_div_sqrt_two_le one_le_two (pow_zero v) (fun m => pow_nonneg hv m)
    (fun m => by simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg hv m) hv1)
    fun m _ => by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (pow_nonneg hv m)

end CslibFrontierTests.RepetitionRecursion
