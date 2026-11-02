/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.ParameterChoice
public import Complexity.Algorithms.ExactTriangle.Splitting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cost geometry of the computed dyadic parameters

Exact powers connect the conservative native parameter family to preparation, query and
thin-product costs. These are original arithmetic bounds, not an execution theorem or the
source's tuned exponent. The group-growth estimate includes the loss from integer rounding.

## Main results

* `rpow_window`: exact thin-product denominator at the computed balance.
* `preparation_le`, `root_work_le`, `query_work_le`: common cubic-over-groups cost scale.
* `cubic_div_groups_le`: the explicit real-power saving, before logarithmic factors.
-/

public section

namespace Cslib.Algorithms.ExactTriangle.ParameterChoice

/-- The actual fast-branch condition excludes the empty input. -/
theorem pos_of_blocks_pos {n : ℕ} (hf : 0 < blocks n) : 0 < n :=
  lt_of_lt_of_le (Nat.two_pow_pos 1296) ((blocks_pos_iff n).mp hf)

/-- The group parameter is at least one, including the small-input branch. -/
theorem one_le_groups (n : ℕ) : 1 ≤ groups n := groups_pos n

/-- The geometry reserve in group coordinates. -/
theorem groups_pow_le {n : ℕ} (hn : 0 < n) : groups n ^ 648 ≤ n := by
  have h := geometry hn
  rw [← groups_pow, ← pow_mul] at h
  norm_num only [Nat.reduceMul] at h
  exact h

/-- The exact integer square root of the chosen window. -/
theorem sqrt_window (n : ℕ) : Nat.sqrt (window n) = groups n ^ 18 := by
  rw [← groups_pow]
  have he : groups n ^ 36 = (groups n ^ 18) ^ 2 := by rw [← pow_mul]
  rw [he, Nat.sqrt_eq']

/-- The real square root agrees with the same exact power. -/
theorem real_sqrt_window (n : ℕ) : Real.sqrt (window n : ℝ) = (groups n : ℝ) ^ 18 := by
  rw [← groups_pow, Nat.cast_pow]
  have he : (groups n : ℝ) ^ 36 = ((groups n : ℝ) ^ 18) ^ 2 := by ring
  rw [he, Real.sqrt_sq (by positivity)]

/-- The actual thin-product denominator is exactly the square of the group count. -/
theorem rpow_window (n : ℕ) : (window n : ℝ) ^ (1 / 18 : ℝ) = (groups n : ℝ) ^ 2 := by
  rw [← groups_pow, Nat.cast_pow]
  have he : (groups n : ℝ) ^ 36 = ((groups n : ℝ) ^ 2) ^ 18 := by ring
  rw [he]
  simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast
    (x := (groups n : ℝ) ^ 2) (n := 18) (sq_nonneg _) (by decide)

/-- Preparation's extra dimension and two group factors fit in the original dimension. -/
theorem window_mul_groups_sq_le {n : ℕ} (hn : 0 < n) :
    window n * groups n ^ 2 ≤ n := by
  have hg2 : groups n ^ 2 ≤ window n := by
    rw [← groups_pow]
    exact Nat.pow_le_pow_right (one_le_groups n) (by decide : 2 ≤ 36)
  have hd1 : 1 ≤ window n := Nat.one_le_pow _ _ (by decide)
  calc
    _ ≤ window n * window n := Nat.mul_le_mul_left _ hg2
    _ = window n ^ 2 := by ring
    _ ≤ window n ^ 18 := Nat.pow_le_pow_right hd1 (by decide : 2 ≤ 18)
    _ ≤ n := geometry hn

/-- Two group factors fit under the real square root. -/
theorem groups_sq_le_sqrt (n : ℕ) : (groups n : ℝ) ^ 2 ≤ Real.sqrt (window n : ℝ) := by
  rw [real_sqrt_window]
  exact pow_le_pow_right₀ (by exact_mod_cast one_le_groups n) (by decide : 2 ≤ 18)

private theorem cast_growth {a b k : ℕ} (h : a < b ^ k) : (a : ℝ) < (b : ℝ) ^ k := by
  exact_mod_cast h

-- The fixed reserve exponent is 648; allow its numeral coercion in this local calculation.
set_option exponentiation.threshold 648 in
/-- Real growth survives rounding down the block count, with only a factor four loss. -/
theorem rpow_lt_four_mul_groups (n : ℕ) :
    (n : ℝ) ^ (1 / 648 : ℝ) < 4 * groups n := by
  have h := cast_growth (a := n) (b := 4 * groups n) (k := 648) (size_lt_groups_pow n)
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  have hp := Real.rpow_lt_rpow (Nat.cast_nonneg n) h (by norm_num : (0 : ℝ) < 1 / 648)
  have he := Real.pow_rpow_inv_natCast (x := 4 * (groups n : ℝ)) (n := 648)
    (by positivity) (by decide)
  norm_num only [Nat.cast_ofNat] at he
  simp only [one_div] at he hp
  rw [he] at hp
  simpa only [one_div] using hp

-- Only the fixed geometric reserve exponent is evaluated in the cast calculation.
set_option exponentiation.threshold 648 in
/-- Every nonnegative group power is bounded by the corresponding fractional input power. -/
theorem groups_pow_le_rpow {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (groups n : ℝ) ^ k ≤ (n : ℝ) ^ ((k : ℝ) / 648) := by
  have h : (groups n : ℝ) ^ 648 ≤ n := by
    exact_mod_cast groups_pow_le (n := n) hn
  calc
    _ = ((groups n : ℝ) ^ 648) ^ ((k : ℝ) / 648) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      norm_num only [Nat.cast_ofNat]
      rw [mul_div_cancel₀ _ (by norm_num : (648 : ℝ) ≠ 0), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by positivity)

/-- Explicit positive-power saving from the computed integer group count. Logarithmic cost
factors have not been absorbed into this exponent. -/
theorem cubic_div_groups_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 3 / groups n ≤ 4 * (n : ℝ) ^ (3 - 1 / 648 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hg0 : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  have hr := (rpow_lt_four_mul_groups n).le
  have hpow : (n : ℝ) ^ (3 - 1 / 648 : ℝ) * (n : ℝ) ^ (1 / 648 : ℝ) =
      (n : ℝ) ^ 3 := by
    rw [← Real.rpow_add hn0]
    norm_num
  apply (div_le_iff₀ hg0).mpr
  have h := mul_le_mul_of_nonneg_left hr
    (show (0 : ℝ) ≤ (n : ℝ) ^ (3 - 1 / 648 : ℝ) by positivity)
  rw [hpow] at h
  nlinarith only [h]

/-- The one-time preparation term gains one inverse group factor. -/
theorem preparation_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 * window n * groups n ≤ (n : ℝ) ^ 3 / groups n := by
  have hg : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  have hscale : (window n : ℝ) * (groups n : ℝ) ^ 2 ≤ n := by
    exact_mod_cast window_mul_groups_sq_le hn
  apply (le_div_iff₀ hg).mpr
  calc
    _ = (n : ℝ) ^ 2 * ((window n : ℝ) * (groups n : ℝ) ^ 2) := by ring
    _ ≤ (n : ℝ) ^ 2 * n := mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
    _ = _ := by ring

/-- Constant work per group fits the same common cost scale. -/
theorem group_work_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * groups n ≤ (n : ℝ) ^ 3 / groups n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ window n := by
    exact_mod_cast (Nat.one_le_pow _ _ (by decide : 1 ≤ (4 : ℕ)) : 1 ≤ window n)
  calc
    _ ≤ (n : ℝ) ^ 2 * window n * groups n := by
      gcongr
      exact (le_self_pow₀ hn1 (by decide : 2 ≠ 0)).trans
        (le_mul_of_one_le_right (sq_nonneg _) hd1)
    _ ≤ _ := preparation_le hn

/-- Root setup per group also fits the common scale. -/
theorem root_work_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * groups n * Nat.sqrt (window n) ≤ (n : ℝ) ^ 3 / groups n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (Nat.sqrt (window n) : ℝ) ≤ window n := by
    exact_mod_cast Nat.sqrt_le_self (window n)
  calc
    _ = (n : ℝ) * (Nat.sqrt (window n) : ℝ) * groups n := by ring
    _ ≤ (n : ℝ) ^ 2 * window n * groups n := by
      gcongr
      exact le_self_pow₀ hn1 (by decide : 2 ≠ 0)
    _ ≤ _ := preparation_le hn

/-- The actual integer query capacity yields the same saving, without dropping rounding. -/
theorem query_work_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * groups n * queryCap n (window n) ≤ (n : ℝ) ^ 3 / groups n := by
  have hg : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  have hs : (0 : ℝ) < Real.sqrt (window n : ℝ) := by rw [real_sqrt_window]; positivity
  have hQ : (queryCap n (window n) : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt (window n) := by
    rw [queryCap_eq_floor]
    exact Nat.floor_le (by positivity)
  calc
    _ ≤ (n : ℝ) * groups n * ((n : ℝ) ^ 2 / Real.sqrt (window n)) := by gcongr
    _ = (n : ℝ) ^ 3 * ((groups n : ℝ) / Real.sqrt (window n)) := by ring
    _ ≤ (n : ℝ) ^ 3 * (1 / groups n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_div_iff₀ hs hg).mpr
      nlinarith only [groups_sq_le_sqrt n]
    _ = _ := by ring

end Cslib.Algorithms.ExactTriangle.ParameterChoice
