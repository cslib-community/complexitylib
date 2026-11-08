/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.ExactTriangle.ParameterChoice
public import CslibFrontier.Algorithms.ExactTriangle.Splitting
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite cost geometry of the integer box parameters

The nineteen-factor reservation gives the common `n^3/g` scale for actual preparation,
products, query/root control and scans. Group rounding supplies raw saving `2/1197`;
logarithmic factors remain to be absorbed by the complete native caller.
-/

public section

namespace Cslib.Algorithms.ExactTriangle.ParameterChoice

/-- Preparation's extra window and two group factors fit within nineteen reserved factors. -/
theorem window_mul_groups_sq_le {n : ℕ} (hn : 0 < n) :
    window n * groups n ^ 2 ≤ n := by
  have hg2 : groups n ^ 2 ≤ window n := by
    simp only [groups, window, level, ← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hd1 : 1 ≤ window n := window_pos n
  calc
    _ ≤ window n * window n := Nat.mul_le_mul_left _ hg2
    _ = window n ^ 2 := by ring
    _ ≤ window n ^ 19 := Nat.pow_le_pow_right hd1 (by decide : 2 ≤ 19)
    _ ≤ n := geometry_nineteen hn

/-- The group-square bound for query control does not assume an exact square-root power. -/
theorem groups_sq_le_sqrt (n : ℕ) : (groups n : ℝ) ^ 2 ≤ Real.sqrt (window n : ℝ) := by
  have hnat : (groups n ^ 2) ^ 2 ≤ window n := by
    simp only [groups, window, level, ← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have h := (Nat.cast_le (α := ℝ)).mpr hnat
  push_cast at h
  exact (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr h

/-- Two group factors fit in the actual finite box product's fractional window saving. -/
theorem groups_sq_le_window_rpow (n : ℕ) :
    (groups n : ℝ) ^ 2 ≤ (window n : ℝ) ^ (8 / 125 : ℝ) := by
  have hnat : (groups n ^ 2) ^ 125 ≤ window n ^ 8 := by
    simp only [groups, window, level, ← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have h := (Nat.cast_le (α := ℝ)).mpr hnat
  push_cast at h
  have hr := Real.rpow_le_rpow (by positivity) h (show (0 : ℝ) ≤ 1 / 125 by norm_num)
  have hl := Real.pow_rpow_inv_natCast (x := (groups n : ℝ) ^ 2) (n := 125)
    (by positivity) (by decide)
  norm_num only [Nat.cast_ofNat] at hl
  simp only [one_div] at hl hr
  rw [hl] at hr
  have he : ((window n : ℝ) ^ 8) ^ (1 / 125 : ℝ) =
      (window n : ℝ) ^ (8 / 125 : ℝ) := by
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  simpa only [one_div] using hr.trans_eq (by simpa only [one_div] using he)

/-- The rounded group count gains an inverse input power with only a factor16 loss. -/
theorem rpow_lt_sixteen_mul_groups (n : ℕ) :
    (n : ℝ) ^ (2 / 1197 : ℝ) < 16 * groups n := by
  have h := (Nat.cast_lt (α := ℝ)).mpr (size_sq_lt_groups_pow n)
  push_cast at h
  have hp := Real.rpow_lt_rpow (by positivity) h (show (0 : ℝ) < 1 / 1197 by norm_num)
  have he := Real.pow_rpow_inv_natCast (x := 16 * (groups n : ℝ)) (n := 1197)
    (by positivity) (by decide)
  norm_num only [Nat.cast_ofNat] at he
  simp only [one_div] at he hp
  rw [he] at hp
  have hl : ((n : ℝ) ^ 2) ^ (1 / 1197 : ℝ) = (n : ℝ) ^ (2 / 1197 : ℝ) := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
    norm_num
  simpa only [one_div, ← hl] using hp

/-- The original nineteen-factor reserve controls every nonnegative real window power. -/
theorem window_rpow_le_rpow {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    (window n : ℝ) ^ r ≤ (n : ℝ) ^ (r / 19) := by
  have h := (Nat.cast_le (α := ℝ)).mpr (geometry_nineteen hn)
  push_cast at h
  calc
    _ = ((window n : ℝ) ^ 19) ^ (r / 19) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by positivity)

/-- Explicit raw saving before logarithmic factors are absorbed. -/
theorem cubic_div_groups_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 3 / groups n ≤ 16 * (n : ℝ) ^ (3 - 2 / 1197 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hg0 : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  have hr := (rpow_lt_sixteen_mul_groups n).le
  have hpow : (n : ℝ) ^ (3 - 2 / 1197 : ℝ) * (n : ℝ) ^ (2 / 1197 : ℝ) =
      (n : ℝ) ^ 3 := by
    rw [← Real.rpow_add hn0]
    norm_num
  apply (div_le_iff₀ hg0).mpr
  have h := mul_le_mul_of_nonneg_left hr
    (show (0 : ℝ) ≤ (n : ℝ) ^ (3 - 2 / 1197 : ℝ) by positivity)
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
  have hs : (0 : ℝ) < Real.sqrt (window n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast window_pos n)
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

/-- Product saving converts the additional group multiplier into one inverse group factor. -/
theorem product_work_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 3 * groups n * (window n : ℝ) ^ (-(8 / 125 : ℝ)) ≤
      (n : ℝ) ^ 3 / groups n := by
  have hg : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  have hd : (0 : ℝ) < (window n : ℝ) ^ (8 / 125 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast window_pos n) _
  have hratio : (groups n : ℝ) / (window n : ℝ) ^ (8 / 125 : ℝ) ≤ 1 / groups n := by
    apply (div_le_div_iff₀ hd hg).mpr
    have h := groups_sq_le_window_rpow n
    nlinarith only [h]
  calc
    _ = (n : ℝ) ^ 3 * ((groups n : ℝ) / (window n : ℝ) ^ (8 / 125 : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
      ring
    _ ≤ (n : ℝ) ^ 3 * (1 / groups n) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end Cslib.Algorithms.ExactTriangle.ParameterChoice
