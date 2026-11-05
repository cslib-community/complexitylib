/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Geometric sums about a natural offset

Finite sets of bins have a uniform two-sided geometric bound about any natural
center. The bound counts the center twice and has no horizon or cardinality cost.
-/

public section
noncomputable section
open Finset
open scoped BigOperators
namespace Cslib

/-- Two finite sides of a geometric series cost no factor for the number of bins.
The boundary may be counted twice in this conservative bound. -/
theorem sum_pow_offset_le (S : Finset ℕ) (a : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    ∑ i ∈ S, q ^ (a - i + (i - a)) ≤ 2 / (1 - q) := by
  classical
  let L := S.filter (· ≤ a)
  let R := S.filter (fun i => ¬ i ≤ a)
  have hside (T : Finset ℕ) (f : ℕ → ℕ) (hf : Set.InjOn f T) :
      ∑ i ∈ T, q ^ f i ≤ 1 / (1 - q) := by
    rw [← sum_image hf]
    have hh := sum_le_sum_of_subset_of_nonneg
      (show T.image f ⊆ range (T.sup f + 1) from by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
        exact mem_range.mpr (Nat.lt_succ_of_le (le_sup hi)))
      (fun i _ _ => pow_nonneg hq i)
    apply hh.trans
    simpa only [Nat.add_zero, pow_zero, Nat.Ico_zero_eq_range] using
      geom_sum_Ico_le_of_lt_one (m := 0) (n := T.sup f + 1) hq hq1
  have hL : ∑ i ∈ L, q ^ (a - i + (i - a)) ≤ 1 / (1 - q) := by
    have hh := hside L (fun i => a - i) (by
      intro i hi j hj he
      have hi' := (mem_filter.mp hi).2
      have hj' := (mem_filter.mp hj).2
      dsimp only at he
      omega)
    convert hh using 1
    apply sum_congr rfl
    intro i hi
    rw [Nat.sub_eq_zero_of_le (mem_filter.mp hi).2, Nat.add_zero]
  have hR : ∑ i ∈ R, q ^ (a - i + (i - a)) ≤ 1 / (1 - q) := by
    have hh := hside R (fun i => i - a) (by
      intro i hi j hj he
      have hi' := (mem_filter.mp hi).2
      have hj' := (mem_filter.mp hj).2
      dsimp only at he
      omega)
    convert hh using 1
    apply sum_congr rfl
    intro i hi
    rw [Nat.sub_eq_zero_of_le (by have := (mem_filter.mp hi).2; omega), Nat.zero_add]
  have hh := add_le_add hL hR
  rw [show L = S.filter (· ≤ a) from rfl, show R = S.filter (fun i => ¬ i ≤ a) from rfl,
    sum_filter_add_sum_filter_not] at hh
  convert hh using 1; ring

/-- Fourth-root fine/coarse offset decay is summable uniformly over finite horizons. -/
theorem sum_two_rpow_offset_le (S : Finset ℕ) (a : ℕ) :
    ∑ i ∈ S, (2 : ℝ) ^ (-3 * |(i : ℝ) - a| / 4) ≤
      2 / (1 - (2 : ℝ) ^ (-3 / 4 : ℝ)) := by
  have hh := sum_pow_offset_le S a
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-3 / 4 : ℝ))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (-3 / 4 : ℝ) < 0))
  convert hh using 1
  apply sum_congr rfl
  intro i _
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  by_cases hi : i ≤ a
  · have hir : (i : ℝ) ≤ a := by exact_mod_cast hi
    rw [abs_of_nonpos (sub_nonpos.mpr hir), Nat.sub_eq_zero_of_le hi,
      Nat.add_zero, Nat.cast_sub hi]
    ring
  · have hn : a ≤ i := by omega
    have hir : (a : ℝ) ≤ i := by exact_mod_cast hn
    rw [abs_of_nonneg (sub_nonneg.mpr hir), Nat.sub_eq_zero_of_le hn,
      Nat.zero_add, Nat.cast_sub hn]
    ring

end Cslib
