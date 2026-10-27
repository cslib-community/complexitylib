import Complexity.Foundations.Data.Nat.Choose.Real

/-!
Concrete controls for the geometric binomial-tail budget. These include a positive radius, a
nonintegral real exponent, zero input/radius, and cases where an omitted premise would fail.
-/

open Finset Cslib

-- The accepted budget is 40 ≤ 64, the radius is one, and the tail counts 65 subsets:
-- one empty subset and 64 singletons.
example :
    (∑ j ∈ range (4 * 16 / 64 + 1), ((4 * 16).choose j : ℝ)) = 65 ∧
    (∑ j ∈ range (4 * 16 / 64 + 1), ((4 * 16).choose j : ℝ)) ≤ (2 : ℝ) ^ (16 : ℕ) := by
  constructor
  · norm_num [sum_range_succ]
  · simpa using sum_choose_le_two_rpow_div (C := 4) (Γ := 4) (M := 64) (B := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) 16

-- Odd input size and B = 2 exercise both real division and the natural rounded consumer bound.
example :
    (∑ j ∈ range (4 * 33 / 128 + 1), ((4 * 33).choose j : ℝ)) ≤ (2 : ℝ) ^ (33 / 2 : ℝ) ∧
    (∑ j ∈ range (4 * 33 / 128 + 1), (4 * 33).choose j) ≤ 2 ^ 17 := by
  constructor
  · exact sum_choose_le_two_rpow_div (C := 4) (Γ := 4) (M := 128) (B := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) 33
  · exact sum_choose_le_two_pow_div_add_one (C := 4) (Γ := 4) (M := 128) (B := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) 33

-- N = 0 has one empty subset, and its real upper bound is exactly one.
example : (∑ j ∈ range (4 * 0 / 64 + 1), ((4 * 0).choose j : ℝ)) ≤ 1 := by
  exact (sum_choose_le_two_rpow_div (C := 4) (Γ := 4) (M := 64) (B := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) 0).trans (by norm_num)

-- Positive input need not give positive radius: 4 * 15 / 64 = 0.
example :
    (∑ j ∈ range (4 * 15 / 64 + 1), ((4 * 15).choose j : ℝ)) = 1 ∧
    (∑ j ∈ range (4 * 15 / 64 + 1), (4 * 15).choose j) ≤ 2 ^ 16 := by
  constructor
  · norm_num
  · exact sum_choose_le_two_pow_div_add_one (C := 4) (Γ := 4) (M := 64) (B := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) 15

-- M ≥ Γ alone is insufficient: this rejected budget has a tail of 5, above 2^(N/B) = 2.
example : ¬ (1 * 4 * Nat.clog 2 (4 * 4 * 4) ≤ 4) ∧
    ¬ ((∑ j ∈ range (4 * 1 / 4 + 1), ((4 * 1).choose j : ℝ)) ≤ (2 : ℝ) ^ (1 / 1 : ℝ)) := by
  constructor
  · decide
  · norm_num [sum_range_succ]

-- Positivity of B matters even when the multiplied budget test itself holds.
example : 0 * 4 * Nat.clog 2 (4 * 4 * 64) ≤ 64 ∧
    ¬ ((∑ j ∈ range (4 * 16 / 64 + 1), ((4 * 16).choose j : ℝ)) ≤ (2 : ℝ) ^ (16 / 0 : ℝ)) := by
  constructor
  · decide
  · norm_num [sum_range_succ]
