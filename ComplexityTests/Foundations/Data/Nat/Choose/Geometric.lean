import Complexity.Foundations.Data.Nat.Choose.Real

/-!
Concrete controls for the geometric binomial-tail budget. These include a positive radius, a
nonintegral real exponent, zero input/radius, and cases where an omitted premise would fail.
-/

open Finset Cslib

-- The accepted budget is 40 ≤ 64, the radius is one, and the tail counts 65 subsets:
-- one empty subset and 64 singletons. Odd input size and B = 2 exercise both real division
-- and the natural rounded consumer bound; N = 0 and 4 * 15 / 64 = 0 exercise zero radius.
example :
    (∑ j ∈ range (4 * 16 / 64 + 1), ((4 * 16).choose j : ℝ)) = 65 ∧
    (∑ j ∈ range (4 * 16 / 64 + 1), ((4 * 16).choose j : ℝ)) ≤ (2 : ℝ) ^ (16 : ℕ) ∧
    (∑ j ∈ range (4 * 33 / 128 + 1), ((4 * 33).choose j : ℝ)) ≤ (2 : ℝ) ^ (33 / 2 : ℝ) ∧
    (∑ j ∈ range (4 * 33 / 128 + 1), (4 * 33).choose j) ≤ 2 ^ 17 ∧
    (∑ j ∈ range (4 * 0 / 64 + 1), ((4 * 0).choose j : ℝ)) ≤ 1 ∧
    (∑ j ∈ range (4 * 15 / 64 + 1), ((4 * 15).choose j : ℝ)) = 1 ∧
    (∑ j ∈ range (4 * 15 / 64 + 1), (4 * 15).choose j) ≤ 2 ^ 16 := by
  refine ⟨by norm_num [sum_range_succ], ?_,
    sum_choose_le_two_rpow_div (C := 4) (Γ := 4) (M := 128) (B := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) 33,
    sum_choose_le_two_pow_div_add_one (C := 4) (Γ := 4) (M := 128) (B := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) 33,
    (sum_choose_le_two_rpow_div (C := 4) (Γ := 4) (M := 64) (B := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) 0).trans (by norm_num),
    by norm_num,
    sum_choose_le_two_pow_div_add_one (C := 4) (Γ := 4) (M := 64) (B := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) 15⟩
  simpa using sum_choose_le_two_rpow_div (C := 4) (Γ := 4) (M := 64) (B := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) 16

-- M ≥ Γ alone is insufficient (tail 5 > 2^(1/1)), and positivity of B matters even when the
-- multiplied budget test itself holds.
example :
    ¬ (1 * 4 * Nat.clog 2 (4 * 4 * 4) ≤ 4) ∧
    ¬ ((∑ j ∈ range (4 * 1 / 4 + 1), ((4 * 1).choose j : ℝ)) ≤ (2 : ℝ) ^ (1 / 1 : ℝ)) ∧
    0 * 4 * Nat.clog 2 (4 * 4 * 64) ≤ 64 ∧
    ¬ ((∑ j ∈ range (4 * 16 / 64 + 1), ((4 * 16).choose j : ℝ)) ≤ (2 : ℝ) ^ (16 / 0 : ℝ)) := by
  refine ⟨by decide, by norm_num [sum_range_succ], by decide, by norm_num [sum_range_succ]⟩
