/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.MassProduction.Fine
import Complexity.Computability.Circuit.Boolean.MassProduction.FineParameters

/-!
# Fine mass-production clients

These clients evaluate the parameter choices at concrete lengths, exercise the boundary of the
floor budget and the copy depth, and check the slack and suffix-fraction inequalities at concrete
values.
-/

namespace ComplexityTests.MassProduction.Fine

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.MassProduction
open Cslib.Circuits.Boolean.MassProduction.Fine Filter

/-! ### Parameters at rate `1 / 2` with slack `X = 32`, budget, and slack -/

example :
    -- Prefix fraction (den + num X) / ((X + 1) den) = 34 / 66.
    prefixWidth 1 2 32 1000 = 515 ∧
    suffixWidth 1 2 32 1000 = 485 ∧
    -- The suffix keeps 32 / 33 of the half of the input not taken by the copies.
    32 * (2 - 1) * 1000 ≤ (32 + 1) * 2 * suffixWidth 1 2 32 1000 ∧
    -- Dimension 4 (den + num X) + 3 = 139, and 139 ≤ 2 ^ 8.
    dimension 1 2 32 = 139 ∧ blockWidth 1 2 32 = 8 ∧
    -- At n = 1000 there are no complete blocks yet: the parameters are eventual.
    blocks 1 2 32 1000 = 0 ∧ fieldWidth 1 2 32 1000 = 0 ∧
    -- The batch exponent rounds γ n down and adds one.
    depth 1 2 1000 = 501 ∧ depth 1 2 1001 = 501 ∧ depth 0 7 1000 = 1 ∧
    rationalCopyBudget 2 3 5 = 8 ∧
    rationalCopyBudget 2 3 5 ≤ 2 ^ (2 * 5 / 3 + 1) ∧
    2 * 1 * ((16 * (1 + 1) + 1) ^ 2 * (16 * (1 + 1) + 2)) ≤
      (2 * 1 + 1) * (16 * (1 + 1)) ^ 3 ∧
    -- Rate zero, precision one, all four inputs in the suffix, single-copy cost 1, no overhead.
    1 * (1 - 0) * 4 * (1 * 1 + 0) ≤ (1 + 1) * 1 * 2 ^ 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    rationalCopyBudget_le_two_pow 5,
    two_mul_slack_le 1,
    mul_add_le_of_slack (P := 1) (p := 0) (w := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

-- Zero copies: the core budget always allows at least two copies, the floor budget one.
example (n : ℕ) : 2 ≤ 2 ^ (0 * n / 1 + 1) ∧ rationalCopyBudget 0 1 n = 1 := by
  simp [rationalCopyBudget]

/-! ### Corollaries and unconditional theorems -/

-- The corollaries require only the core bound at every rational exponent.
example (h : ∀ num den : ℕ, num < den → FineMassProducesThrough num den) :
    ExponentialMassProduction ∧ RealFineMassProduction ∧ FineMassProducesAt 1 2 :=
  ⟨exponentialMassProduction_of_fine h, realFineMassProduction_of_fine h,
    (h 1 2 (by decide)).fineMassProducesAt⟩

-- Concrete instances of `exists_rat_coefficient`, `fineMassProducesThrough` at `1 / 2` and `0 / 1`,
-- `exponentialMassProduction` at `9 / 10`, and `realFineMassProduction` at `γ = 0.99`.
example (precision : ℕ) :
    (∃ num den P : ℕ, num < den ∧ 0 < P ∧ (1 / 2 : ℝ) < (num : ℝ) / den ∧
      ((P : ℝ) + 1) * den ≤ (1 / (1 - 1 / 2) + 1 / 10) * P * ((den - num : ℕ) : ℝ)) ∧
    (∀ᶠ n in atTop, ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), k ≤ 2 ^ (1 * n / 2 + 1) →
      ((4 * (2 - 1) * n : ℕ) : ℕ∞) * massComplexity f k ≤ ((4 + 1) * 2 * 2 ^ n : ℕ)) ∧
    -- At rate zero and positive precision, a constant number of copies costs
    -- (1 + 1/precision) 2 ^ n / n,
    -- recovering Lupanov's coefficient as precision increases.
    (∀ᶠ n in atTop, ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), k ≤ 2 ^ (0 * n / 1 + 1) →
      ((precision * (1 - 0) * n : ℕ) : ℕ∞) * massComplexity f k ≤
        ((precision + 1) * 1 * 2 ^ n : ℕ)) ∧
    MassProducesAtAllLengths 9 10 ∧
    ∃ cutoff : ℕ, ∀ n, cutoff ≤ n → ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), 0 < k →
      (k : ℝ) ≤ (2 : ℝ) ^ ((99 / 100 : ℝ) * n) → ∃ bound : ℕ, massComplexity f k ≤ bound ∧
        (bound : ℝ) ≤ (1 / (1 - 99 / 100) + 1) * ((2 : ℝ) ^ n / n) :=
  ⟨exists_rat_coefficient (by norm_num) (by norm_num) (by norm_num),
    fineMassProducesThrough (num := 1) (den := 2) (by decide) 4,
    fineMassProducesThrough (num := 0) (den := 1) (by decide) precision,
    exponentialMassProduction 9 10 (by decide) (by decide),
    realFineMassProduction _ (by norm_num) (by norm_num) 1 (by norm_num)⟩

end ComplexityTests.MassProduction.Fine
