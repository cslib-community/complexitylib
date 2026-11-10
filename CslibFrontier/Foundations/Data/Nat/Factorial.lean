/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (cslib, addition to Cslib/Foundations/Data/Nat/Factorial.lean)

public import CslibFrontier.Init
public import Cslib.Foundations.Data.Nat.Factorial
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Factorial estimates

Elementary bounds comparing factorials and powers.

## Main results

* `Nat.pow_self_le_three_pow_mul_factorial`: `n ^ n ≤ 3 ^ n * n!`.
-/

@[expose] public section

namespace Nat

/-- Elementary factorial estimate: `n ^ n ≤ 3 ^ n * n!`, from `n ^ n / n! ≤ exp n` and `e < 3`. -/
theorem pow_self_le_three_pow_mul_factorial (n : ℕ) :
    n ^ n ≤ 3 ^ n * n.factorial := by
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (by positivity) n
  have he : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
    calc
      Real.exp (n : ℝ) = Real.exp 1 ^ n := by
        rw [← Real.exp_nat_mul, mul_one]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hn := (div_le_iff₀ hf).mp (h.trans he)
  exact_mod_cast hn

end Nat
