/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# An exponential upper bound on binomial coefficients

## Main results

* `Nat.choose_le_exp_mul_div_pow`: the bound `(e n / k)^k`, including `k = 0`.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
Source-derived descriptions below are paraphrases.
-/

@[expose] public section

namespace Nat

/-- `binom(n, k) ≤ (e n / k) ^ k`: indeed `binom(n, k) ≤ n ^ k / k!`, and
`k ^ k / k! ≤ e ^ k` is one term of the exponential series. For `k = 0` both sides are `1`. -/
theorem choose_le_exp_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  obtain rfl | hk := k.eq_zero_or_pos
  · rw [choose_zero_right, pow_zero, cast_one]
  have hk' : (0 : ℝ) < k := cast_pos.2 hk
  have hfact : (0 : ℝ) < k.factorial := cast_pos.2 k.factorial_pos
  have hexp : (k : ℝ) ^ k ≤ Real.exp k * k.factorial :=
    (div_le_iff₀ hfact).1 (Real.pow_div_factorial_le_exp _ hk'.le k)
  rw [div_pow, mul_pow, ← Real.exp_nat_mul, mul_one]
  refine (choose_le_pow_div k n).trans ?_
  rw [div_le_div_iff₀ hfact (pow_pos hk' k)]
  calc (n : ℝ) ^ k * (k : ℝ) ^ k ≤ (n : ℝ) ^ k * (Real.exp k * k.factorial) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg n.cast_nonneg k)
    _ = Real.exp k * (n : ℝ) ^ k * k.factorial := by ring


end Nat
