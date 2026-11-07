/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF

/-!
# Chebyshev's inequality for finite distributions

For a distribution `p` on a finite type, a real score `f`, a centre `m` and `c > 0`, the mass of
any set of points where `|f a - m| ≥ c` is at most `∑ a, p(a) (f a - m)² / c²`
(`sum_mul_ite_le_sum_mul_sq_div`). With `m` the mean of `f` this is Chebyshev's inequality with
the variance; the statement is a finite sum, so no measure-theoretic integrability side
conditions arise.

## Main results

* `Cslib.Probability.PMF.sum_mul_ite_le_sum_mul_sq_div`: Chebyshev's inequality.
-/

public section

namespace Cslib.Probability.PMF

open Finset

variable {α : Type*} [Fintype α]

/-- **Chebyshev's inequality** for a finite distribution: every set of points where `f` deviates
from `m` by at least `c > 0` has mass at most the second moment of `f - m` divided by `c²`. -/
theorem sum_mul_ite_le_sum_mul_sq_div (p : PMF α) (f : α → ℝ) (m : ℝ) {c : ℝ} (hc : 0 < c)
    (A : α → Prop) [DecidablePred A] (hA : ∀ a, A a → c ≤ |f a - m|) :
    ∑ a, (p a).toReal * (if A a then 1 else 0) ≤ (∑ a, (p a).toReal * (f a - m) ^ 2) / c ^ 2 := by
  rw [le_div_iff₀ (by positivity), sum_mul]
  refine sum_le_sum fun a _ => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  split_ifs with h
  · rw [one_mul, ← sq_abs (f a - m)]
    exact pow_le_pow_left₀ hc.le (hA a h) 2
  · rw [zero_mul]
    exact sq_nonneg _

end Cslib.Probability.PMF
