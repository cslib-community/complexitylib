/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF

/-!
# Expectations that only see the support

An `ℝ≥0∞`-valued expectation `∑' a, p a * f a` under `p : PMF α` depends only on the values of
`f` on `p.support`. These lemmas package the off-support case split (`p a = 0`) that otherwise
recurs whenever a coupled-state invariant holds only on the support, such as a pinned
abstract state in the randomized state-transition certificates.

## Main results

* `Cslib.Probability.PMF.tsum_mul_congr_support`: expectations of functions agreeing on the
  support are equal.
* `Cslib.Probability.PMF.tsum_mul_add_of_support`: a summand that is constant on the support
  leaves the expectation as that constant.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*}

/-- An expectation depends only on the values of the integrand on the support. -/
theorem tsum_mul_congr_support (p : PMF α) {f g : α → ℝ≥0∞} (h : ∀ a ∈ p.support, f a = g a) :
    ∑' a, p a * f a = ∑' a, p a * g a := by
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff p a).mpr ha, zero_mul, zero_mul]

/-- A summand equal to the constant `c` on the support contributes exactly `c` to the
expectation. -/
theorem tsum_mul_add_of_support (p : PMF α) {g f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hg : ∀ a ∈ p.support, g a = c) :
    ∑' a, p a * (g a + f a) = c + ∑' a, p a * f a := by
  rw [tsum_mul_congr_support p (g := fun a => c + f a) fun a ha => by rw [hg a ha]]
  simp only [mul_add]
  rw [tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

end Cslib.Probability.PMF
