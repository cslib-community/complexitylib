/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteTable

/-!
# Nonnegative table expectations as PMF sums

## Main results

* `Distribution.ofReal_mean`: a nonnegative finite real mean is the corresponding
  extended nonnegative PMF expectation.
-/

public section
noncomputable section
namespace Cslib.Optimization.OneConstraint.Distribution
open Finset
variable {α : Type*} [Fintype α]

/-- Nonnegative finite table expectation agrees with the PMF weighted sum. -/
theorem ofReal_mean (w : Distribution α ℝ) (score : α → ℝ) (hscore : ∀ x, 0 ≤ score x) :
    ENNReal.ofReal (w.mean score) = ∑' x, w.toPMF x * ENNReal.ofReal (score x) := by
  rw [tsum_fintype]
  change ENNReal.ofReal (∑ x, w.weight x * score x) = _
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (w.nonneg x) (hscore x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [ENNReal.ofReal_mul (w.nonneg x)]
  rfl

end Cslib.Optimization.OneConstraint.Distribution
