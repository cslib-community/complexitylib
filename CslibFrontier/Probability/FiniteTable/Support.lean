/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteTable

/-!
# Support of finite-table interpretations

Interpreting a real probability table preserves its positive-weight outcomes.
-/

public section
namespace Cslib.Optimization.OneConstraint.Distribution
variable {α : Type*} [Fintype α]

/-- Actual PMF support consists exactly of the original positive-weight outcomes. -/
theorem mem_support_toPMF (w : Distribution α ℝ) (a : α) :
    a ∈ w.toPMF.support ↔ 0 < w.weight a := by
  change ENNReal.ofReal (w.weight a) ≠ 0 ↔ 0 < w.weight a
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]

end Cslib.Optimization.OneConstraint.Distribution
