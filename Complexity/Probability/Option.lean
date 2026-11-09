/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Logic.Equiv.Option
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Summing optional outcomes

## Main results

* `tsum_option_eq`: split a nonnegative extended-real sum into failure and successful outcomes.
-/

@[expose] public section

namespace Cslib.Probability

open scoped ENNReal

/-- Separate the failure outcome from all successful outcomes, without a summability premise. -/
theorem tsum_option_eq {α : Type*} (f : Option α → ℝ≥0∞) :
    ∑' x, f x = f none + ∑' x, f (some x) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, _} α).symm.tsum_eq f]
  rw [CompleteLattice.summable.tsum_sum CompleteLattice.summable]
  simp [add_comm]

end Cslib.Probability
