/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Resources
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Real per-call caps for concurrent invoices

## Main results

* `observe_tokens_le`: accrued invoices, including cancellation, are bounded by
  the sum of real per-call caps. No total-bill or integrability premise is used.
-/

public section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch
open scoped NNReal

/-- Monotone accrued charges at actual response/cancellation times obey arbitrary
real per-call caps, whether or not the caps are encoded as algorithmic input. -/
theorem observe_tokens_le {n : ℕ} (limits : Limits n) (remaining : ℝ≥0) (b : Batch n)
    (paths : Fin n → CallTrace) (caps : Fin n → ℝ)
    (hcap : ∀ i ∈ active b.slots, ((paths i).accrued (limits.cutoff i) : ℝ) ≤ caps i) :
    ((observe limits remaining b paths).tokens : ℝ) ≤ ∑ i ∈ active b.slots, caps i := by
  rw [observe_tokens, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ ((paths i).accrued (limits.cutoff i) : ℝ) := by
      exact_mod_cast (paths i).monotone
        (((paths i).stop_le _).trans (min_le_left (limits.cutoff i) remaining))
    _ ≤ _ := hcap i hi

end Cslib.Probability.StochasticOracle.ConcurrentBatch
