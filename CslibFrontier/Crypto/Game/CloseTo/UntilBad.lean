/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Probability.PMF.Event

/-!
# Mixtures that agree outside a bad event

Two randomized continuations that agree on supported inputs outside a bad event induce close
mixtures, with error equal to the actual probability of that event. Neither type must be finite.
The proof specializes the variable-error mixture bound `CloseTo.bind_right_tsum` to the indicator
of `bad`.

## Main results

* `CloseTo.bind_of_eq_on`: charge only the probability of inputs where the kernels may differ.

This original application supports cache programming: a memoized query and fresh programming
agree when the query point is absent from the current cache.
-/

public section

namespace Cslib.Interactive

open Probability
open scoped ENNReal

/-- Mixtures of kernels that agree on supported inputs outside `bad` are close within the
probability of `bad`. The conclusion controls all output events, including on infinite types. -/
theorem CloseTo.bind_of_eq_on {α β : Type} (μ : PMF α) (f g : α → PMF β) (bad : Set α)
    (h : ∀ a ∈ μ.support, a ∉ bad → f a = g a) :
    CloseTo (μ.bind f) (μ.bind g) (μ.toOuterMeasure bad) := by
  classical
  refine (CloseTo.bind_right_tsum (err := bad.indicator 1) μ fun a ha => ?_).mono ?_
  · by_cases hbad : a ∈ bad
    · intro event
      simp only [Set.indicator_of_mem hbad, Pi.one_apply]
      exact (PMF.toOuterMeasure_le_one (f a) event).trans le_add_self
    · rw [h a ha hbad, Set.indicator_of_notMem hbad]
      exact CloseTo.refl _
  · rw [PMF.toOuterMeasure_apply]
    refine le_of_eq (tsum_congr fun a => ?_)
    by_cases hbad : a ∈ bad <;> simp [hbad]

end Cslib.Interactive
