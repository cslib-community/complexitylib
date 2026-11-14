/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection

/-!
# Finite-history expectation towers

The newest-first recurrence can average the final transition after averaging
its earlier prefix. This common finite tower identity is used by both infinite
path semantics and finite sequential PMF semantics.
-/

public section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
variable {Ω : Type*} [Fintype Ω]

/-- Average the last transition after the preceding prefix, using the actual
full-history conditional response table. -/
theorem historyExpectation_succ_right
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (f : List Ω → ℝ) (n : ℕ) (h : List Ω) :
    historyExpectation law f (n + 1) h =
      historyExpectation law (fun h => (law h).mean (fun y => f (y :: h))) n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change ((law h).mean fun x => historyExpectation law f (n + 1) (x :: h)) = _
    simp only [ih]
    rfl

end Cslib.Probability.StochasticOracle.AdaptiveSelection
