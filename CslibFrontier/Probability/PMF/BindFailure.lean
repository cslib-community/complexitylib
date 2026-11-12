/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.EventBind

/-!
# Failure of a continuation after a bad first stage

After a random first stage `p`, a continuation `kernel` reaches `event` with probability at most
the probability that the first stage is bad plus a bound on reaching `event` from its supported
good outcomes. This is `toOuterMeasure_bind_failure_le` stated for the bad set instead of its
complement; it replaces the recurring split of `∑' a, p a * (kernel a).toOuterMeasure event` into
`bad.indicator 1 a + error`.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_bind_le_add`: the failure bound for a bad first stage.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- A continuation reaches `event` with probability at most that of a bad first stage plus
`error`, when every supported good first-stage outcome leads to `event` with probability at most
`error`. -/
theorem toOuterMeasure_bind_le_add (p : PMF α) (kernel : α → PMF β) (bad : Set α)
    (event : Set β) (error : ℝ≥0∞)
    (hstep : ∀ a ∈ p.support, a ∉ bad → (kernel a).toOuterMeasure event ≤ error) :
    (p.bind kernel).toOuterMeasure event ≤ p.toOuterMeasure bad + error := by
  simpa only [compl_compl] using toOuterMeasure_bind_failure_le p kernel badᶜ event error hstep

end Cslib.Probability.PMF
