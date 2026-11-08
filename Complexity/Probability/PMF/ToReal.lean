/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import Complexity.Init
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import Complexity.Probability.PMF.Event

/-!
# Real-valued probabilities are at most one

Real-valued probabilities `(μ a).toReal` and `(μ.toOuterMeasure s).toReal` of a discrete
distribution lie in `[0, 1]`. Nonnegativity is `ENNReal.toReal_nonneg`; this module supplies the
upper bounds, so that clients working with real-valued probabilities need not convert `μ a ≤ 1`
or `μ.toOuterMeasure s ≤ 1` through `ENNReal.toReal` by hand.

## Main results

* `Cslib.Probability.PMF.toReal_apply_le_one`: an outcome has real-valued probability at most one;
  in particular `Pr[e] ≤ 1` for every Boolean experiment.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_le_one`: an event has real-valued probability at
  most one.
-/

public section

namespace Cslib.Probability.PMF

/-- A probability is at most one; in particular `Pr[e] ≤ 1` for every Boolean experiment. -/
theorem toReal_apply_le_one {α : Type*} (μ : _root_.PMF α) (a : α) : (μ a).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using μ.coe_le_one a)

/-- An event has real-valued probability at most one. -/
theorem toOuterMeasure_toReal_le_one {α : Type*} (μ : _root_.PMF α) (s : Set α) :
    (μ.toOuterMeasure s).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using toOuterMeasure_le_one μ s)

end Cslib.Probability.PMF
