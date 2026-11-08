/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Additivity of discrete outer measures

The outer measure of a discrete distribution is additive on disjoint events: every set is
Carathéodory-measurable for it (`PMF.toOuterMeasure_caratheodory`).

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_union_of_disjoint`: additivity on two disjoint events.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*}

/-- The probability of a union of two disjoint events is the sum of their probabilities. -/
theorem toOuterMeasure_union_of_disjoint (p : PMF α) {s t : Set α} (h : Disjoint s t) :
    p.toOuterMeasure (s ∪ t) = p.toOuterMeasure s + p.toOuterMeasure t := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  exact tsum_congr fun y => congrFun (Set.indicator_union_of_disjoint h (⇑p)) y

end Cslib.Probability.PMF
