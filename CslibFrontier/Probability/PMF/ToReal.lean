/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Init
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Real-valued probabilities

Real-valued probabilities `(μ a).toReal` and `(μ.toOuterMeasure s).toReal` of a discrete
distribution lie in `[0, 1]`. Nonnegativity is `ENNReal.toReal_nonneg`; this module supplies the
upper bounds and monotonicity in the event, so that clients working with real-valued probabilities
need not convert `μ a ≤ 1`, `μ.toOuterMeasure s ≤ 1` or `μ.toOuterMeasure s ≤ μ.toOuterMeasure t`
through `ENNReal.toReal` by hand.

## Main results

* `Cslib.Probability.PMF.toReal_apply_le_one`: an outcome has real-valued probability at most one;
  in particular `Pr[e] ≤ 1` for every Boolean experiment.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_le_one`: an event has real-valued probability at
  most one. The name puts `toOuterMeasure` first, as the `toOuterMeasure_toReal_*` lemmas of
  `CslibFrontier.Probability.PMF.Event` do, rather than Mathlib's head-first
  `toReal_toOuterMeasure_le_one`.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_mono`: a larger event has larger real-valued
  probability.
-/

public section

namespace Cslib.Probability.PMF

/-- A probability is at most one; in particular `Pr[e] ≤ 1` for every Boolean experiment. -/
theorem toReal_apply_le_one {α : Type*} (μ : _root_.PMF α) (a : α) : (μ a).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using μ.coe_le_one a)

/-- An event has real-valued probability at most one. -/
theorem toOuterMeasure_toReal_le_one {α : Type*} (μ : _root_.PMF α) (s : Set α) :
    (μ.toOuterMeasure s).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one <| by
    rw [ENNReal.ofReal_one, ← (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)]
    exact μ.toOuterMeasure.mono (Set.subset_univ s)

/-- A larger event has larger real-valued probability. Unlike `ENNReal.toReal_mono`, this needs no
finiteness side condition, since every event has probability at most one. -/
theorem toOuterMeasure_toReal_mono {α : Type*} (μ : _root_.PMF α) {s t : Set α} (h : s ⊆ t) :
    (μ.toOuterMeasure s).toReal ≤ (μ.toOuterMeasure t).toReal := by
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top ?_) (μ.toOuterMeasure.mono h)
  rw [← (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)]
  exact μ.toOuterMeasure.mono (Set.subset_univ t)

end Cslib.Probability.PMF
