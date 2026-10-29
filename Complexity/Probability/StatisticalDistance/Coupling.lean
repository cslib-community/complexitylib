/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Event
import Complexity.Probability.StatisticalDistance

/-!
# The coupling inequality

Two functions of one sample are at statistical distance at most the probability that they differ
(`Cslib.Probability.PMF.dist_map_map_le`). The sample space may be infinite; only the common
codomain is finite.

## Main results

* `Cslib.Probability.PMF.dist_map_map_le`: the coupling inequality.
-/

@[expose] public section

open scoped Cslib.Probability.PMF

namespace Cslib.Probability.PMF

variable {α β : Type*}

private theorem dist_map_map_le_of_finite [Finite α] [Fintype β] (p : PMF α) (f g : α → β) :
    dist (p.map f) (p.map g) ≤ (p.toOuterMeasure {a | f a ≠ g a}).toReal := by
  classical
  have := Fintype.ofFinite α
  have hmap (h : α → β) :
      (p.bind fun a => (PMF.pure (h a)).map (a, ·)).map Prod.snd = p.map h := by
    simp only [PMF.map_bind, PMF.pure_map]
    rfl
  rw [← hmap f, ← hmap g]
  refine (dist_map_le _ _ Prod.snd).trans ?_
  rw [dist_bind_pair, toOuterMeasure_apply_toReal]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases h : f a = g a
  · simp [h]
  · simpa [h] using mul_le_mul_of_nonneg_left
      (dist_le_one (PMF.pure (f a)) (PMF.pure (g a))) (ENNReal.toReal_nonneg (a := p a))

/-- **Coupling inequality.** Two functions of the same sample are at statistical distance at most
the probability that they differ. -/
theorem dist_map_map_le [Fintype β] (p : PMF α) (f g : α → β) :
    dist (p.map f) (p.map g) ≤ (p.toOuterMeasure {a | f a ≠ g a}).toReal := by
  have h := dist_map_map_le_of_finite (p.map fun a => (f a, g a)) Prod.fst Prod.snd
  rwa [PMF.map_comp, PMF.map_comp, PMF.toOuterMeasure_map_apply] at h

end Cslib.Probability.PMF
