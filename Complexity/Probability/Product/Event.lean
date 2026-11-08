/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product

/-!
# Failure events in finite products

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_pi_exists_le`: a union bound for coordinate events.
-/

public section

namespace Cslib.Probability.PMF

/-- The probability that some coordinate lies in its bad event is at most the sum of the
coordinate probabilities. The marginal identities supply the exact coordinate laws. -/
theorem toOuterMeasure_pi_exists_le {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Finite (α i)] (p : ∀ i, PMF (α i)) (bad : ∀ i, Set (α i)) :
    (pi p).toOuterMeasure {x | ∃ i, x i ∈ bad i} ≤ ∑ i, (p i).toOuterMeasure (bad i) := by
  classical
  have hset : {x : ∀ i, α i | ∃ i, x i ∈ bad i} =
      ⋃ i, (fun x : ∀ i, α i => x i) ⁻¹' bad i := by ext; simp
  rw [hset]
  calc
    _ ≤ ∑ i, (pi p).toOuterMeasure ((fun x => x i) ⁻¹' bad i) :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ = _ := by
      congr 1
      funext i
      rw [← PMF.toOuterMeasure_map_apply, pi_map_eval]

end Cslib.Probability.PMF
