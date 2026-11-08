/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Init
public import Complexity.Algorithms.Lean.MaxFlow.Hungarian

/-!
# Hungarian Method Tests

Kernel-checked examples (without `native_decide`) for
`Complexity.Algorithms.Lean.MaxFlow.WeightedMatching` and
`Complexity.Algorithms.Lean.MaxFlow.Hungarian`:

1. **Greedy trap (`2 × 2`):** taking the cheapest entry of row `0` first costs `1 + 100`, while the
   optimum is `2 + 2 = 4`. The solver returns the anti-diagonal with potentials summing to `4`.
2. **A `3 × 3` instance:** the returned matching costs `5`, the potentials are feasible and sum to
   `5`, and every permutation costs at least `5` (checked by enumeration).
3. **Dual adjustments with negative costs (`4 × 4`):** `c (i, j) = (i + 1) (j + 1) - 6` has all row
   minima in column `0`, so the phases have to adjust potentials. The optimum `-4` is the
   anti-diagonal, by the rearrangement inequality.
4. **Edge cases and the structures:** `n = 0` and `n = 1`, charged times within
   `hungarianM_time_le`, and positive and negative `IsPerfectMatching` and `IsFeasiblePotential`
   instances.
-/

public section

namespace ComplexityTests.Hungarian

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow

/-! ### 1. Greedy trap -/

/-- Costs `[[1, 2], [2, 100]]`. -/
def trapCost : Fin 2 × Fin 2 → ℤ := fun e => ![![1, 2], ![2, 100]] e.1 e.2

example : (hungarianM trapCost).ret.matching = {(0, 1), (1, 0)} := by decide

example : matchingCost trapCost (hungarianM trapCost).ret.matching = 4 := by decide

/-- The greedy assignment `{(0, 0), (1, 1)}` is a perfect matching costing `101`. -/
example : IsPerfectMatching (fun _ => true) ({(0, 0), (1, 1)} : Finset (Fin 2 × Fin 2)) ∧
    matchingCost trapCost {(0, 0), (1, 1)} = 101 := by
  unfold IsPerfectMatching
  decide

example : ∑ u, (hungarianM trapCost).ret.y u + ∑ v, (hungarianM trapCost).ret.z v = 4 := by
  decide

example : (hungarianM trapCost).time = 58 := by decide

/-! ### 2. A `3 × 3` instance -/

/-- Costs `[[4, 1, 3], [2, 0, 5], [3, 2, 2]]`. -/
def cost3 : Fin 3 × Fin 3 → ℤ := fun e => ![![4, 1, 3], ![2, 0, 5], ![3, 2, 2]] e.1 e.2

example : (hungarianM cost3).ret.matching = {(0, 1), (1, 0), (2, 2)} := by decide

example : matchingCost cost3 (hungarianM cost3).ret.matching = 5 := by decide

/-- Independent certificate check: the output potentials are feasible and sum to the cost. -/
example : IsFeasiblePotential (fun _ => true) cost3 (hungarianM cost3).ret.y
      (hungarianM cost3).ret.z ∧
    ∑ u, (hungarianM cost3).ret.y u + ∑ v, (hungarianM cost3).ret.z v = 5 := by
  unfold IsFeasiblePotential
  decide

/-- Brute force: every permutation costs at least the optimum `5`. -/
example : ∀ σ : Equiv.Perm (Fin 3), 5 ≤ ∑ u, cost3 (u, σ u) := by decide

example : (hungarianM cost3).time = 112 := by decide

example : (hungarianM cost3).time ≤ 6 * 3 ^ 3 + 6 * 3 ^ 2 + 3 * 3 := hungarianM_time_le cost3

/-- The general theorem applied to the instance. -/
example : IsMinCostPerfectMatching (fun _ => true) cost3 (hungarianM cost3).ret.matching :=
  (hungarianM_correct cost3).1

/-! ### 3. Dual adjustments with negative costs -/

/-- Costs `(i + 1) (j + 1) - 6`: every row minimum lies in column `0`. -/
def cost4 : Fin 4 × Fin 4 → ℤ := fun e => ((e.1 : ℤ) + 1) * ((e.2 : ℤ) + 1) - 6

example : (hungarianM cost4).ret.matching = {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide

example : matchingCost cost4 (hungarianM cost4).ret.matching = -4 := by decide

example : IsFeasiblePotential (fun _ => true) cost4 (hungarianM cost4).ret.y
      (hungarianM cost4).ret.z ∧
    ∑ u, (hungarianM cost4).ret.y u + ∑ v, (hungarianM cost4).ret.z v = -4 := by
  unfold IsFeasiblePotential
  decide +kernel

/-- Row reduction alone does not give tight potentials here: the row minima sum to `-14`. -/
example : ∑ u, (hgRowMinM cost4 u).ret = -14 := by decide

/-! ### 4. Edge cases and the structures -/

example : (hungarianM (n := 0) fun _ => 0).time = 0 := by decide

example : (hungarianM (n := 0) fun _ => 0).ret.matching = ∅ := by decide

example : (hungarianM (n := 1) fun _ => 7).ret.matching = {(0, 0)} := by decide

example : ¬ IsPerfectMatching (fun _ => true) ({(0, 1)} : Finset (Fin 2 × Fin 2)) := by
  unfold IsPerfectMatching
  decide

example : ¬ IsPerfectMatching (fun _ => true) ({(0, 0), (1, 0)} : Finset (Fin 2 × Fin 2)) := by
  unfold IsPerfectMatching
  decide

/-- Row maxima are not feasible potentials for `trapCost`. -/
example : ¬ IsFeasiblePotential (fun _ => true) trapCost ![2, 100] ![0, 0] := by
  unfold IsFeasiblePotential
  decide

example : IsPerfectMatching (fun _ => true) (permMatching (Equiv.swap (0 : Fin 3) 2)) :=
  isPerfectMatching_permMatching _

example : matchingCost cost3 (permMatching (Equiv.swap (0 : Fin 3) 2)) = 3 + 0 + 3 := by
  rw [matchingCost_permMatching]
  decide

end ComplexityTests.Hungarian
