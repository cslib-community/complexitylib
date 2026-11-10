/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Sensitivity
public import CslibFrontier.Computability.QueryComplexity.Threshold
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment

/-!
# Decision trees for parity

Flipping any bit flips the parity, so parity is sensitive to every bit at every input
(`BitString.sensitivityAt_parity`), and every decision tree for it queries all of its bits in the
worst case (`DecisionTree.complexity_parity`) [Jukna, Chapter 14][Jukna2012]. More generally,
restricted parity queries every free bit (`DecisionTree.card_free_le_complexity_parity_fill`).

## Main results

* `Cslib.DecisionTree.complexity_parity`: the decision tree complexity of the parity of `n` bits
  is `n`.
* `Cslib.DecisionTree.card_free_le_complexity_parity_fill`: restricted parity still needs to query
  every free bit.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

public section

namespace Cslib

open Finset BitString QueryComplexity

variable {n : ℕ}

namespace DecisionTree

/-- Every decision tree for the parity of `n` bits queries all of them in the worst case. -/
theorem complexity_parity : complexity (parity n) = n :=
  complexity_eq_card_of_sensitivityAt_eq_card (sensitivityAt_parity (fun _ => false))

/-- **Restricted parity** is the parity of the free bits, up to a constant, so every decision tree
for it queries all free bits in the worst case. -/
theorem card_free_le_complexity_parity_fill (ρ : PartialAssignment (Fin n)) :
    #ρ.free ≤ complexity fun x => parity n (ρ.fill x) := by
  refine card_le_complexity_of_forall_update_ne (x := fun _ => false) fun i hi => ?_
  have hρ := PartialAssignment.mem_free.1 hi
  set y := ρ.fill fun _ => false
  have hfill : ρ.fill (Function.update (fun _ => false) i !false) = Function.update y i !y i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [y, PartialAssignment.fill, hρ]
    · simp [y, PartialAssignment.fill, hj]
  simp only [hfill]
  rw [parity, parityOn_update_not (mem_univ i)]
  cases parityOn univ y <;> decide

end DecisionTree

end Cslib
