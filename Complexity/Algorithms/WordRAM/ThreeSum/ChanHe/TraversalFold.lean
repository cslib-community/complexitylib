/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalModel

/-!
# Ordered folds over Chan–He worklist emissions

A visitor consumes the current optional node before processing the updated pending list.
The fold law retains the finite reduction's exact preorder and multiplicity, so it applies
to a stateful consumer as well as Boolean disjunction. Skipped entries leave the fold unchanged.

## Main results

* `Math.foldl_step`: one worklist transition preserves the complete ordered fold.

This follows from the existing exact output-list invariant and the standard list fold law.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal.Math

open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Consume the optional current emission before the exact remaining preorder output. -/
theorem foldl_step {α : Type*} (consume : α → Node → α) (initial : α)
    (Q : Finset ℕ) (Λ : ℕ) (t : Task) (ts : List Task) :
    (output Q Λ (t :: ts)).foldl consume initial =
      (output Q Λ (step Q Λ t ts).1).foldl consume
        ((step Q Λ t ts).2.toList.foldl consume initial) := by
  rw [output_step, List.foldl_append]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal.Math
