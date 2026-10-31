/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.WeightedCut.Multigraph

/-!
# Weighted cut tests

Exercise `Cslib.Multigraph.weightMatrix` and the cut API of `Cslib.WeightedCut` on a multigraph
on `Bool` with two parallel edges and a self-loop: the loop is dropped, the parallel edges count
twice, and the global minimum cut weight is `2`.
-/

namespace ComplexityTests.WeightedCut

open Cslib Cslib.WeightedCut Cslib.Multigraph

/-- Two parallel edges joining `false` and `true`, and a self-loop at `false`. -/
private def ends : Fin 3 → Sym2 Bool
  | 0 => s(false, true)
  | 1 => s(true, false)
  | 2 => s(false, false)

example : weightMatrix ends false true = 2 := by decide

example : weightMatrix ends false false = 0 := by decide

example : IsMultigraph (weightMatrix ends) := isMultigraph_weightMatrix ends

example : cutWeight (weightMatrix ends) {false} = 2 := by
  rw [cutWeight_weightMatrix]
  decide

example : minCut (weightMatrix ends) = 2 := by
  have hV : 2 ≤ Fintype.card Bool := by simp
  refine le_antisymm ?_ ((le_minCut_iff hV _ 2).2 fun C hC => ?_)
  · exact (minCut_weightMatrix_le_card_edgeCut ends (isNonTrivialCut_singleton hV false)).trans
      (by decide)
  · rw [cutWeight_weightMatrix]
    revert C
    unfold IsNonTrivialCut
    decide

end ComplexityTests.WeightedCut
