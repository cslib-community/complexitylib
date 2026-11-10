/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Multigraph.CutSpace
import CslibFrontier.Foundations.Data.Finset.SymmDiff

/-!
# Tests: the cut space of a multigraph

Edge cuts of single vertices on a multigraph with a self-loop and parallel edges, the symmetric
difference identity on a triangle together with the cardinality bound `#(s ∆ t) ≤ #s + #t`,
connectivity in the empty-cut lemma, and the expansion dichotomy on `K₄`, including the case where
its two-thirds hypothesis fails.
-/

namespace CslibFrontierTests.Foundations.Multigraph.CutSpace

open Cslib Finset

/-! ### Single vertices, self-loops and parallel edges -/

/-- Edge `0` is a self-loop at `0`; edges `1` and `2` are parallel edges joining `0` and `1`. -/
private def multi : Fin 3 → Sym2 (Fin 2) := fun e => if e = 0 then s(0, 0) else s(0, 1)

/-- The self-loop does not leave `{0}`; both parallel edges do. -/
example : Multigraph.edgeCut multi {0} = {1, 2} := by
  rw [Multigraph.edgeCut_singleton]
  decide

/-! ### Symmetric differences on a triangle -/

/-- The triangle on `Fin 3`: edge `i` joins `i` and `i + 1`. -/
private def triangle : Fin 3 → Sym2 (Fin 3) := fun i => s(i, i + 1)

example : Multigraph.edgeCut triangle {0} = {0, 2} := by
  rw [Multigraph.edgeCut_singleton]
  decide

/-- The cuts of `{0}` and `{1}` share edge `0`, which joins them, so the cut of `{0, 1}` is
`{1, 2}`. -/
example : Multigraph.edgeCut triangle {0, 1} =
    symmDiff (Multigraph.edgeCut triangle {0}) (Multigraph.edgeCut triangle {1}) := by
  rw [← Multigraph.edgeCut_symmDiff]
  decide

/-- By `Finset.card_symmDiff_le`, at most `2 + 2` edges leave `{0, 1}`. The bound is not
attained: only two edges leave, since the shared edge `0` cancels. -/
example : #(Multigraph.edgeCut triangle {0, 1}) ≤ 4 := by
  rw [show ({0, 1} : Finset (Fin 3)) = symmDiff {0} {1} by decide, Multigraph.edgeCut_symmDiff]
  exact (card_symmDiff_le _ _).trans (by decide)

/-! ### Connectivity is needed for empty cuts -/

private theorem connected_triangle : (Multigraph.toSimpleGraph triangle).Connected :=
  (Multigraph.connected_toSimpleGraph_iff triangle).2 ⟨⟨0⟩, by decide⟩

/-- On the connected triangle, a set with empty cut is `∅` or everything. -/
example {S : Finset (Fin 3)} (hS : Multigraph.edgeCut triangle S = ∅) : S = ∅ ∨ S = univ :=
  Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty connected_triangle hS

/-- Two vertices whose only edge is a self-loop at `0`. -/
private def loopAndPoint : Fin 1 → Sym2 (Fin 2) := fun _ => s(0, 0)

/-- This multigraph is not connected, and `{0}` has empty cut but is neither `∅` nor everything,
so connectivity cannot be dropped. -/
example : ¬ (Multigraph.toSimpleGraph loopAndPoint).Connected ∧
    Multigraph.edgeCut loopAndPoint {0} = ∅ ∧ ({0} : Finset (Fin 2)) ≠ ∅ ∧
    ({0} : Finset (Fin 2)) ≠ univ := by
  refine ⟨fun h => ?_, by decide⟩
  obtain ⟨e, he⟩ := ((Multigraph.connected_toSimpleGraph_iff loopAndPoint).1 h).2 {0}
    (by decide) (by decide)
  revert e
  decide

/-! ### The expansion dichotomy on `K₄` -/

/-- The complete graph on four vertices, with one edge for each pair `i < j`. -/
private def k4 : {p : Fin 4 × Fin 4 // p.1 < p.2} → Sym2 (Fin 4) := fun p => s(p.1.1, p.1.2)

/-- The balanced sets of `K₄` are its pairs, and four edges leave each pair, so `e(K₄) ≥ 4`. -/
private theorem four_le_minBalancedCut_k4 : 4 ≤ Multigraph.minBalancedCut k4 :=
  (Multigraph.le_minBalancedCut_iff k4 (by decide)).2 (by decide)

/-- Three edges leave a single vertex, fewer than `e(K₄)`, so the dichotomy applies. -/
example : 3 * #({0} : Finset (Fin 4)) < Fintype.card (Fin 4) :=
  Multigraph.three_mul_card_lt_of_card_edgeCut_lt
    (lt_of_lt_of_le (by decide) four_le_minBalancedCut_k4) (by decide)

/-- The two-thirds hypothesis is needed: three edges leave a set of three vertices, fewer than
`e(K₄)`, yet that set has more than a third of the vertices. -/
example : #(Multigraph.edgeCut k4 {0, 1, 2}) < Multigraph.minBalancedCut k4 ∧
    ¬ 3 * #({0, 1, 2} : Finset (Fin 4)) < Fintype.card (Fin 4) :=
  ⟨lt_of_lt_of_le (by decide) four_le_minBalancedCut_k4, by decide⟩

end CslibFrontierTests.Foundations.Multigraph.CutSpace
