/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.QueryComplexity.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! Concrete edge-query clients, including the empty graph and two graphs with the same number
of edges but different connectivity. The theorem also applies to trees that repeat a query. -/

open Cslib Cslib.BitString.Graph

namespace CslibFrontierTests.ConnectivityEvasiveness

example (x : BitString (edgeCount 0)) : connectivity 0 x = false := connectivity_zero x
example (x : BitString (edgeCount 1)) : connectivity 1 x = true := connectivity_one x
example : DecisionTree.complexity (connectivity 0) = 0 := complexity_connectivity 0
example : DecisionTree.complexity (connectivity 1) = 0 := complexity_connectivity 1
example : DecisionTree.complexity (connectivity 2) = 1 := complexity_connectivity 2
example : DecisionTree.complexity (connectivity 3) = 3 := complexity_connectivity 3
example : DecisionTree.complexity (connectivity 4) = 6 := complexity_connectivity 4

example : connectivity 3 (ofGraph (SimpleGraph.pathGraph 3)) = true := by
  rw [connectivity_eq_true, graph_ofGraph]
  exact SimpleGraph.connected_pathGraph_add_one 2

private def triangleWithIsolate : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v ∧ u < 3 ∧ v < 3
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance : DecidableRel triangleWithIsolate.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ < 3 ∧ _ < 3))

example : (SimpleGraph.pathGraph 4).edgeFinset.card = 3 := by decide
example : triangleWithIsolate.edgeFinset.card = 3 := by decide

example : connectivity 4 (ofGraph (SimpleGraph.pathGraph 4)) = true := by
  rw [connectivity_eq_true, graph_ofGraph]
  exact SimpleGraph.connected_pathGraph_add_one 3

example : connectivity 4 (ofGraph triangleWithIsolate) = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  have hc : triangleWithIsolate.Connected := by
    simpa only [graph_ofGraph] using connectivity_eq_true.mp htrue
  have hzero : triangleWithIsolate.neighborSet 3 = ∅ := by
    ext v
    simp [SimpleGraph.mem_neighborSet, triangleWithIsolate]
  exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
    (by decide : (3 : Fin 4) ≠ 0) hzero (hc 3 0)

/-- A redundant first query may be added to an optimal tree; both remaining queries read that
same unique possible edge. Its depth is two, while connectivity's minimum depth is one. -/
example : ∃ t : DecisionTree (Fin (edgeCount 2)) Bool,
    t.Computes (connectivity 2) ∧ t.depth = 2 := by
  obtain ⟨t, ht, hd⟩ := DecisionTree.exists_computes_depth_eq_complexity (connectivity 2)
  let i : Fin (edgeCount 2) := ⟨0, by rw [edgeCount_eq_choose]; decide⟩
  refine ⟨.node i t t, ?_, ?_⟩
  · intro x
    simp only [DecisionTree.eval_node, Bool.cond_self]
    exact ht x
  · rw [DecisionTree.depth_node, max_self, hd, complexity_connectivity]
    rfl

end CslibFrontierTests.ConnectivityEvasiveness
