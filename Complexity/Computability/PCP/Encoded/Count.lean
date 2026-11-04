/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Counting violated edges of an executable constraint graph

The edge list counts occurrences, including loops and parallel edges. These identities connect
its executable Boolean tests to the finite-edge semantics used by `ConstraintGraph.unsatVal`.

## Main results

* `Cslib.PCP.Encoded.Graph.card_unsatEdges_toGraph`: the number of violations as a list count.
* `Cslib.PCP.Encoded.Graph.unsatFrac_toGraph`: the proportion of violations as a list count.
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Finset

private theorem card_filter_get_eq_countP {β : Type*} (p : β → Bool) (l : List β) :
    #{i : Fin l.length | p (l.get i) = true} = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    change #{i : Fin (l.length + 1) | p ((a :: l).get i) = true} = _
    rw [List.countP_cons, ← ih, Fin.card_filter_univ_succ', add_comm]
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ]
    congr

/-- Violated edge occurrences counted along the stored edge list. -/
theorem card_unsatEdges_toGraph {C α : Type} (g : Graph C) (eval : C → α → α → Bool)
    (σ : ℕ → α) :
    #((g.toGraph eval).unsatEdges σ) =
      g.edges.countP fun d => !eval d.constraint (σ d.src) (σ d.dst) := by
  rw [← card_filter_get_eq_countP]
  congr 1
  ext i
  simp [ConstraintGraph.Satisfies, toGraph]

/-- The semantic violated fraction is the executable count divided by the edge-list length. -/
theorem unsatFrac_toGraph {C α : Type} (g : Graph C) (eval : C → α → α → Bool)
    (σ : ℕ → α) :
    (g.toGraph eval).unsatFrac σ =
      (g.edges.countP (fun d => !eval d.constraint (σ d.src) (σ d.dst)) : ℝ) / g.edges.length := by
  rw [ConstraintGraph.unsatFrac, card_unsatEdges_toGraph, Fintype.card_fin]

end Cslib.PCP.Encoded.Graph
