/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Basic.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.SymmDiff

/-!
# Symmetric difference of simple graphs

Simple graphs on `V` form a Boolean algebra, so two graphs have a symmetric difference. Its edges
are the edges of exactly one of the two graphs.

## Main results

* `SimpleGraph.symmDiff_adj`: adjacency in the symmetric difference of two graphs.
* `SimpleGraph.edgeSet_symmDiff`: the edge set of a symmetric difference is the symmetric
  difference of the edge sets.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- Two vertices are adjacent in `symmDiff G H` exactly when they are adjacent in one of `G` and
`H` but not in the other. -/
@[simp]
theorem symmDiff_adj (G H : SimpleGraph V) (a b : V) :
    (symmDiff G H).Adj a b ↔ G.Adj a b ∧ ¬H.Adj a b ∨ H.Adj a b ∧ ¬G.Adj a b := by
  rw [symmDiff_def, sup_adj, sdiff_adj, sdiff_adj]

/-- The edge set of the symmetric difference of two graphs is the symmetric difference of their
edge sets. -/
@[simp]
theorem edgeSet_symmDiff (G H : SimpleGraph V) :
    (symmDiff G H).edgeSet = symmDiff G.edgeSet H.edgeSet := by
  rw [symmDiff_def, symmDiff_def, edgeSet_sup, edgeSet_sdiff, edgeSet_sdiff]
  rfl

end SimpleGraph
