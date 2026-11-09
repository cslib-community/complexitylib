/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Operations.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Set.Card
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.SymmDiff
import CslibFrontier.Foundations.Data.Set.SymmDiff

/-!
# Graphs with an even number of edges

`SimpleGraph.EvenEdges G` says that `G` has an even number of edges, counted with `Set.ncard`.
Toggling one potential edge, that is, taking the symmetric difference with `SimpleGraph.edge u v`
for distinct `u` and `v`, flips this parity on finitely many vertices.

## Main definitions

* `SimpleGraph.EvenEdges`: a graph with an even number of edges.

## Main results

* `SimpleGraph.evenEdges_symmDiff_edge_iff`: toggling one potential edge flips the parity of the
  number of edges.
-/

public section

namespace SimpleGraph

/-- A graph has an even number of edges. -/
@[expose]
def EvenEdges {V : Type*} (G : SimpleGraph V) : Prop :=
  Even G.edgeSet.ncard

/-- Toggling one potential edge `uv` of a graph on finitely many vertices changes the parity of
its number of edges. -/
theorem evenEdges_symmDiff_edge_iff {V : Type*} [Finite V] {u v : V} (huv : u ≠ v)
    (G : SimpleGraph V) : (symmDiff G (edge u v)).EvenEdges ↔ ¬G.EvenEdges := by
  rw [EvenEdges, EvenEdges, edgeSet_symmDiff, edgeSet_edge_of_ne huv]
  exact Set.even_ncard_symmDiff_singleton_iff (Set.toFinite _) _

end SimpleGraph
