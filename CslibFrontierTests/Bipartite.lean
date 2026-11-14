/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.Bipartite.LogSpace

/-!
# Bipartiteness tests

Goldreich, Exercise 5.16: bipartiteness of graphs encoded by adjacency matrices is in `L`
(`Cslib.Complexity.Bipartite.mem_L`), through a logspace many-one reduction of non-bipartiteness
to undirected connectivity (`Cslib.Complexity.Bipartite.compl_logSpaceReducible_USTCON`).

The language is neither empty nor everything: the single edge is bipartite and the triangle is
not. The encoding of the single edge is pinned bit by bit. The copies of the double cover of the
triangle connect the source to the target, and those of the single edge do not
(`Cslib.Complexity.Bipartite.oddCycleInstance_mem_iff`); the number of vertices of the instance
and the numbering of the vertices of the copies are checked on small values.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Bipartite

open Cslib Cslib.Complexity Cslib.Complexity.Bipartite

/-- The single edge `0 — 1`. -/
private def edge : UGraphInstance where
  n := 2
  adj a b := decide (a ≠ b)
  symm a b := by simp [ne_comm]
  loopless a := by simp

/-- The single edge is bipartite: colour each vertex by itself. -/
private theorem edge_mem : edge ∈ Bipartite :=
  ⟨SimpleGraph.Coloring.mk (fun v => v) fun {a b} h => by
    have h' : edge.adj a b = true := h
    simpa [edge] using h'⟩

example : edge ∈ Bipartite := edge_mem

example : triangle ∉ Bipartite := triangle_notMem

example : empty ∈ Bipartite := empty_mem

/-- The encoding of the single edge: the header `1 1 0` and the matrix `0 1 1 0`. -/
example : encUGraph edge = [true, true, false, false, true, true, false] := by decide

/-- The instance has `2 n² + 2` vertices: `20` for the triangle. -/
example : (oddCycleInstance triangle).n = 20 := rfl

/-- The vertex `(v, b)` of the copy `x` is `2 + 2 n x + 2 v + b`; it decodes back. -/
example : copyVertex 3 1 2 true = 13 ∧ copy 3 13 = 1 ∧ vert 3 13 = 2 ∧ side 13 = 1 := by decide

/-- The triangle has an odd cycle, so the source reaches the target. -/
example : oddCycleInstance triangle ∈ USTCON :=
  (oddCycleInstance_mem_iff triangle).2 triangle_notMem

/-- The single edge has no odd cycle, so the source does not reach the target. -/
example : oddCycleInstance edge ∉ USTCON :=
  fun h => (oddCycleInstance_mem_iff edge).1 h edge_mem

/-- The headline: bipartiteness is in `L`, and non-bipartiteness and undirected connectivity
reduce to each other in logarithmic space. -/
example : Bipartite ∈ L encUGraph := mem_L

example : LogSpaceReducible encUGraph encUSTCON Bipartiteᶜ USTCON :=
  compl_logSpaceReducible_USTCON

example : LogSpaceReducible encUSTCON encUGraph USTCON Bipartiteᶜ :=
  USTCON_logSpaceReducible_compl

end CslibFrontierTests.Bipartite
