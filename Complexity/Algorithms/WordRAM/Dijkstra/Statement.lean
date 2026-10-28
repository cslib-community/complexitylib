/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fintype.Prod

/-!
# Dijkstra's algorithm on the word RAM: statements

This file defines the single-source shortest-path problem solved by Dijkstra's algorithm
[Dijkstra][Dijkstra1959] [Cormen et al., Section 24.3][CLRS2009].

An instance (`Cslib.Algorithms.WordRAM.Dijkstra.Instance`) is a directed graph on `Fin n` with
natural-number edge weights, given by its weight matrix, and a source vertex. The distance
`Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist` is the infimum, in `ℕ∞`, of the weights of the
paths (`Quiver.Path`, `Quiver.Path.addWeight`) between two vertices; it is `⊤` when there is no
path. A program writes a distance as a word with `0` for an unreachable vertex and `d + 1` for
distance `d` (`Cslib.Algorithms.WordRAM.Dijkstra.encodeDist`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.Instance`: a weighted directed graph with a source.
* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist`: the shortest-path distance.
* `Cslib.Algorithms.WordRAM.Dijkstra.encodeDist`: a distance as a word.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist_self`: every vertex is at distance `0` from
  itself.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

/-- An instance of the **single-source shortest-path problem**: a directed graph on `Fin n` with
natural-number edge weights, given by its weight matrix, and a source vertex. The entry
`weight u v` is `some c` for an edge from `u` to `v` of weight `c`, and `none` for no edge. -/
structure Instance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The weight matrix. -/
  weight : Fin n → Fin n → Option ℕ
  /-- The source. -/
  source : Fin n

namespace Instance

variable (I : Instance)

/-- The vertices of an instance, as a quiver: an arrow from `u` to `v` is a weight `c` with
`I.weight u v = some c`, so there is at most one. -/
def Vertex : Type := Fin I.n

instance : Quiver I.Vertex where
  Hom u v := {c : ℕ // I.weight u v = some c}

/-- The weight of an arrow. -/
def arrowWeight {u v : I.Vertex} (e : u ⟶ v) : ℕ∞ :=
  (show {c : ℕ // I.weight u v = some c} from e).1

/-- The **shortest-path distance** from `u` to `v`: the infimum of the weights of the paths from
`u` to `v`, and `⊤` when there is none. -/
noncomputable def dist (u v : Fin I.n) : ℕ∞ :=
  ⨅ p : Quiver.Path (V := I.Vertex) u v, p.addWeight I.arrowWeight

/-- Every vertex is at distance `0` from itself, by the empty path. -/
theorem dist_self (u : Fin I.n) : I.dist u u = 0 :=
  le_antisymm (iInf_le_of_le .nil (Quiver.Path.addWeight_nil _ _).le) (by simp)

/-- The largest edge weight, and `0` when there is no edge. -/
def maxWeight : ℕ :=
  Finset.univ.sup fun uv : Fin I.n × Fin I.n => (I.weight uv.1 uv.2).getD 0

end Instance

/-- A distance as a word: `0` for an unreachable vertex and `d + 1` for distance `d`. -/
def encodeDist (d : ℕ∞) : ℕ := if d = ⊤ then 0 else d.toNat + 1

end Cslib.Algorithms.WordRAM.Dijkstra
