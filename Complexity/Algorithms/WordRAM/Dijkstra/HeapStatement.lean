/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.Statement
public import Complexity.Computability.WordRAM.Time

/-!
# Dijkstra's algorithm on the word RAM with adjacency lists: statements

This file states, without proof, what a single-source shortest-path program on the word RAM
must satisfy to run in `O((m + 1) log n)` time on a graph with `n` vertices and `m` edges, the
bound of Dijkstra's algorithm with a binary heap [Dijkstra][Dijkstra1959]
[Cormen et al., Section 24.3][CLRS2009]. The bound has no `n` term: memory past the input starts
at `0`, so the per-vertex arrays need no initialization, and the offsets give the adjacency list
of any vertex directly, so the program touches only the vertices it reaches.

An instance (`Cslib.Algorithms.WordRAM.Dijkstra.ListInstance`) is a directed graph on `Fin n`
given by its adjacency lists of `(target, weight)` pairs, with natural-number weights, and a
source vertex. The lists may repeat a pair of endpoints (parallel edges) and may contain
self-loops. The instance determines a weight-matrix instance of
`Cslib.Algorithms.WordRAM.Dijkstra.Instance` that keeps, for each pair of endpoints, the
lightest of its edges (`Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.toInstance`); the distance
is the distance of that instance.

The program reads the input words `n`, the source, the `n + 1` offsets of the adjacency lists in
the edge array, and the edges in order, each as two words, its target and its weight. When it
halts, the `n` memory cells just past the input hold the distances from the source, with `0` for
an unreachable vertex and `d + 1` for distance `d`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance`: a directed graph by adjacency lists, with a
  source.
* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.toInstance`: its weight-matrix instance.
* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.encode`: its input words.
* `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec`: a flat program computes every distance from
  the source within `K (m + 1) (⌊log₂ n⌋ + 1)` instructions.
* `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearStatement`: some program meets `LogLinearSpec`.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.lightest_eq_some_iff`: the matrix entry of a
  pair of endpoints is the least weight of the edges between them.
* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.lightest_eq_none_iff`: it is absent exactly
  when there is no such edge.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

/-- An instance of the **single-source shortest-path problem** given by adjacency lists: a
directed graph on `Fin n` and a source vertex. The list `adj u` holds a pair `(v, c)` for each
edge from `u` to `v` of weight `c`; it may hold several pairs with the same `v`. -/
structure ListInstance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency lists. -/
  adj : Fin n → List (Fin n × ℕ)
  /-- The source. -/
  source : Fin n

namespace ListInstance

variable (G : ListInstance)

/-- The least weight of an edge from `u` to `v`, and `none` when there is no such edge. -/
def lightest (u v : Fin G.n) : Option ℕ :=
  ((G.adj u).filterMap fun e => if e.1 = v then some e.2 else none).min?

/-- The weight-matrix instance with the same vertices and source, whose entry for `u` and `v` is
the least weight of an edge from `u` to `v`. Keeping a lightest edge between each pair preserves
distances. -/
def toInstance : Instance where
  n := G.n
  weight := G.lightest
  source := G.source

/-- The **shortest-path distance** from `u` to `v`: the distance of the weight-matrix instance,
`Cslib.Algorithms.WordRAM.Dijkstra.Instance.dist`. -/
noncomputable def dist (u v : Fin G.n) : ℕ∞ :=
  G.toInstance.dist u v

/-- The number of edges. -/
def m : ℕ := ∑ u, (G.adj u).length

/-- The largest edge weight, and `0` when there is no edge. -/
def maxWeight : ℕ :=
  Finset.univ.sup fun u => ((G.adj u).map Prod.snd).foldr max 0

/-- The offset of the adjacency list of vertex `u` in the edge array: the number of edges out of
the vertices below `u`. The offset of `n` is the number `m` of edges. -/
def offset (u : ℕ) : ℕ :=
  (((List.finRange G.n).take u).map fun x => (G.adj x).length).sum

/-- The input words: `n`, the source, the offsets of the vertices `0, …, n`, and then the edges of
the lists `adj 0, …, adj (n - 1)` in order, each as its target and its weight. Edge `j` in this
order has its target at word `n + 3 + 2 j` and its weight at word `n + 4 + 2 j`, and the edges
out of `u` are those with `offset u ≤ j < offset (u + 1)`. -/
def encode : List ℕ :=
  G.n :: (G.source : ℕ) ::
    ((List.range (G.n + 1)).map G.offset ++
      (List.finRange G.n).flatMap fun u => (G.adj u).flatMap fun e => [(e.1 : ℕ), e.2])

/-- The output address of vertex `v`: the `n` cells just past the input, which has `n + 2 m + 3`
words and so ends at address `n + 2 m + 3`. -/
def outAddr (v : Fin G.n) : ℕ := G.n + 2 * G.m + 4 + v

/-- The matrix entry of `u` and `v` is `c` exactly when `c` is the least weight of an edge from
`u` to `v`. -/
theorem lightest_eq_some_iff {u v : Fin G.n} {c : ℕ} :
    G.lightest u v = some c ↔ (v, c) ∈ G.adj u ∧ ∀ c', (v, c') ∈ G.adj u → c ≤ c' := by
  simp only [lightest, List.min?_eq_some_iff, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.exists]
  constructor
  · rintro ⟨⟨a, b, hab, rfl, rfl⟩, hle⟩
    exact ⟨hab, fun c' hc' => hle c' ⟨a, c', hc', rfl, rfl⟩⟩
  · rintro ⟨hc, hle⟩
    refine ⟨⟨v, c, hc, rfl, rfl⟩, ?_⟩
    rintro b ⟨a, b', hab, rfl, rfl⟩
    exact hle b' hab

/-- The matrix entry of `u` and `v` is absent exactly when there is no edge from `u` to `v`. -/
theorem lightest_eq_none_iff {u v : Fin G.n} :
    G.lightest u v = none ↔ ∀ c, (v, c) ∉ G.adj u := by
  simp only [lightest, List.min?_eq_none_iff, List.filterMap_eq_nil_iff]
  constructor
  · intro h c hc
    simpa using h _ hc
  · rintro h ⟨a, b⟩ hab
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false]
    rintro rfl
    exact h b hab

end ListInstance

/-- **Shortest paths in `O((m + 1) log n)` time.** At every word size `w` that holds
`8 (n + m + 2) (W + 2)`, where `m` is the number of edges and `W` the largest weight, the flat
program `p`, started on the input words of an adjacency-list instance, halts within
`K (m + 1) (⌊log₂ n⌋ + 1)` instructions, the final `halt` included, and its memory then holds at
`G.outAddr v` the encoded distance from the source to `v`, for every vertex `v`. The register
value returned by `halt` is not part of the result. -/
def LogLinearSpec {r : ℕ} (p : Program .exact r) (K : ℕ) : Prop :=
  ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
    ∃ t steps, Runs w p (.init G.encode) t steps ∧ (∃ v, step w p t = .halt v) ∧
      steps + 1 ≤ K * (G.m + 1) * (Nat.log 2 G.n + 1) ∧
      ∀ v : Fin G.n, t.data.mem (G.outAddr v) = encodeDist (G.dist G.source v)

/-- **Log-linear main theorem (statement).** Some word-RAM program over the exact basis computes
all shortest-path distances from the source of a weighted directed graph with `n` vertices and
`m` edges, given by adjacency lists, within `O((m + 1) log n)` instructions. -/
def LogLinearStatement : Prop :=
  ∃ r, ∃ p : Program .exact r, ∃ K, LogLinearSpec p K

end Cslib.Algorithms.WordRAM.Dijkstra
