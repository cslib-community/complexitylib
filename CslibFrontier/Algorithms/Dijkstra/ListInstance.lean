/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Dijkstra.Invariant
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Shortest paths on adjacency lists

An instance (`Cslib.Algorithms.Dijkstra.ListInstance`) is a directed graph on `Fin n` given by its
adjacency lists of `(target, weight)` pairs, with natural-number weights, and a source vertex. The
lists may repeat a pair of endpoints (parallel edges) and may contain self-loops. The instance
determines a weight-matrix instance of `Cslib.Algorithms.Dijkstra.Instance` that keeps, for each
pair of endpoints, the lightest of its edges (`Cslib.Algorithms.Dijkstra.ListInstance.toInstance`);
the distance is the distance of that instance [Dijkstra][Dijkstra1959]
[Cormen et al., Section 24.3][CLRS2009].

Scanning the edges out of a vertex `u` in list order, and lowering the tentative distance of each
target `v` to that of `u` plus the weight, has the effect of relaxing `u` in the weight-matrix
instance (`Cslib.Algorithms.Dijkstra.ListInstance.relaxEdges_eq_relax`): the scan of all parallel
edges to `v` has the effect of the lightest one. Nothing here refers to a machine: the interface
client (`CslibFrontier.Algorithms.Lean.Dijkstra.Client`) uses this directly, and the word-RAM
statements (`CslibFrontier.Algorithms.WordRAM.Dijkstra.HeapStatement`) add the input words.

## Main definitions

* `Cslib.Algorithms.Dijkstra.ListInstance`: a directed graph by adjacency lists, with a source.
* `Cslib.Algorithms.Dijkstra.ListInstance.toInstance`: its weight-matrix instance.
* `Cslib.Algorithms.Dijkstra.ListInstance.dist`: the shortest-path distance.
* `Cslib.Algorithms.Dijkstra.ListInstance.relaxEdges`: the tentative distance of a vertex after
  scanning a list of edges.

## Main results

* `Cslib.Algorithms.Dijkstra.ListInstance.lightest_eq_some_iff`: the matrix entry of a pair of
  endpoints is the least weight of the edges between them.
* `Cslib.Algorithms.Dijkstra.ListInstance.lightest_eq_none_iff`: it is absent exactly when there is
  no such edge.
* `Cslib.Algorithms.Dijkstra.ListInstance.toInstance_maxWeight_le`: the largest weight of the
  matrix instance is at most the largest edge weight.
* `Cslib.Algorithms.Dijkstra.ListInstance.relaxEdges_eq_relax`: scanning the edges out of `u`
  relaxes the tentative distances.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Dijkstra

/-- An instance of the single-source shortest-path problem by **adjacency lists**: a
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
`Cslib.Algorithms.Dijkstra.Instance.dist`. -/
noncomputable def dist (u v : Fin G.n) : ℕ∞ :=
  G.toInstance.dist u v

/-- The number of edges. -/
def m : ℕ := ∑ u, (G.adj u).length

/-- The largest edge weight, and `0` when there is no edge. -/
def maxWeight : ℕ :=
  Finset.univ.sup fun u => ((G.adj u).map Prod.snd).foldr max 0

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

/-- Every edge weight is at most the largest weight. -/
theorem le_maxWeight {u : Fin G.n} {e : Fin G.n × ℕ} (he : e ∈ G.adj u) : e.2 ≤ G.maxWeight := by
  have h1 : e.2 ≤ ((G.adj u).map Prod.snd).foldr max 0 :=
    List.le_max_of_le (List.mem_map_of_mem he) le_rfl
  exact h1.trans (Finset.le_sup (f := fun u => ((G.adj u).map Prod.snd).foldr max 0)
    (Finset.mem_univ u))

/-- The largest weight of the weight-matrix instance is at most the largest edge weight. -/
theorem toInstance_maxWeight_le : G.toInstance.maxWeight ≤ G.maxWeight := by
  refine Finset.sup_le fun uv _ => ?_
  change (G.lightest uv.1 uv.2).getD 0 ≤ G.maxWeight
  cases h : G.lightest uv.1 uv.2 with
  | none => simp
  | some c => exact G.le_maxWeight ((G.lightest_eq_some_iff.mp h).1)

/-- The tentative distance `d` of `v` after scanning the edges of `es` in order from a vertex at
tentative distance `b`: each edge `(v, c)` lowers it to at most `b + c`. -/
noncomputable def relaxEdges {N : ℕ} (b : ℕ∞) (es : List (Fin N × ℕ)) (v : Fin N) (d : ℕ∞) : ℕ∞ :=
  es.foldl (fun d e => if e.1 = v then min d (b + e.2) else d) d

/-- Scanning the edges to `v` in `es` has the effect of the lightest of them. -/
private theorem relaxEdges_eq_match {N : ℕ} (b : ℕ∞) (es : List (Fin N × ℕ)) (v : Fin N)
    (d : ℕ∞) :
    relaxEdges b es v d =
      match (es.filterMap fun e => if e.1 = v then some e.2 else none).min? with
      | none => d
      | some c => min d (b + c) := by
  induction es generalizing d with
  | nil => rfl
  | cons e es ih =>
    rw [relaxEdges, List.foldl_cons, ← relaxEdges, ih]
    by_cases he : e.1 = v
    · simp only [List.filterMap_cons, he, ↓reduceIte, List.min?_cons]
      cases es.filterMap (fun e => if e.1 = v then some e.2 else none) |>.min? with
      | none => rfl
      | some c =>
        simp only [Option.elim_some]
        rw [min_assoc, min_add_add_left, Nat.mono_cast.map_min]
    · simp only [List.filterMap_cons, he, ↓reduceIte]

/-- **Scanning the edges out of `u` relaxes the tentative distances**: from tentative distances
`D`, scanning the list of `u` lowers the tentative distance of `v` to its relaxation in the
weight-matrix instance. -/
theorem relaxEdges_eq_relax (D : Fin G.n → ℕ∞) (u v : Fin G.n) :
    relaxEdges (D u) (G.adj u) v (D v) = G.toInstance.relax D u v := by
  rw [relaxEdges_eq_match]
  rfl

end ListInstance

end Cslib.Algorithms.Dijkstra
