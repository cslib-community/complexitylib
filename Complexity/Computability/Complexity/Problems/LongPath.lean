/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# k-Path

`Cslib.Complexity.LongPath` is the decision version of *Longest Path* with the length as parameter
[CyganEtAl2015, Section 5.2]: the pairs `(G, k)` such that the graph `G` has a simple path on `k` of
its declared vertices. A path is a duplicate-free list of declared vertices in which consecutive
vertices are adjacent (`Cslib.Complexity.Graph.IsVertexPath`); for `k = k' + 1` these are the paths
of length `k'` of Mathlib's `SimpleGraph.Walk` on the induced graph
(`Cslib.Complexity.mem_LongPath_succ_iff`). The target `k = 0` is accepted by the empty path.

## Main definitions

* `Cslib.Complexity.Graph.IsVertexPath`: a path given by its list of vertices.
* `Cslib.Complexity.LongPath`: graphs with a path on `k` vertices.

## Main results

* `Cslib.Complexity.Graph.IsVertexPath.length_le`: a path has at most as many vertices as the
  distinct declared vertices.
* `Cslib.Complexity.mem_LongPath_succ_iff`: `(G, k + 1) ∈ LongPath` exactly when the induced graph
  has a path (`SimpleGraph.Walk.IsPath`) of length `k`.

## References

* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Complexity

namespace Graph

/-- `p` is a path of `G`: a list of declared vertices without repetitions in which consecutive
vertices are adjacent. -/
@[expose]
def IsVertexPath (G : Graph) (p : List ℕ) : Prop :=
  p.Nodup ∧ (∀ v ∈ p, v ∈ G.1) ∧ p.IsChain G.toSimpleGraph.Adj

/-- A path has at most as many vertices as the distinct declared vertices. -/
theorem IsVertexPath.length_le {G : Graph} {p : List ℕ} (hp : G.IsVertexPath p) :
    p.length ≤ G.distinctVertices.length := by
  rw [length_distinctVertices, ← List.toFinset_card_of_nodup hp.1]
  exact Finset.card_le_card fun v hv => List.mem_toFinset.2 (hp.2.1 v (List.mem_toFinset.1 hv))

/-- The empty list is a path. -/
@[simp]
theorem isVertexPath_nil (G : Graph) : G.IsVertexPath [] :=
  ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil, List.isChain_nil⟩

end Graph

/-- **k-Path** (the decision version of *Longest Path*) [CyganEtAl2015, Section 5.2]: the pairs
`(G, k)` such that `G` has a path on `k` vertices. -/
@[expose]
def LongPath : Set (Graph × ℕ) :=
  {x | ∃ p : List ℕ, x.1.IsVertexPath p ∧ p.length = x.2}

theorem mem_LongPath_iff {G : Graph} {k : ℕ} :
    (G, k) ∈ LongPath ↔ ∃ p : List ℕ, G.IsVertexPath p ∧ p.length = k := Iff.rfl

/-- Every graph has a path on no vertices. -/
theorem mem_LongPath_zero (G : Graph) : (G, 0) ∈ LongPath := ⟨[], G.isVertexPath_nil, rfl⟩

/-- A graph has no path on more vertices than its distinct declared vertices. -/
theorem not_mem_LongPath_of_lt {G : Graph} {k : ℕ} (hk : G.distinctVertices.length < k) :
    (G, k) ∉ LongPath := fun ⟨_, hp, hlen⟩ =>
  absurd (hlen.symm.trans_le hp.length_le) (Nat.not_le.2 hk)

/-- **Paths on `k + 1` vertices are paths of length `k`** of Mathlib's `SimpleGraph.Walk` on the
induced graph. -/
theorem mem_LongPath_succ_iff {G : Graph} {k : ℕ} :
    (G, k + 1) ∈ LongPath ↔
      ∃ (u v : {v // v ∈ G.1}) (w : G.induced.Walk u v), w.IsPath ∧ w.length = k := by
  rw [mem_LongPath_iff]
  constructor
  · rintro ⟨p, ⟨hnd, hV, hch⟩, hlen⟩
    have hLne : p.pmap (fun a ha => (⟨a, ha⟩ : {v // v ∈ G.1})) hV ≠ [] := by
      grind [List.pmap_eq_nil_iff]
    have hLch := List.isChain_pmap_of_isChain (S := G.induced.Adj)
      (f := fun a ha => (⟨a, ha⟩ : {v // v ∈ G.1})) (fun _ _ _ _ hab => hab) hch hV
    refine ⟨_, _, SimpleGraph.Walk.ofSupport _ hLne hLch, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_ofSupport]
      exact hnd.pmap fun _ _ _ _ hab => congrArg Subtype.val hab
    · rw [SimpleGraph.Walk.length_ofSupport, List.length_pmap, hlen]
      rfl
  · rintro ⟨u, v, w, hw, hlen⟩
    refine ⟨w.support.map Subtype.val, ⟨hw.support_nodup.map Subtype.val_injective,
      fun x hx => ?_, ?_⟩, ?_⟩
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact y.2
    · exact List.isChain_map_of_isChain (S := G.toSimpleGraph.Adj) Subtype.val
        (fun _ _ hab => hab) w.isChain_adj_support
    · rw [List.length_map, SimpleGraph.Walk.length_support, hlen]

end Cslib.Complexity
