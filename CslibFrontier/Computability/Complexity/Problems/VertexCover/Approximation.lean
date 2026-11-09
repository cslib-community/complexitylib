/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.VertexCover.Matching
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# A polynomial-time 2-approximation for `VertexCover`

The maximal-matching algorithm `Cslib.Algorithms.Lean.VertexCover.matchingCover`, run on the
edges of an encoded graph `G : Graph` between declared vertices, returns a vertex cover with at most
twice the minimum number of vertices, and is computable in polynomial time on `encGraph`
([CLRS2009], Section 35.1, Theorem 35.1).

## Model

`VertexCover` and `Graph.vertexCoverNum` count declared vertices meeting every edge between
declared vertices; edges with an undeclared endpoint and self-loops impose nothing. The algorithm
therefore scans `Cslib.Complexity.VertexCover.declaredEdges G`, the listed edges with both endpoints
declared.

## Main definitions

* `Cslib.Complexity.VertexCover.approxCover`: the matching cover of the declared edges.

## Main results

* `approxCover_mem_VertexCover`: `(G, (approxCover G).length) ∈ VertexCover`, with
  `nodup_approxCover` and `isCover_approxCover` for the list itself.
* `length_approxCover_le_two_mul_vertexCoverNum`: `(approxCover G).length ≤ 2 * G.vertexCoverNum`.
* `computableInPolyTime_approxCover`: the algorithm is polynomial-time from `encGraph` to framed
  binary vertex lists.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 35.1.
-/

public section

namespace Cslib.Complexity.VertexCover

open Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Algorithms.Lean.VertexCover

/-- **The maximal-matching approximation** for `VertexCover`: both endpoints of each edge of a
greedy maximal matching of the edges between declared vertices. -/
@[expose] def approxCover (G : Graph) : List ℕ :=
  matchingCover (declaredEdges G)

/-- The returned vertices are distinct. -/
theorem nodup_approxCover (G : Graph) : (approxCover G).Nodup :=
  nodup_matchingCover _

/-- The returned vertices are declared. -/
theorem mem_vertices_of_mem_approxCover {G : Graph} {v : ℕ} (hv : v ∈ approxCover G) :
    v ∈ G.1 := by
  obtain ⟨e, he, rfl | rfl⟩ := mem_matchingCover hv
  · exact (mem_declaredEdges.1 he).2.1
  · exact (mem_declaredEdges.1 he).2.2

/-- Between declared vertices, the graph of the declared edges is the graph of `G`. -/
theorem fromRel_declaredEdges_adj {G : Graph} {u v : ℕ} (hu : u ∈ G.1) (hv : v ∈ G.1) :
    (SimpleGraph.fromRel fun a b => (a, b) ∈ declaredEdges G).Adj u v ↔
      G.toSimpleGraph.Adj u v := by
  simp only [SimpleGraph.fromRel_adj, Graph.toSimpleGraph, mem_declaredEdges]
  tauto

/-- **Feasibility.** The returned vertices meet every edge between declared vertices. -/
theorem isCover_approxCover (G : Graph) :
    ∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ approxCover G ∨ v ∈ approxCover G :=
  fun _ hu _ hv huv => isVertexCover_matchingCover _ ((fromRel_declaredEdges_adj hu hv).2 huv)

/-- The returned list is a vertex cover of its length. -/
theorem approxCover_mem_VertexCover (G : Graph) : (G, (approxCover G).length) ∈ VertexCover :=
  mem_VertexCover_iff.2 ⟨(approxCover G).toFinset,
    fun _ hv => mem_vertices_of_mem_approxCover (List.mem_toFinset.1 hv),
    fun u hu v hv huv => (isCover_approxCover G u hu v hv huv).imp List.mem_toFinset.2
      List.mem_toFinset.2,
    List.toFinset_card_of_nodup (nodup_approxCover G)⟩

/-- **The 2-approximation** ([CLRS2009], Theorem 35.1): the returned cover has at most twice the
minimum number of vertices of a cover. -/
theorem length_approxCover_le_two_mul_vertexCoverNum (G : Graph) :
    (approxCover G).length ≤ 2 * G.vertexCoverNum := by
  obtain ⟨S, hSV, hS, hcard⟩ := mem_VertexCover_iff.1 (G.vertexCoverNum_mem_VertexCover)
  rw [← hcard]
  refine length_matchingCover_le_two_mul_card _ fun u v huv => ?_
  have hdecl : u ∈ G.1 ∧ v ∈ G.1 := by
    rw [SimpleGraph.fromRel_adj] at huv
    rcases huv.2 with he | he
    · exact ⟨(mem_declaredEdges.1 he).2.1, (mem_declaredEdges.1 he).2.2⟩
    · exact ⟨(mem_declaredEdges.1 he).2.2, (mem_declaredEdges.1 he).2.1⟩
  exact hS u hdecl.1 v hdecl.2 ((fromRel_declaredEdges_adj hdecl.1 hdecl.2).1 huv)

/-! ### Polynomial time -/

/-- One step of the cover scan is polynomial-time. -/
@[local fun_prop]
private theorem computableInPolyTime_coverStep :
    ComputableInPolyTime (fun p : List ℕ × (ℕ × ℕ) => coverStep p.1 p.2)
      (encPair (encList encNat) (encPair encNat encNat)) (encList encNat) := by
  unfold coverStep
  fun_prop

/-- One step of the cover scan over a declared edge adds at most `4 * |encGraph G| + 2` bits. -/
private theorem length_encList_coverStep_le {G : Graph} (C : List ℕ) {e : ℕ × ℕ}
    (he : e ∈ declaredEdges G) :
    (encList encNat (coverStep C e)).length ≤
      (encList encNat C).length + (4 * (encGraph G).length + 2) := by
  obtain ⟨-, h1, h2⟩ := mem_declaredEdges.1 he
  have hV : (encList encNat G.1).length ≤ (encGraph G).length := by
    simp only [encGraph, length_encPair]
    omega
  have h1 := (length_le_encList_of_mem encNat h1).trans hV
  have h2 := (length_le_encList_of_mem encNat h2).trans hV
  unfold coverStep
  split_ifs
  · simp only [length_encList, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega
  · omega

/-- **The 2-approximation is polynomial-time**: `approxCover` is computable in polynomial time from
`encGraph` to framed binary vertex lists. -/
@[fun_prop]
theorem computableInPolyTime_approxCover :
    ComputableInPolyTime approxCover encGraph (encList encNat) := by
  have heq : approxCover = fun G => (declaredEdges G).foldl (fun C e => coverStep C e) [] := by
    funext G
    exact matchingCover_eq_foldl_coverStep _
  rw [heq]
  exact foldlWithInput_of_bounded_growth (encA := encPair encNat encNat)
    (encL := encList (encPair encNat encNat)) (step := fun _ C e => coverStep C e)
    (const []) ⟨computableInPolyTime_declaredEdges, by fun_prop, inferInstance, inferInstance⟩
    ⟨((PolyBounded.const 4).mul .self).add (.const 2),
      fun _ C _ he => length_encList_coverStep_le C he⟩

end Cslib.Complexity.VertexCover
