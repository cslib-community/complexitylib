/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.VertexMergeGenus
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletion

/-!
# Directed contraction of an indexed nonloop edge

The last edge's first endpoint is identified with its second endpoint. The two vertex
cycles are spliced at the actual edge ends and those ends are then removed. This retains
the direction of the two remaining cyclic blocks, even if one block is empty, and redirects
every other loop or parallel edge positionally. No bridge or cofacial hypothesis is used.
These are original permutation constructions on the existing listed graph model.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv Perm.CycleSurgery

/-- Remove the last edge and replace its first endpoint's name by its second throughout
the retained graph. Declared points and repeated edge occurrences are retained. -/
@[expose] def contractLastEdgeGraph (G : Graph) (u v : ℕ) : Graph :=
  G.relabel (Function.update id u v)

private theorem lastEdge_vertices_ne (G : Graph) (u v : ℕ) (huv : u ≠ v) :
    (lastEdgeDart G u v true).vertex ≠ (lastEdgeDart G u v false).vertex := by
  rw [vertex_lastEdgeDart, vertex_lastEdgeDart]
  exact huv.symm

/-- The intermediate corner splice turns the selected edge into a loop at the retained
endpoint. This is literal equality of the listed graphs, including all declared points. -/
theorem mergeGraph_lastEdgeDart (G : Graph) (u v : ℕ) :
    mergeGraph (lastEdgeDart G u v true) (lastEdgeDart G u v false) =
      lastEdgeGraph (contractLastEdgeGraph G u v) v v := by
  unfold mergeGraph
  rw [vertex_lastEdgeDart, vertex_lastEdgeDart]
  change (G.1.map (Function.update id u v),
    (G.2 ++ [(u, v)]).map (Prod.map (Function.update id u v) (Function.update id u v))) = _
  simp [lastEdgeGraph, contractLastEdgeGraph, Graph.relabel, Function.update_apply]

/-- Reinterpret the actual corner splice as a graph with one final loop. No numerical
genus premise is imposed on this intermediate rotation. -/
@[expose] def contractLastEdgeSplice {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    RotationSystem (lastEdgeGraph (contractLastEdgeGraph G u v) v v) :=
  (r.mergeVertices (lastEdgeDart G u v true) (lastEdgeDart G u v false)
    (by exact lastEdge_vertices_ne G u v huv)).transport
    (graphEqDartEquiv (mergeGraph_lastEdgeDart G u v)) (by
      intro a b
      rw [vertex_graphEqDartEquiv, vertex_graphEqDartEquiv])

/-- Contract an actual nonloop edge by directed vertex splicing followed by removal of
its two ends. The construction applies to arbitrary nonloop edges, including nonbridges. -/
@[expose] def contractLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    RotationSystem (contractLastEdgeGraph G u v) :=
  (r.contractLastEdgeSplice huv).deleteLastEdge

/-- Old edge ends retain their original index and end tag during the preliminary splice. -/
@[expose] def contractLastEdgeDartEquiv (G : Graph) (u v : ℕ) :
    Dart (lastEdgeGraph G u v) ≃
      Dart (lastEdgeGraph (contractLastEdgeGraph G u v) v v) :=
  (mergeDartEquiv (lastEdgeDart G u v true) (lastEdgeDart G u v false)).trans
    (graphEqDartEquiv (mergeGraph_lastEdgeDart G u v))

/-- Literal successor of the preliminary splice: the outgoing successors of the two
selected ends are exchanged, with no reversal of either remaining block. -/
theorem rotate_contractLastEdgeSplice {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    (r.contractLastEdgeSplice huv).rotate = (contractLastEdgeDartEquiv G u v).permCongr
      (r.rotate * swap (lastEdgeDart G u v true) (lastEdgeDart G u v false)) := by
  rfl

/-- Literal retained rotation after directed nonloop contraction. -/
theorem rotate_contractLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    (r.contractLastEdge huv).rotate = removeNone (removeNone
      (((contractLastEdgeDartEquiv G u v).trans
        (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)).permCongr
          (r.rotate * swap (lastEdgeDart G u v true) (lastEdgeDart G u v false)))) := by
  rfl

/-- The splice changes exactly the selected endpoint name at each actual dart. -/
theorem vertex_contractLastEdgeDartEquiv (G : Graph) (u v : ℕ)
    (d : Dart (lastEdgeGraph G u v)) :
    (contractLastEdgeDartEquiv G u v d).vertex = Function.update id u v d.vertex := by
  rw [contractLastEdgeDartEquiv, Equiv.trans_apply, vertex_graphEqDartEquiv,
    vertex_mergeDartEquiv, vertex_lastEdgeDart, vertex_lastEdgeDart]
  rfl

/-- The preliminary splice retains the original edge reversal. -/
theorem reverse_contractLastEdgeDartEquiv (G : Graph) (u v : ℕ)
    (d : Dart (lastEdgeGraph G u v)) :
    contractLastEdgeDartEquiv G u v d.reverse = (contractLastEdgeDartEquiv G u v d).reverse := by
  rw [contractLastEdgeDartEquiv, Equiv.trans_apply, Equiv.trans_apply,
    mergeDartEquiv_reverse, reverse_graphEqDartEquiv]

/-- The retained and removed coordinates are literal: old edge/end positions map
pointwise, and the two deleted ends keep their tags. -/
theorem contractLastEdge_coordinates (G : Graph) (u v : ℕ) :
    (contractLastEdgeDartEquiv G u v).trans
        (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v) =
      (lastEdgeDartEquiv G u v).trans
        (Dart.relabelEquiv G (Function.update id u v)).optionCongr.optionCongr := by
  apply Equiv.ext
  rintro ⟨⟨i, hi⟩, b⟩
  change (if h : i < (contractLastEdgeGraph G u v).2.length then
      some (some (⟨i, h⟩, b)) else if b then none else some none) =
    (Dart.relabelEquiv G (Function.update id u v)).optionCongr.optionCongr
      (if h : i < G.2.length then some (some (⟨i, h⟩, b))
        else if b then none else some none)
  by_cases h : i < G.2.length
  · have he : i < (contractLastEdgeGraph G u v).2.length := by
      simpa only [contractLastEdgeGraph, Graph.relabel, List.length_map] using h
    rw [dite_eq_left he, dite_eq_left h]
    rfl
  · have he : ¬i < (contractLastEdgeGraph G u v).2.length := by
      simpa only [contractLastEdgeGraph, Graph.relabel, List.length_map] using h
    rw [dite_eq_right he, dite_eq_right h]
    cases b <;> rfl

/-- The face successor after the preliminary vertex splice has one incoming swap. -/
theorem faceNext_contractLastEdgeSplice {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    (r.contractLastEdgeSplice huv).faceNext = (contractLastEdgeDartEquiv G u v).permCongr
      (swap (lastEdgeDart G u v true) (lastEdgeDart G u v false) * r.faceNext) := by
  apply Equiv.ext
  intro d
  obtain ⟨a, rfl⟩ := (contractLastEdgeDartEquiv G u v).surjective d
  let h := lastEdgeDart G u v true
  let k := lastEdgeDart G u v false
  let e := graphEqDartEquiv (mergeGraph_lastEdgeDart G u v)
  have ht := (r.mergeVertices h k (by exact lastEdge_vertices_ne G u v huv)).faceNext_transport e
    (by intro a b; rw [vertex_graphEqDartEquiv, vertex_graphEqDartEquiv])
    (reverse_graphEqDartEquiv _) (mergeDartEquiv h k a)
  rw [faceNext_mergeVertices] at ht
  exact ht.symm

/-- In retained-plus-two-removed coordinates the selected ends remain the two removed
points, including when the retained graph has no darts. -/
theorem contractLastEdge_coordinates_last (G : Graph) (u v : ℕ) (b : Bool) :
    ((contractLastEdgeDartEquiv G u v).trans
      (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)) (lastEdgeDart G u v b) =
        if b then none else some none := by
  rw [contractLastEdge_coordinates]
  change (Dart.relabelEquiv G (Function.update id u v)).optionCongr.optionCongr
    ((lastEdgeDartEquiv G u v) ((lastEdgeDartEquiv G u v).symm
      (if b then none else some none))) = _
  rw [Equiv.apply_symm_apply]
  cases b <;> rfl

/-- Exact face successor of nonloop contraction. The incoming and outgoing swaps
conjugate the original face permutation at the two removed ends before deleting them.
Both swaps are derived from the actual directed splice, rather than assumed face counts. -/
theorem faceNext_contractLastEdge {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
    (r.contractLastEdge huv).faceNext = removeNone (removeNone
      (swap (some none) none * (((contractLastEdgeDartEquiv G u v).trans
        (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)).permCongr r.faceNext) *
          swap (some none) none)) := by
  rw [contractLastEdge, faceNext_deleteLastEdge, faceNext_contractLastEdgeSplice]
  let e := (contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)
  change removeNone (removeNone (e.permCongr
    (swap (lastEdgeDart G u v true) (lastEdgeDart G u v false) * r.faceNext) *
      swap (some none) none)) = _
  rw [Equiv.permCongr_mul]
  have hs : e.permCongr (swap (lastEdgeDart G u v true) (lastEdgeDart G u v false)) =
      swap (some none) none := by
    apply Equiv.ext
    intro z
    rw [Equiv.permCongr_apply, e.injective.map_swap, Equiv.apply_symm_apply]
    simp only [e, contractLastEdge_coordinates_last, ↓reduceIte]
    exact congrArg (fun p : Perm (Option (Option (Dart (contractLastEdgeGraph G u v)))) =>
      p z) (swap_comm none (some none))
  rw [hs]

end Cslib.Complexity.Graph.RotationSystem
