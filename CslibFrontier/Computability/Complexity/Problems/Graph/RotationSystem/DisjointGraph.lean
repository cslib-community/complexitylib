/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Relabel
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Disjoint union of actual listed multigraphs

Even names tag the left graph and odd names tag the right graph. Declarations and indexed
edges are concatenated without deduplication. The dart equivalence preserves each old end
and left-then-right edge order. No scan is funded by the magnitude of a vertex name.
-/

public section

namespace Cslib.Complexity.Graph

/-- Disjoint parity-tagged copies, with all left declarations and edges before all right
declarations and edges. Duplicate declarations, loops, parallel edges and points survive. -/
@[expose] def disjointUnion (G H : Graph) : Graph :=
  ⟨(G.vertices.map (fun v => 2 * v)) ++ H.vertices.map (fun v => 2 * v + 1),
    (G.edges.map (fun e => (2 * e.1, 2 * e.2))) ++
      H.edges.map (fun e => (2 * e.1 + 1, 2 * e.2 + 1))⟩

/-- The complete indexed dart sum, retaining all old edge ends in concatenation order. -/
@[expose] def disjointDartEquiv (G H : Graph) :
    Dart G ⊕ Dart H ≃ Dart (G.disjointUnion H) :=
  (Equiv.sumProdDistrib (Fin G.edges.length) (Fin H.edges.length) Bool).symm.trans
    ((finSumFinEquiv.prodCongr (Equiv.refl Bool)).trans
      ((finCongr (by simp only [disjointUnion, List.length_append, List.length_map])).prodCongr
        (Equiv.refl Bool)))

/-- Left indexed ends occupy the unchanged edge-list prefix. -/
theorem disjointDartEquiv_inl (G H : Graph) (d : Dart G) :
    disjointDartEquiv G H (Sum.inl d) =
      (⟨d.1.val, by simpa only [disjointUnion, List.length_append, List.length_map] using
        (Nat.lt_add_right H.edges.length d.1.isLt)⟩, d.2) := rfl

/-- Right indexed ends follow exactly the old left edge count. -/
theorem disjointDartEquiv_inr (G H : Graph) (d : Dart H) :
    disjointDartEquiv G H (Sum.inr d) =
      (⟨G.edges.length + d.1.val, by
        simpa only [disjointUnion, List.length_append, List.length_map] using
          Nat.add_lt_add_left d.1.isLt G.edges.length⟩, d.2) := rfl

/-- Actual left endpoints carry the even tag, including both ends of a loop. -/
theorem vertex_disjointDartEquiv_inl (G H : Graph) (d : Dart G) :
    (disjointDartEquiv G H (Sum.inl d)).vertex = 2 * d.vertex := by
  rw [disjointDartEquiv_inl]
  change (if d.2 then ((G.disjointUnion H).edges.getD d.1.val (0, 0)).2 else
    ((G.disjointUnion H).edges.getD d.1.val (0, 0)).1) = 2 * d.vertex
  simp only [disjointUnion]
  rw [List.getD_eq_getElem _ _ (by
    simpa only [disjointUnion, List.length_append, List.length_map] using
      Nat.lt_add_right H.edges.length d.1.isLt)]
  rw [List.getElem_append_left (by simpa only [List.length_map] using d.1.isLt),
    List.getElem_map]
  change (if d.2 then 2 * G.edges[d.1.val].2 else 2 * G.edges[d.1.val].1) =
    2 * (if d.2 then (G.edges.getD d.1.val (0, 0)).2 else (G.edges.getD d.1.val (0, 0)).1)
  rw [List.getD_eq_getElem _ _ d.1.isLt]
  cases d.2 <;> rfl

/-- Actual right endpoints carry the odd tag, irrespective of sparse binary labels. -/
theorem vertex_disjointDartEquiv_inr (G H : Graph) (d : Dart H) :
    (disjointDartEquiv G H (Sum.inr d)).vertex = 2 * d.vertex + 1 := by
  rw [disjointDartEquiv_inr]
  change (if d.2 then ((G.disjointUnion H).edges.getD (G.edges.length + d.1.val) (0, 0)).2 else
    ((G.disjointUnion H).edges.getD (G.edges.length + d.1.val) (0, 0)).1) = 2 * d.vertex + 1
  simp only [disjointUnion]
  rw [List.getD_eq_getElem _ _ (by
    simpa only [disjointUnion, List.length_append, List.length_map] using
      Nat.add_lt_add_left d.1.isLt G.edges.length)]
  rw [List.getElem_append_right (by simp only [List.length_map]; omega), List.getElem_map]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  change (if d.2 then 2 * H.edges[d.1.val].2 + 1 else 2 * H.edges[d.1.val].1 + 1) =
    2 * (if d.2 then (H.edges.getD d.1.val (0, 0)).2 else (H.edges.getD d.1.val (0, 0)).1) + 1
  rw [List.getD_eq_getElem _ _ d.1.isLt]
  cases d.2 <;> rfl

/-- Parity tagging retains all old edge reversals in their respective indexed blocks. -/
theorem reverse_disjointDartEquiv (G H : Graph) (d : Dart G ⊕ Dart H) :
    disjointDartEquiv G H (Sum.map Dart.reverse Dart.reverse d) =
      (disjointDartEquiv G H d).reverse := by
  cases d <;> rfl

/-- Endpoint declaration is inherited from the corresponding source graph. -/
theorem endpoints_declared_disjointUnion (G H : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.vertices) :
    ∀ v ∈ (G.disjointUnion H).incidenceVertices, v ∈ (G.disjointUnion H).vertices := by
  intro v hv
  obtain ⟨edge, he, hv⟩ := List.mem_flatMap.mp hv
  rcases List.mem_append.mp he with he | he
  · obtain ⟨old, ho, rfl⟩ := List.mem_map.mp he
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_append_left _ (List.mem_map_of_mem
        (hG old.1 (List.mem_flatMap.mpr ⟨old, ho, by simp⟩)))
    · have hv' : v = 2 * old.2 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hv
      subst v
      exact List.mem_append_left _ (List.mem_map_of_mem
        (hG old.2 (List.mem_flatMap.mpr ⟨old, ho, by simp⟩)))
  · obtain ⟨old, ho, rfl⟩ := List.mem_map.mp he
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_append_right _ (List.mem_map_of_mem
        (hH old.1 (List.mem_flatMap.mpr ⟨old, ho, by simp⟩)))
    · have hv' : v = 2 * old.2 + 1 := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hv
      subst v
      exact List.mem_append_right _ (List.mem_map_of_mem
        (hH old.2 (List.mem_flatMap.mpr ⟨old, ho, by simp⟩)))

end Cslib.Complexity.Graph
