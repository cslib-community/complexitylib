/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.Ports
public import Complexity.Foundations.Geometry.Orthogonal.Layout
import Mathlib.Data.List.GetD

/-!
# Finite orthogonal routes indexed by the existing graph edge list

No new graph representation is introduced. Positions follow `G.1` and routes follow `G.2`, so
every edge occurrence keeps its original index, including parallel edge occurrences. The input
port table is a finite list assigning a pair of three-way ports to each edge occurrence.

## Main definitions

* `Cslib.Complexity.Graph.orthogonalPositions`: finite list of diagonal vertex positions.
* `Cslib.Complexity.Graph.orthogonalRoutes`: finite list of routes in edge-list order.

## Main results

* `Cslib.Complexity.Graph.orthogonalRoutes_endpoints`: each indexed route has the actual edge's
  endpoint positions.
* `Cslib.Complexity.Graph.orthogonalRoutes_wireLength_le`: explicit quadratic total wire bound.
-/

@[expose] public section

namespace Cslib.Complexity.Graph

open Orthogonal

/-- Vertex positions indexed by the existing declared vertex list. -/
def orthogonalPositions (G : Graph) : List Point :=
  (List.range G.1.length).map Layout.center

/-- The finite route list, in exactly the order of the graph's edge occurrences.
A missing port-table entry defaults to the left port at both ends. Contact separation requires
that the supplied table assigns distinct ports to different incidences. -/
def orthogonalRoutes (G : Graph) (ports : List (Fin 3 × Fin 3)) : List Route :=
  G.2.zipIdx.map fun (edge, i) =>
    Layout.route G.1.length i (G.1.idxOf edge.1) (G.1.idxOf edge.2)
      (ports.getD i (0, 0)).1 (ports.getD i (0, 0)).2

/-- The output lists have the original vertex and edge counts. -/
@[simp] theorem orthogonalPositions_length (G : Graph) :
    G.orthogonalPositions.length = G.1.length := by simp [orthogonalPositions]

/-- The output lists have the original vertex and edge counts. -/
@[simp] theorem orthogonalRoutes_length (G : Graph) (ports : List (Fin 3 × Fin 3)) :
    (G.orthogonalRoutes ports).length = G.2.length := by simp [orthogonalRoutes]

/-- The route at index `i` is the route for the edge at the same index. -/
theorem getElem_orthogonalRoutes (G : Graph) (ports : List (Fin 3 × Fin 3))
    {i : ℕ} (hi : i < G.2.length) :
    (G.orthogonalRoutes ports)[i]'(by simpa using hi) =
      Layout.route G.1.length i (G.1.idxOf G.2[i].1) (G.1.idxOf G.2[i].2)
        (ports.getD i (0, 0)).1 (ports.getD i (0, 0)).2 := by
  simp [orthogonalRoutes, List.getElem_zipIdx]

/-- A side-indexed version of the exact route formula. -/
theorem getElem_orthogonalRoutes_endpoint (G : Graph) (ports : List (Fin 3 × Fin 3))
    {i : ℕ} (hi : i < G.2.length) :
    (G.orthogonalRoutes ports)[i]'(by simpa using hi) =
      Layout.route G.1.length i (G.1.idxOf (G.edgeEndpoint i false))
        (G.1.idxOf (G.edgeEndpoint i true)) (portAt ports i false) (portAt ports i true) := by
  rw [getElem_orthogonalRoutes G ports hi]
  simp only [edgeEndpoint, portAt, Bool.false_eq_true, ↓reduceIte]
  rw [List.getD_eq_getElem _ _ hi]

/-- Every route has the actual indexed graph edge's endpoints, regardless of the port table. -/
theorem orthogonalRoutes_endpoints (G : Graph) (ports : List (Fin 3 × Fin 3))
    {i : ℕ} (hi : i < G.2.length) :
    let r := (G.orthogonalRoutes ports)[i]'(by simpa using hi)
    r.head? = some (Layout.center (G.1.idxOf G.2[i].1)) ∧
      r.getLast? = some (Layout.center (G.1.idxOf G.2[i].2)) := by
  simp [getElem_orthogonalRoutes G ports hi]

/-- Declared, distinct edge endpoints give a proper orthogonal route. -/
theorem orthogonalRoutes_orthogonal (G : Graph) (ports : List (Fin 3 × Fin 3))
    {i : ℕ} (hi : i < G.2.length) (hu : G.2[i].1 ∈ G.1) (hv : G.2[i].2 ∈ G.1)
    (hne : G.2[i].1 ≠ G.2[i].2) :
    IsOrthogonal ((G.orthogonalRoutes ports)[i]'(by simpa using hi)) := by
  rw [getElem_orthogonalRoutes G ports hi]
  exact Layout.route_orthogonal (List.idxOf_lt_length_iff.2 hu)
    (List.idxOf_lt_length_iff.2 hv) (fun h => hne ((List.idxOf_inj hu).1 h)) _ _

/-- Declared, distinct edge endpoints give a continuously simple route. -/
theorem orthogonalRoutes_simple (G : Graph) (ports : List (Fin 3 × Fin 3))
    {i : ℕ} (hi : i < G.2.length) (hu : G.2[i].1 ∈ G.1) (hv : G.2[i].2 ∈ G.1)
    (hne : G.2[i].1 ≠ G.2[i].2) :
    IsSimple ((G.orthogonalRoutes ports)[i]'(by simpa using hi)) := by
  rw [getElem_orthogonalRoutes G ports hi]
  exact Layout.route_simple (List.idxOf_lt_length_iff.2 hu)
    (List.idxOf_lt_length_iff.2 hv) (fun h => hne ((List.idxOf_inj hu).1 h)) _ _

/-- At most `2m²` candidate grid sites suffice for every bridge/stem crossing. Candidates may
repeat or be unused; this explicit list is a cover, not a claim that every candidate is crossed. -/
def crossingCandidates (G : Graph) (ports : List (Fin 3 × Fin 3)) : List Point :=
  (List.range G.2.length).flatMap fun i =>
    (List.range G.2.length).flatMap fun j =>
      [(Layout.column (G.1.idxOf (G.edgeEndpoint j false)) (portAt ports j false),
          Layout.track G.1.length i),
        (Layout.column (G.1.idxOf (G.edgeEndpoint j true)) (portAt ports j true),
          Layout.track G.1.length i)]

/-- A quadratic bound on the explicit crossing-site cover, counting repeated candidates. -/
@[simp] theorem crossingCandidates_length (G : Graph) (ports : List (Fin 3 × Fin 3)) :
    (G.crossingCandidates ports).length = 2 * G.2.length ^ 2 := by
  simp [crossingCandidates, List.length_flatMap, List.map_const', pow_two, Nat.mul_comm,
    Nat.mul_assoc]

/-- Every indexed bridge/port intersection point occurs in the finite candidate cover. -/
theorem mem_crossingCandidates (G : Graph) (ports : List (Fin 3 × Fin 3))
    {i j : ℕ} (hi : i < G.2.length) (hj : j < G.2.length) (side : Bool) :
    (Layout.column (G.1.idxOf (G.edgeEndpoint j side)) (portAt ports j side),
        Layout.track G.1.length i) ∈ G.crossingCandidates ports := by
  apply List.mem_flatMap.2
  refine ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, ?_⟩⟩
  cases side <;> simp

/-- Every contact in the canonical drawing lies at a vertex center or in an explicit list of
`2m²` candidate crossing sites. Strict transversality is supplied by `Layout.route_contact`;
this finite cover additionally bounds the number of distinct crossing sites. -/
theorem orthogonalRoutes_contact_cover (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j) {p : ℝ × ℝ}
    (hp : p ∈ support ((G.orthogonalRoutes G.canonicalPorts)[i]'(by simpa using hi)))
    (hq : p ∈ support ((G.orthogonalRoutes G.canonicalPorts)[j]'(by simpa using hj))) :
    (∃ w < G.1.length, p = realPoint (Layout.center w)) ∨
      ∃ z ∈ G.crossingCandidates G.canonicalPorts, p = realPoint z := by
  have hindex (k : ℕ) (hk : k < G.2.length) (side : Bool) :
      G.1.idxOf (G.edgeEndpoint k side) < G.1.length :=
    List.idxOf_lt_length_iff.2 (edgeEndpoint_mem G hG hk side)
  rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hi] at hp
  rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hj] at hq
  have hc := Layout.route_contact (hindex i hi false) (hindex i hi true)
    (hindex j hj false) (hindex j hj true) hij
    (canonical_index_port_ne G hG hdeg hi hj hij false false)
    (canonical_index_port_ne G hG hdeg hi hj hij false true)
    (canonical_index_port_ne G hG hdeg hi hj hij true false)
    (canonical_index_port_ne G hG hdeg hi hj hij true true) hp hq
  rcases hc with ⟨w, hw, _, hp⟩ | h | h | h | h
  · refine Or.inl ⟨w, ?_, hp⟩
    rcases hw with rfl | rfl
    · exact hindex i hi false
    · exact hindex i hi true
  · exact Or.inr ⟨_, mem_crossingCandidates G G.canonicalPorts hi hj false,
      Layout.bridge_stem_crossing_point h⟩
  · exact Or.inr ⟨_, mem_crossingCandidates G G.canonicalPorts hi hj true,
      Layout.bridge_stem_crossing_point h⟩
  · exact Or.inr ⟨_, mem_crossingCandidates G G.canonicalPorts hj hi false,
      Layout.bridge_stem_crossing_point h⟩
  · exact Or.inr ⟨_, mem_crossingCandidates G G.canonicalPorts hj hi true,
      Layout.bridge_stem_crossing_point h⟩

/-- Exactly five segments are emitted for every edge occurrence. -/
theorem orthogonalRoutes_segments (G : Graph) (ports : List (Fin 3 × Fin 3)) :
    ((G.orthogonalRoutes ports).map fun r => r.consecutivePairs.length).sum = 5 * G.2.length := by
  simp [orthogonalRoutes, Layout.route, List.map_map, Function.comp_def, Nat.mul_comm]

/-- The total wire length is at most `90 (n+m)²`, for `n` declared vertices and `m` edge
occurrences. Endpoint membership is the only graph hypothesis needed for this resource bound. -/
theorem orthogonalRoutes_wireLength_le (G : Graph) (ports : List (Fin 3 × Fin 3))
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1) :
    ((G.orthogonalRoutes ports).map wireLength).sum ≤ 90 * (G.1.length + G.2.length) ^ 2 := by
  have hbound : ∀ r ∈ G.orthogonalRoutes ports,
      wireLength r ≤ 80 * G.1.length + 10 * G.2.length := by
    intro r hr
    obtain ⟨⟨edge, i⟩, he, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 he)
    change G.2[i] = edge at heq
    have hm : edge ∈ G.2 := by
      have hmem : G.2[i] ∈ G.2 := List.getElem_mem hi
      simpa only [heq] using hmem
    exact Layout.route_wireLength_le hi (List.idxOf_lt_length_iff.2 (hG edge hm).1)
      (List.idxOf_lt_length_iff.2 (hG edge hm).2) _ _
  calc
    _ ≤ ((G.orthogonalRoutes ports).map fun _ => 80 * G.1.length + 10 * G.2.length).sum :=
      List.sum_le_sum hbound
    _ = G.2.length * (80 * G.1.length + 10 * G.2.length) := by simp
    _ ≤ 90 * (G.1.length + G.2.length) ^ 2 := by nlinarith

end Cslib.Complexity.Graph
