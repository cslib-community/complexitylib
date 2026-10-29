/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.Graph.OrthogonalPath

/-! Concrete finite occupancy and crossing-neighborhood regressions. -/

open Cslib.Complexity Cslib.Orthogonal

private def exampleGraph : Graph := ([0, 1, 2, 3, 4, 5], [(0, 2), (1, 3), (4, 5)])

private theorem declared : ∀ e ∈ exampleGraph.2, e.1 ∈ exampleGraph.1 ∧ e.2 ∈ exampleGraph.1 := by
  intro e he
  simp only [exampleGraph, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> decide

private theorem loopless : ∀ e ∈ exampleGraph.2, e.1 ≠ e.2 := by
  intro e he
  simp only [exampleGraph, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> decide

private theorem degree : ∀ v, exampleGraph.incidenceVertices.count v ≤ 3 := by
  have hn : exampleGraph.incidenceVertices.Nodup := by decide
  exact fun v => (List.nodup_iff_count_le_one.1 hn v).trans (by decide)

private def crossing : Point := (10, 50)

private theorem first_member : crossing ∈ exampleGraph.unitPath 0 := by decide

private theorem second_member : crossing ∈ exampleGraph.unitPath 1 := by decide

private theorem not_center : crossing ∉ exampleGraph.orthogonalPositions := by decide

private theorem strict_crossing : exampleGraph.BridgeStemCrossing 0 1 false crossing := by
  change Transverse (2, 50) (18, 50) (10, 12) (10, 52) (realPoint (10, 50))
  norm_num [Transverse, realPoint]

-- Unit-path lengths, endpoints, straight-through crossing neighborhoods, non-center occupancy,
-- elbow neighbor lengths/distinctness, and crossing-candidate membership on `exampleGraph`.
example :
    exampleGraph.unitPaths.length = 3 ∧
    exampleGraph.unitPath 3 = [] ∧
    ((exampleGraph.unitPath 0).head? = some (4, 4) ∧
      (exampleGraph.unitPath 0).getLast? = some (20, 20)) ∧
    (StraightThrough (exampleGraph.unitPath 0) crossing (1, 0) ∧
      StraightThrough (exampleGraph.unitPath 1) crossing (0, 1)) ∧
    crossing ∉ exampleGraph.unitPath 2 ∧
    Layout.center 2 ∉ exampleGraph.unitPath 1 ∧
    ((exampleGraph.unitPath 0).getD 55 crossing = crossing - (1, 0) ∧
      (exampleGraph.unitPath 0).getD 57 crossing = crossing + (1, 0)) ∧
    ((exampleGraph.unitPath 1).getD 39 crossing = crossing - (0, 1) ∧
      (exampleGraph.unitPath 1).getD 41 crossing = crossing + (0, 1)) ∧
    (0 < 56 ∧ 56 + 1 < (exampleGraph.unitPath 0).length ∧
      (((exampleGraph.unitPath 0).getD 55 crossing = crossing - (1, 0) ∧
        (exampleGraph.unitPath 0).getD 57 crossing = crossing + (1, 0)) ∨
        ((exampleGraph.unitPath 0).getD 55 crossing = crossing + (1, 0) ∧
          (exampleGraph.unitPath 0).getD 57 crossing = crossing - (1, 0)))) ∧
    (crossing ∉ (exampleGraph.orthogonalRoutes exampleGraph.canonicalPorts)[0] ∧
      crossing ∉ (exampleGraph.orthogonalRoutes exampleGraph.canonicalPorts)[1]) ∧
    ((exampleGraph.unitPath 0).head? ≠ some crossing ∧
      (exampleGraph.unitPath 0).getLast? ≠ some crossing) ∧
    (length ((exampleGraph.unitPath 0).getD 1 (2, 4)) (2, 4) = 1 ∧
      length (2, 4) ((exampleGraph.unitPath 0).getD 3 (2, 4)) = 1) ∧
    (exampleGraph.unitPath 0).getD 1 (2, 4) ≠ (exampleGraph.unitPath 0).getD 3 (2, 4) ∧
    crossing ∈ exampleGraph.crossingCandidates exampleGraph.canonicalPorts := by
  refine ⟨by decide, by decide, by decide,
    strict_crossing.neighbors declared loopless (by decide) (by decide), ?_, ?_,
    by decide, by decide,
    (strict_crossing.neighbors declared loopless (by decide) (by decide)).1.getD_neighbors
      (Graph.unitPath_nodup exampleGraph declared loopless (by decide))
      (k := 56) (by decide) (by decide),
    strict_crossing.not_listed declared (by decide) (by decide),
    Graph.unitPath_not_endpoints exampleGraph declared loopless (by decide) not_center,
    Graph.unitPath_neighbor_lengths exampleGraph declared loopless (by decide)
      (k := 2) (by decide) (by decide) (by decide),
    Graph.unitPath_neighbors_distinct exampleGraph declared loopless (by decide)
      (k := 2) (by decide) (by decide) (by decide),
    Graph.unitPath_shared_mem_crossingCandidates exampleGraph declared loopless degree
      (by decide) (by decide) (by decide) not_center first_member second_member⟩
  · intro h
    have hindex := Graph.unitPath_atMostTwo exampleGraph declared loopless degree
      (by decide : 0 < exampleGraph.2.length) (by decide : 1 < exampleGraph.2.length)
      (by decide : 2 < exampleGraph.2.length) (by decide) not_center first_member second_member h
    omega
  · rw [Graph.unitPath_center_iff exampleGraph declared loopless (by decide) (by decide)]
    decide

private def reverseGraph : Graph := ([0, 1, 2, 3, 4, 5], [(2, 0), (3, 1), (4, 5)])
private def starGraph : Graph := ([0, 1, 2, 3], [(0, 1), (0, 2), (0, 3)])
private def returnStar : Graph := ([0, 1, 2, 3], [(1, 0), (2, 0), (3, 0)])

private theorem star_declared : ∀ e ∈ starGraph.2, e.1 ∈ starGraph.1 ∧ e.2 ∈ starGraph.1 := by
  intro e he
  simp only [starGraph, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> decide

private theorem star_loopless : ∀ e ∈ starGraph.2, e.1 ≠ e.2 := by
  intro e he
  simp only [starGraph, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> decide

private theorem star_degree : ∀ v, starGraph.incidenceVertices.count v ≤ 3 := by
  intro v
  by_cases hv : v ∈ starGraph.incidenceVertices
  · have hv' : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
      simpa [starGraph, Graph.incidenceVertices, or_assoc, or_left_comm, or_comm] using hv
    rcases hv' with rfl | rfl | rfl | rfl <;> decide
  · rw [List.count_eq_zero_of_not_mem hv]
    decide

-- Reversed endpoint traversal, declared source center occupancy, canonical source/target port
-- neighbors, and distinctness of endpoint neighbors on `starGraph`.
example (d : Point) :
    ((reverseGraph.unitPath 0).getD 39 crossing = crossing + (1, 0) ∧
      (reverseGraph.unitPath 0).getD 41 crossing = crossing - (1, 0)) ∧
    ((reverseGraph.unitPath 1).getD 43 crossing = crossing + (0, 1) ∧
      (reverseGraph.unitPath 1).getD 45 crossing = crossing - (0, 1)) ∧
    (Layout.center 0 ∈ starGraph.unitPath 0 ∧ Layout.center 0 ∈ starGraph.unitPath 1 ∧
      Layout.center 0 ∈ starGraph.unitPath 2) ∧
    (starGraph.endpointNeighbor 0 false = (3, 4) ∧
      starGraph.endpointNeighbor 1 false = (4, 5) ∧
      starGraph.endpointNeighbor 2 false = (5, 4)) ∧
    (returnStar.endpointNeighbor 0 true = (3, 4) ∧
      returnStar.endpointNeighbor 1 true = (4, 5) ∧
      returnStar.endpointNeighbor 2 true = (5, 4)) ∧
    (exampleGraph.unitPath 0).getD 1 d =
      Layout.center (exampleGraph.1.idxOf (exampleGraph.edgeEndpoint 0 false)) +
        Layout.portStep (Graph.portAt exampleGraph.canonicalPorts 0 false) ∧
    (exampleGraph.unitPath 0).getD ((exampleGraph.unitPath 0).length - 2) d =
      Layout.center (exampleGraph.1.idxOf (exampleGraph.edgeEndpoint 0 true)) +
        Layout.portStep (Graph.portAt exampleGraph.canonicalPorts 0 true) ∧
    starGraph.endpointNeighbor 0 false ≠ starGraph.endpointNeighbor 1 false :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   Graph.unitPath_first_neighbor exampleGraph declared loopless (by decide) d,
   Graph.unitPath_last_neighbor exampleGraph declared loopless (by decide) d,
   Graph.endpointNeighbor_ne starGraph star_declared star_loopless star_degree
     (by decide) (by decide) (by decide) false false (by decide)⟩
