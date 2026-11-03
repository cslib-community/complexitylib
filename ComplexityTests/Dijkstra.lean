/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dijkstra.Cost

/-! Runs of Dijkstra's algorithm as a client of the priority-queue, distance-map and graph
interfaces, and nonvacuity of its correctness and cost theorems. -/

@[expose] public section

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance)
open Cslib.Algorithms.Lean.Dijkstra

namespace DijkstraTests

/-- Three vertices, a parallel edge and a shorter path through a third vertex: edges `0 → 1` of
weights `4` and `5`, `0 → 2` of weight `1`, and `2 → 1` of weight `2`, from source `0`. The
distances are `0`, `3` and `1`. -/
def graph : ListInstance where
  n := 3
  adj := ![[(1, 4), (2, 1), (1, 5)], [], [(1, 2)]]
  source := 0

/-- `graph` has `4` edges and largest weight `5`, so keys up to `15` and values below `16`
suffice. -/
example : graph.m = 4 ∧ graph.maxWeight = 5 := by decide

/-- Running the client against the specifications ends with an empty queue and the distances
`0`, `3` and `1` in the distance map. -/
example : let (q, dist, _) := (spec 3 15 16).clientState (init graph) (dijkstra graph.source)
    q = IndexedMinPQ.empty 3 ∧ dist = ![some 0, some 3, some 1] := by
  decide +kernel

/-- The operations, by kind. The parallel edge of weight `5` is read but relaxes nothing, the edge
`2 → 1` decreases the key of `1` from `4` to `3`, and the third extraction visits `1`, which has
no edges. The graph queries meet their bound `min (n + m) (2 m + 1) = 7`. -/
example : ((spec 3 15 16).clientHistory (init graph) (dijkstra graph.source)).map kind =
    [.distance, .insert,
      .extractMin, .graph, .graph, .distance, .distance, .insert,
        .graph, .distance, .distance, .insert, .graph, .distance,
      .extractMin, .graph, .graph, .distance, .distance, .decreaseKey,
      .extractMin, .graph] ∧
    ((spec 3 15 16).clientHistory (init graph) (dijkstra graph.source)).countP
      (kind · = .graph) = maxCount 3 4 .graph := by
  decide +kernel

/-- The correctness theorem applies to `graph`, and gives the distance `3` to vertex `1`. -/
example : (spec 3 15 16).ValidHistory (init graph)
      ((spec 3 15 16).clientHistory (init graph) (dijkstra graph.source)) ∧
    HasDistances graph ((spec 3 15 16).clientState (init graph) (dijkstra graph.source)) :=
  dijkstra_correct graph (by decide) (by decide)

/-- Two vertices and no edge, from source `0`: vertex `1` stays unreached. -/
def edgeless : ListInstance where
  n := 2
  adj := ![[], []]
  source := 0

/-- On `edgeless`, the second round finds the queue empty, and vertex `1` has no distance. -/
example : let (q, dist, _) := (spec 2 0 1).clientState (init edgeless) (dijkstra edgeless.source)
    q = IndexedMinPQ.empty 2 ∧ dist = ![some 0, none] := by
  decide +kernel

/-- Four vertices and one edge `0 → 1`: the counts follow the edges, not the vertices. Two
insertions and three extractions, the last finding the queue empty, meet the bounds
`min n (m + 1) = 2` and `min n (m + 2) = 3`. -/
def sparse : ListInstance where
  n := 4
  adj := ![[(1, 7)], [], [], []]
  source := 0

example : let hist := (spec 4 28 29).clientHistory (init sparse) (dijkstra sparse.source)
    hist.countP (kind · = .insert) = maxCount 4 1 .insert ∧
      hist.countP (kind · = .extractMin) = maxCount 4 1 .extractMin := by
  decide +kernel

/-- Under binary-heap-style charges of `2` per queue operation, the cost theorem bounds the cost
on `graph` by `3 · 2 + 3 · 2 + 4 · 2 + 3 + 3 · 4 + 1 = 36`, the lesser of the two forms of the
budget. -/
example : (spec 3 15 16).CostHoare (charge fun _ _ => 2) (· = init graph) (dijkstra graph.source)
    (fun _ => HasDistances graph) (fun _ => 36) :=
  (costHoare_dijkstra (K := 15) (V := 16) (cI := 2) (cE := 2) (cD := 2) graph (by decide)
    (by decide) _ (fun _ _ _ => le_rfl) (fun _ => le_rfl) (fun _ _ _ => le_rfl)).consequence
    (fun _ h => h) (fun _ _ h => h) fun _ _ => by decide

/-- The asymptotic binary-heap-style bound applies to `graph` with charges of `2` per queue
operation, which is `⌊log₂ 3⌋ + 1`. -/
example : ∃ b, (spec 3 15 16).CostHoare (charge fun _ _ => 2) (· = init graph)
    (dijkstra graph.source) (fun _ => HasDistances graph) (fun _ => b) := by
  obtain ⟨f, _, _, hf⟩ := exists_costHoare_logLinear 1
  exact ⟨_, hf graph 15 16 (by decide) (by decide) _ fun _ _ => by
    rw [show Nat.log 2 graph.n = 1 from Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)]⟩

end DijkstraTests
