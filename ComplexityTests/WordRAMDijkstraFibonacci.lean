/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.Fibonacci

/-!
# Non-vacuity and interpreter checks for Dijkstra's algorithm with a Fibonacci heap

Exercises `fibDijkstra`, `fibonacciSpec`, `fibonacciLinearSpec`, and `fibonacciStatement` on
concrete graphs with parallel edges, multi-hop relaxations, and unreachable vertices.
-/

@[expose] public section

open Cslib Cslib.WordRAM Cslib.Algorithms.WordRAM.Dijkstra

namespace WordRAMDijkstraFibonacciTests

/-- Three vertices, a parallel edge and a shorter path through vertex `2`: edges `0 → 1` of weights
`4` and `5`, `0 → 2` of weight `1`, and `2 → 1` of weight `2`, from source `0`. Distances are `0`,
`3` and `1` (encoded as `1`, `4` and `2`). -/
def graph : ListInstance where
  n := 3
  adj := ![[(1, 4), (2, 1), (1, 5)], [], [(1, 2)]]
  source := 0

theorem fits_graph : Fits 10 (8 * (graph.n + graph.m + 2) * (graph.maxWeight + 2)) := by decide

/-- Non-vacuity of `fibonacciLinearSpec` (`O(m + n log n)`) on `graph`. -/
example : ∃ t steps, Runs 10 (fibDijkstra.program OuterReg.zero) (.init graph.encode) t steps ∧
    (∃ v, step 10 (fibDijkstra.program OuterReg.zero) t = .halt v) ∧
    steps + 1 ≤ 640 * (4 + 3 * 2) ∧
    t.data.mem (graph.outAddr graph.source) = 1 := by
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := fibonacciLinearSpec graph 10 fits_graph
  have hm : graph.m = 4 := by decide
  have hn : graph.n = 3 := rfl
  have hlog : Nat.log 2 graph.n = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [hm, hlog, hn] at hle
  refine ⟨t, steps, hr, hh, hle, ?_⟩
  rw [hd]
  exact (congrArg encodeDist (graph.toInstance.dist_self graph.toInstance.source)).trans
    (by simp [encodeDist])

/-- Five vertices and no edges (`m = 0`): `fibonacciSpec` bounds total instructions by
`640 * (0 + min 5 1 * 3) = 1920`, strictly sharper than `640 * (0 + 5 * 3) = 9600`. -/
def sparseEdgeless : ListInstance where
  n := 5
  adj := fun _ => []
  source := 0

theorem fits_sparseEdgeless :
    Fits 10 (8 * (sparseEdgeless.n + sparseEdgeless.m + 2) * (sparseEdgeless.maxWeight + 2)) := by
  decide

example : ∃ t steps,
    Runs 10 (fibDijkstra.program OuterReg.zero) (.init sparseEdgeless.encode) t steps ∧
    (∃ v, step 10 (fibDijkstra.program OuterReg.zero) t = .halt v) ∧
    steps + 1 ≤ 640 * 3 ∧
    t.data.mem (sparseEdgeless.outAddr sparseEdgeless.source) = 1 := by
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := fibonacciSpec sparseEdgeless 10 fits_sparseEdgeless
  have hm : sparseEdgeless.m = 0 := by decide
  have hn : sparseEdgeless.n = 5 := rfl
  have hlog : Nat.log 2 sparseEdgeless.n = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [hm, hlog, hn] at hle
  refine ⟨t, steps, hr, hh, by omega, ?_⟩
  rw [hd]
  exact (congrArg encodeDist
    (sparseEdgeless.toInstance.dist_self sparseEdgeless.toInstance.source)).trans
    (by simp [encodeDist])

/-- Concrete interpreter execution of `fibDijkstra` on `graph`: produces encoded distances
`[1, 4, 2]` within the `640 * (4 + 3 * 2) = 6400` step bound of `fibDijkstra_spec`. -/
example : ((fibDijkstra.eval 10 32 (.init graph.encode)).map fun yn =>
    ((List.finRange 3).map fun v => yn.1.mem (graph.outAddr v), decide (yn.2 ≤ 6400))) =
    some ([1, 4, 2], true) := by
  decide +kernel

/-- Concrete interpreter execution of `fibDijkstra` on an edgeless `2`-vertex graph: produces
`[1, 0]` (`0` for unreachable vertex `1`) within `640 * (0 + 1 * 2) = 1280` steps. -/
def edgeless : ListInstance where
  n := 2
  adj := ![[], []]
  source := 0

example : ((fibDijkstra.eval 10 32 (.init edgeless.encode)).map fun yn =>
    ((List.finRange 2).map fun v => yn.1.mem (edgeless.outAddr v), decide (yn.2 ≤ 1280))) =
    some ([1, 0], true) := by
  decide +kernel

/-- Non-vacuity of `fibonacciStatement` (`O(m + n log n)`) on `graph`. -/
example : ∃ r, ∃ p : Program .exact r, ∃ K t steps,
    Runs 10 p (.init graph.encode) t steps ∧
    (∃ v, step 10 p t = .halt v) ∧
    steps + 1 ≤ K * (4 + 3 * 2) ∧
    t.data.mem (graph.outAddr graph.source) = 1 := by
  obtain ⟨r, p, K, h⟩ := fibonacciStatement
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := h graph 10 fits_graph
  have hm : graph.m = 4 := by decide
  have hn : graph.n = 3 := rfl
  have hlog : Nat.log 2 graph.n = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [hm, hlog, hn] at hle
  refine ⟨r, p, K, t, steps, hr, hh, hle, ?_⟩
  rw [hd]
  exact (congrArg encodeDist (graph.toInstance.dist_self graph.toInstance.source)).trans
    (by simp [encodeDist])

end WordRAMDijkstraFibonacciTests
