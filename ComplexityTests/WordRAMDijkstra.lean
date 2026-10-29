/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.LogLinear

/-! Nonvacuity and interpreter checks for Dijkstra's algorithm with a binary heap. -/

@[expose] public section

open Cslib Cslib.WordRAM Cslib.Algorithms.WordRAM.Dijkstra

namespace WordRAMDijkstraTests

/-- Three vertices, a parallel edge and a shorter path through a third vertex: edges `0 → 1` of
weights `4` and `5`, `0 → 2` of weight `1`, and `2 → 1` of weight `2`, from source `0`. The
distances are `0`, `3` and `1`. -/
def graph : ListInstance where
  n := 3
  adj := ![[(1, 4), (2, 1), (1, 5)], [], [(1, 2)]]
  source := 0

/-- `graph` has `4` edges, maximum weight `5`, and encoded words `n`, source, offsets `0, 3, 3, 4`,
then the edges. -/
example : (graph.m = 4 ∧ graph.maxWeight = 5) ∧
    graph.encode = [3, 0, 0, 3, 3, 4, 1, 4, 2, 1, 1, 5, 1, 2] := by decide

/-- The word-size hypothesis of `LogLinearSpec` holds for the instance at word size `10`. -/
theorem fits : Fits 10 (8 * (graph.n + graph.m + 2) * (graph.maxWeight + 2)) := by decide

/-- The main theorem applies to the instance: the compiled program halts within
`230 (m + 1) (⌊log₂ n⌋ + 1)` instructions and leaves `1` at the source's output cell, the
encoded distance `0`. -/
example : ∃ t steps, Runs 10 (heapDijkstra.program OuterReg.zero) (.init graph.encode) t steps ∧
    (∃ v, step 10 (heapDijkstra.program OuterReg.zero) t = .halt v) ∧ steps + 1 ≤ 230 * 5 * 2 ∧
    t.data.mem (graph.outAddr graph.source) = 1 := by
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := logLinearSpec graph 10 fits
  have hm : graph.m = 4 := by decide
  have hlog : Nat.log 2 graph.n = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [hm, hlog] at hle
  refine ⟨t, steps, hr, hh, hle, ?_⟩
  rw [hd]
  exact (congrArg encodeDist (graph.toInstance.dist_self graph.toInstance.source)).trans
    (by simp [encodeDist])

/-- The interpreter runs the structured program on the instance and finds the encoded distances
`1`, `4` and `2` in the output cells, within the bound `200 (m + 1) (⌊log₂ n⌋ + 1)` of
`heapDijkstra_spec`. -/
example : ((heapDijkstra.eval 10 16 (.init graph.encode)).map fun yn =>
    ((List.finRange 3).map fun v => yn.1.mem (graph.outAddr v), decide (yn.2 ≤ 2000))) =
    some ([1, 4, 2], true) := by
  decide +kernel

/-- Two vertices and no edge, from source `0`: vertex `1` is unreachable. -/
def edgeless : ListInstance where
  n := 2
  adj := ![[], []]
  source := 0

/-- With no edge the bound `200 (m + 1) (⌊log₂ n⌋ + 1)` of `heapDijkstra_spec` is `400`. The
interpreter finds `1` (distance `0`) in the source's output cell and `0` (unreachable) in the other
one, within that bound. -/
example : ((heapDijkstra.eval 10 16 (.init edgeless.encode)).map fun yn =>
    ((List.finRange 2).map fun v => yn.1.mem (edgeless.outAddr v), decide (yn.2 ≤ 400))) =
    some ([1, 0], true) := by
  decide +kernel

end WordRAMDijkstraTests
