/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Dijkstra.LogLinear
import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Binary

/-! Nonvacuity and native-run checks for binary-heap Dijkstra. The original graph, parallel-edge
and edgeless cases now use native flat-program witnesses. The previous structured program's
literal `200`/`230` clock coefficients are not carried over to the new implementation. -/

@[expose] public section

open Cslib Cslib.WordRAM Cslib.Algorithms.Dijkstra Cslib.Algorithms.WordRAM.Dijkstra

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

/-- The unchanged endpoint chooses one program and factor before every graph. Its actual flat
run on the sample includes the halt charge and leaves the encoded source distance `1`. -/
example : ∃ r, ∃ prog : Program .exact r, ∃ K, LogLinearSpec prog K ∧
    ∃ t steps, Runs 10 prog (.init graph.encode) t steps ∧
      (∃ v, step 10 prog t = .halt v) ∧ steps + 1 ≤ K * 5 * 2 ∧
      t.data.mem (graph.outAddr graph.source) = 1 := by
  obtain ⟨r, prog, K, hp⟩ := logLinearStatement
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := hp graph 10 fits
  have hm : graph.m = 4 := by decide
  have hlog : Nat.log 2 graph.n = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [hm, hlog] at hle
  refine ⟨r, prog, K, hp, t, steps, hr, hh, hle, ?_⟩
  rw [hd]
  exact (congrArg encodeDist (graph.toInstance.dist_self graph.toInstance.source)).trans
    (by simp [encodeDist])

/-- Two vertices and no edge, from source `0`: vertex `1` is unreachable. -/
def edgeless : ListInstance where
  n := 2
  adj := ![[], []]
  source := 0

private theorem graph_source_result :
    ((List.finRange graph.n).map fun v =>
      ((DataStructure.Memory.spec 10).clientState
        (DataStructure.Memory.State.init graph.encode)
        Algorithms.Lean.Dijkstra.Memory.run).mem (graph.outAddr v)) = [1, 4, 2] ∧
      ((DataStructure.Memory.spec 10).clientState (DataStructure.Memory.State.init graph.encode)
        Algorithms.Lean.Dijkstra.Memory.run).frontier = 29 := by decide +kernel

private theorem edgeless_source_result :
    ((List.finRange edgeless.n).map fun v =>
      ((DataStructure.Memory.spec 10).clientState
        (DataStructure.Memory.State.init edgeless.encode)
        Algorithms.Lean.Dijkstra.Memory.run).mem (edgeless.outAddr v)) = [1, 0] ∧
      ((DataStructure.Memory.spec 10).clientState (DataStructure.Memory.State.init edgeless.encode)
        Algorithms.Lean.Dijkstra.Memory.run).frontier = 16 := by decide +kernel

/-- A single native flat program handles the original parallel-edge sample and the edgeless
input. The actual runs halt, meet the same uniform clock factor, retain the complete source
memory, and produce the original encoded distances and exact allocated frontiers. -/
example : ∃ r K pc, ∃ prog : Program .exact r, ∃ frontier : Fin r,
    (∃ (y : Data r) (steps : ℕ), Runs 10 prog (.init graph.encode) ⟨pc, y⟩ steps ∧
      step 10 prog ⟨pc, y⟩ = .halt 0 ∧ steps + 1 ≤ K * 5 * 2 ∧
      ((List.finRange graph.n).map fun v => y.mem (graph.outAddr v)) = [1, 4, 2] ∧
      y.regs frontier = 29) ∧
    (∃ (y : Data r) (steps : ℕ), Runs 10 prog (.init edgeless.encode) ⟨pc, y⟩ steps ∧
      step 10 prog ⟨pc, y⟩ = .halt 0 ∧ steps + 1 ≤ K * 1 * 2 ∧
      ((List.finRange edgeless.n).map fun v => y.mem (edgeless.outAddr v)) = [1, 0] ∧
      y.regs frontier = 16) := by
  obtain ⟨r, K, pc, prog, frontier, he⟩ :=
    Algorithms.Lean.Dijkstra.Native.Binary.exists_program_state
  refine ⟨r, K, pc, prog, frontier, ?_, ?_⟩
  · obtain ⟨y, steps, hr, hh, hm, ht, _⟩ := he graph 10 fits
    have hn : graph.m = 4 ∧ Nat.log 2 graph.n = 1 := by decide +kernel
    rw [hn.1, hn.2] at ht
    refine ⟨y, steps, hr, hh, ht, ?_, ?_⟩
    · exact (congrArg (fun m : ℕ → ℕ =>
        (List.finRange graph.n).map fun v => m (graph.outAddr v))
        (congrArg DataStructure.Memory.State.mem hm)).trans graph_source_result.1
    · exact (congrArg DataStructure.Memory.State.frontier hm).trans graph_source_result.2
  · obtain ⟨y, steps, hr, hh, hm, ht, _⟩ := he edgeless 10 (by decide)
    have hn : edgeless.m = 0 ∧ Nat.log 2 edgeless.n = 1 := by decide +kernel
    rw [hn.1, hn.2] at ht
    refine ⟨y, steps, hr, hh, ht, ?_, ?_⟩
    · exact (congrArg (fun m : ℕ → ℕ =>
        (List.finRange edgeless.n).map fun v => m (edgeless.outAddr v))
        (congrArg DataStructure.Memory.State.mem hm)).trans edgeless_source_result.1
    · exact (congrArg DataStructure.Memory.State.frontier hm).trans edgeless_source_result.2

end WordRAMDijkstraTests
