/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Dijkstra.Fibonacci
import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci

/-!
# Native Fibonacci-Dijkstra nonvacuity and whole-state checks

The original parallel-edge, shorter multi-hop, unreachable and sparse-edgeless cases use one
native flat-program witness. The actual source interpreter fixes their distances and allocated
frontiers; the native runs retain that complete source state. The old implementation's literal
coefficient `640` is not carried over to the native program.
-/

@[expose] public section

open Cslib Cslib.WordRAM Cslib.Algorithms.Dijkstra Cslib.Algorithms.WordRAM.Dijkstra
open Cslib.Algorithms.Lean.Dijkstra.Native

namespace WordRAMDijkstraFibonacciTests

/-- Three vertices, a parallel edge and a shorter path through vertex `2`: edges `0 → 1` of weights
`4` and `5`, `0 → 2` of weight `1`, and `2 → 1` of weight `2`, from source `0`. Distances are `0`,
`3` and `1` (encoded as `1`, `4` and `2`). -/
def graph : ListInstance where
  n := 3
  adj := ![[(1, 4), (2, 1), (1, 5)], [], [(1, 2)]]
  source := 0

theorem fits_graph : Fits 10 (8 * (graph.n + graph.m + 2) * (graph.maxWeight + 2)) := by decide

/-- Five vertices without edges: the sharper reachable bound contains only one logarithmic
term, while the textbook bound contains five. -/
def sparseEdgeless : ListInstance where
  n := 5
  adj := fun _ => []
  source := 0

theorem fits_sparseEdgeless :
    Fits 10 (8 * (sparseEdgeless.n + sparseEdgeless.m + 2) * (sparseEdgeless.maxWeight + 2)) := by
  decide

/-- Two vertices and no edges; vertex `1` is unreachable from source `0`. -/
def edgeless : ListInstance where
  n := 2
  adj := ![[], []]
  source := 0

private theorem graph_source_result :
    ((List.finRange graph.n).map fun v =>
      ((DataStructure.Memory.spec 10).clientState
        (DataStructure.Memory.State.init graph.encode) Fibonacci.run).mem (graph.outAddr v)) =
        [1, 4, 2] ∧
      ((DataStructure.Memory.spec 10).clientState
        (DataStructure.Memory.State.init graph.encode) Fibonacci.run).frontier = 50 := by
  decide +kernel

private theorem edgeless_source_result :
    ((List.finRange edgeless.n).map fun v =>
      ((DataStructure.Memory.spec 10).clientState
        (DataStructure.Memory.State.init edgeless.encode) Fibonacci.run).mem (edgeless.outAddr v)) =
        [1, 0] ∧
      ((DataStructure.Memory.spec 10).clientState
        (DataStructure.Memory.State.init edgeless.encode) Fibonacci.run).frontier = 31 := by
  decide +kernel

private theorem sparse_source_result :
    ((List.finRange sparseEdgeless.n).map fun v =>
      ((DataStructure.Memory.spec 10).clientState
        (DataStructure.Memory.State.init sparseEdgeless.encode) Fibonacci.run).mem
        (sparseEdgeless.outAddr v)) = [1, 0, 0, 0, 0] ∧
      ((DataStructure.Memory.spec 10).clientState
        (DataStructure.Memory.State.init sparseEdgeless.encode) Fibonacci.run).frontier = 64 := by
  decide +kernel

private def NativeCase {r : ℕ} (prog : Program .exact r) (pc K : ℕ) (frontier : Fin r)
    (G : ListInstance) (bound : ℕ) (distances : List ℕ) (endFrontier : ℕ) : Prop :=
  ∃ (y : Data r) (steps : ℕ), Runs 10 prog (.init G.encode) ⟨pc, y⟩ steps ∧
    step 10 prog ⟨pc, y⟩ = .halt 0 ∧ steps + 1 ≤ K * bound ∧
    Realization.memoryState frontier y =
      (DataStructure.Memory.spec 10).clientState (DataStructure.Memory.State.init G.encode)
        Fibonacci.run ∧
    ((List.finRange G.n).map fun v => y.mem (G.outAddr v)) = distances ∧
    y.regs frontier = endFrontier

/-- The same native program and clock factor handle all three original graph cases, preserving
whole memory/frontier. In particular the edgeless five-vertex case uses the sharper `K*3`
bound, rather than the textbook `K*15`. No emitter is chosen after seeing a runtime graph. -/
example : ∃ r K pc, ∃ prog : Program .exact r, ∃ frontier : Fin r,
    NativeCase prog pc K frontier graph 10 [1, 4, 2] 50 ∧
    NativeCase prog pc K frontier edgeless 2 [1, 0] 31 ∧
    NativeCase prog pc K frontier sparseEdgeless 3 [1, 0, 0, 0, 0] 64 := by
  obtain ⟨r, K, pc, prog, frontier, he⟩ :=
    Fibonacci.exists_program_state
  refine ⟨r, K, pc, prog, frontier, ?_, ?_, ?_⟩
  · obtain ⟨y, steps, hr, hh, hm, ht, _⟩ := he graph 10 fits_graph
    have hn : graph.m + min graph.n (graph.m + 1) * (Nat.log 2 graph.n + 1) = 10 := by
      decide +kernel
    rw [hn] at ht
    refine ⟨y, steps, hr, hh, ht, ?_, ?_, ?_⟩
    · with_reducible exact hm
    · exact (congrArg (fun m : ℕ → ℕ =>
        (List.finRange graph.n).map fun v => m (graph.outAddr v))
        (congrArg DataStructure.Memory.State.mem hm)).trans graph_source_result.1
    · exact (congrArg DataStructure.Memory.State.frontier hm).trans graph_source_result.2
  · obtain ⟨y, steps, hr, hh, hm, ht, _⟩ := he edgeless 10 (by decide)
    have hn : edgeless.m + min edgeless.n (edgeless.m + 1) *
        (Nat.log 2 edgeless.n + 1) = 2 := by decide +kernel
    rw [hn] at ht
    refine ⟨y, steps, hr, hh, ht, ?_, ?_, ?_⟩
    · with_reducible exact hm
    · exact (congrArg (fun m : ℕ → ℕ =>
        (List.finRange edgeless.n).map fun v => m (edgeless.outAddr v))
        (congrArg DataStructure.Memory.State.mem hm)).trans edgeless_source_result.1
    · exact (congrArg DataStructure.Memory.State.frontier hm).trans edgeless_source_result.2
  · obtain ⟨y, steps, hr, hh, hm, ht, _⟩ := he sparseEdgeless 10 fits_sparseEdgeless
    have hn : sparseEdgeless.m + min sparseEdgeless.n (sparseEdgeless.m + 1) *
        (Nat.log 2 sparseEdgeless.n + 1) = 3 := by decide +kernel
    rw [hn] at ht
    refine ⟨y, steps, hr, hh, ht, ?_, ?_, ?_⟩
    · with_reducible exact hm
    · exact (congrArg (fun m : ℕ → ℕ =>
        (List.finRange sparseEdgeless.n).map fun v => m (sparseEdgeless.outAddr v))
        (congrArg DataStructure.Memory.State.mem hm)).trans sparse_source_result.1
    · exact (congrArg DataStructure.Memory.State.frontier hm).trans sparse_source_result.2

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
