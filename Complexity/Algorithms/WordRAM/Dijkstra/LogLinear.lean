/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.GenericPQ
public import Complexity.Algorithms.WordRAM.PriorityQueue.BinaryHeap

/-!
# Dijkstra's Algorithm with a Binary Heap in `O((m + 1) (⌊log₂ n⌋ + 1))` Time

This file instantiates the black-box outer Dijkstra algorithm
(`Cslib.Algorithms.WordRAM.Dijkstra.dijkstraCode_exec` and
`Cslib.Algorithms.WordRAM.Dijkstra.dijkstra_of_pq_spec`) with the standalone word-RAM binary
min-heap package (`Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.pkg`) to obtain
`Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec` and
`Cslib.Algorithms.WordRAM.Dijkstra.LogLinearStatement` with zero priority-queue code coupled to
Dijkstra's algorithm.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra`: structured exact-basis Dijkstra program
  instantiated with `PriorityQueue.BinaryHeap.pqCode`.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra_spec`: structured execution bound
  `200 * (m + 1) * (⌊log₂ n⌋ + 1)`.
* `Cslib.Algorithms.WordRAM.Dijkstra.logLinearSpec`: compiled flat-program specification
  `LogLinearSpec (heapDijkstra.program OuterReg.zero) 230`.
* `Cslib.Algorithms.WordRAM.Dijkstra.logLinearStatement`: the log-linear main theorem.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

/-- Structured exact-basis Dijkstra program instantiated with the standalone binary min-heap. -/
abbrev heapDijkstra : Code .exact (15 + PriorityQueue.BinaryHeap.rBin) :=
  dijkstraCode PriorityQueue.BinaryHeap.pqCode

private theorem fits_pq_space {G : ListInstance} {w : ℕ}
    (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    Fits w (G.dbase + G.n + PriorityQueue.BinaryHeap.pkg.space G.n) := by
  apply hw.of_le
  dsimp only [ListInstance.dbase, PriorityQueue.BinaryHeap.pkg, PriorityQueue.BinaryHeap.space]
  nlinarith [Nat.zero_le G.maxWeight]

private theorem binaryHeap_dijkstra_bound (G : ListInstance) :
    PriorityQueue.BinaryHeap.pkg.initTime G.n +
      PriorityQueue.BinaryHeap.pkg.insertTime G.n + 28 +
      min G.n (G.m + 1) * (PriorityQueue.BinaryHeap.pkg.extractTime G.n +
        PriorityQueue.BinaryHeap.pkg.emptyTime G.n + 20) +
      min G.n G.m * (PriorityQueue.BinaryHeap.pkg.insertTime G.n + 20) +
      G.m * (PriorityQueue.BinaryHeap.pkg.decreaseTime G.n + 20) ≤
      200 * (G.m + 1) * (Nat.log 2 G.n + 1) := by
  dsimp only [PriorityQueue.BinaryHeap.pkg, PriorityQueue.BinaryHeap.tEmpty,
    PriorityQueue.BinaryHeap.tIns, PriorityQueue.BinaryHeap.tDec, PriorityQueue.BinaryHeap.tExt]
  have hm1 := Nat.mul_le_mul_right (46 * Nat.log 2 G.n + 28 + 10 + 20)
    (Nat.min_le_right G.n (G.m + 1))
  have hm2 := Nat.mul_le_mul_right (28 * Nat.log 2 G.n + 20 + 20) (Nat.min_le_right G.n G.m)
  nlinarith [Nat.zero_le (G.m * Nat.log 2 G.n)]

/-- **Correctness and running time of structured Dijkstra with a binary heap.** -/
theorem heapDijkstra_spec {G : ListInstance} {w : ℕ}
    (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    ∃ y, ExecWithin w heapDijkstra (.init G.encode) y
        (200 * (G.m + 1) * (Nat.log 2 G.n + 1)) ∧
      ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨y, he, hd⟩ :=
    dijkstraCode_exec PriorityQueue.BinaryHeap.pkg G w hw (fits_pq_space hw)
  exact ⟨y, he.mono (binaryHeap_dijkstra_bound G), hd⟩

/-- **Dijkstra's algorithm with a binary heap in `O((m + 1) (⌊log₂ n⌋ + 1))` time.** The
compiled program meets `Cslib.Algorithms.WordRAM.Dijkstra.LogLinearSpec` with `K = 230`. -/
theorem logLinearSpec : LogLinearSpec (heapDijkstra.program OuterReg.zero) 230 := by
  intro G w hw
  obtain ⟨t, steps, hr, hh, hsteps, hd⟩ :=
    dijkstra_of_pq_spec PriorityQueue.BinaryHeap.pkg G w hw (fits_pq_space hw)
  refine ⟨t, steps, hr, hh, ?_, hd⟩
  have hb := binaryHeap_dijkstra_bound G
  have hpos : 1 ≤ (G.m + 1) * (Nat.log 2 G.n + 1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  linarith

/-- **Log-linear main theorem.** Some word-RAM program over the exact basis computes all
shortest-path distances from the source of a weighted directed graph with `n` vertices and `m`
edges, given by adjacency lists, within `O((m + 1) (⌊log₂ n⌋ + 1))` instructions. -/
theorem logLinearStatement : LogLinearStatement :=
  ⟨15 + PriorityQueue.BinaryHeap.rBin, heapDijkstra.program OuterReg.zero, 230, logLinearSpec⟩

end Cslib.Algorithms.WordRAM.Dijkstra
