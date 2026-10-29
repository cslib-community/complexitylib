/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.FibonacciStatement
public import Complexity.Algorithms.WordRAM.Dijkstra.GenericPQ
public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

/-!
# Dijkstra's Algorithm with a Fibonacci Heap in `O(m + n (⌊log₂ n⌋ + 1))` Time

This file instantiates the black-box outer Dijkstra algorithm
(`Cslib.Algorithms.WordRAM.Dijkstra.dijkstraCode_exec` and
`Cslib.Algorithms.WordRAM.Dijkstra.dijkstra_of_pq_spec`) with the standalone static-array
Fibonacci heap package (`Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.pkg`) to obtain both
the sharper reachable-vertex bound `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciSpec`
(`O(m + min(n, m + 1) (⌊log₂ n⌋ + 1))`) and the textbook Fredman–Tarjan bound
`Cslib.Algorithms.WordRAM.Dijkstra.FibonacciStatement` (`O(m + n (⌊log₂ n⌋ + 1))`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.fibDijkstra`: structured exact-basis Dijkstra program
  instantiated with `PriorityQueue.FibonacciHeap.code`.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.fibDijkstra_spec`: structured execution bound
  `640 * (m + min(n, m + 1) * (⌊log₂ n⌋ + 1))`.
* `Cslib.Algorithms.WordRAM.Dijkstra.fibonacciSpec`: compiled flat-program reachable-vertex
  specification `FibonacciSpec (fibDijkstra.program OuterReg.zero) 640`.
* `Cslib.Algorithms.WordRAM.Dijkstra.fibonacciLinearSpec`: compiled flat-program textbook
  specification `FibonacciLinearSpec (fibDijkstra.program OuterReg.zero) 640`.
* `Cslib.Algorithms.WordRAM.Dijkstra.fibonacciSpecStatement`: existential reachable-vertex theorem.
* `Cslib.Algorithms.WordRAM.Dijkstra.fibonacciStatement`: textbook `O(m + n log n)` main theorem.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987], Section 4 (pp. 609–610).
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 24.3 (p. 662).
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

/-- Structured exact-basis Dijkstra program instantiated with the standalone Fibonacci heap. -/
abbrev fibDijkstra : Code .exact (15 + PriorityQueue.FibonacciHeap.rFib) :=
  dijkstraCode PriorityQueue.FibonacciHeap.code

private theorem fits_fib_space {G : ListInstance} {w : ℕ}
    (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    Fits w (G.dbase + G.n + PriorityQueue.FibonacciHeap.pkg.space G.n) := by
  apply hw.of_le
  dsimp only [ListInstance.dbase, PriorityQueue.FibonacciHeap.pkg,
    PriorityQueue.FibonacciHeap.space]
  nlinarith [Nat.zero_le G.maxWeight]

private theorem fibonacciHeap_dijkstra_bound (G : ListInstance) :
    PriorityQueue.FibonacciHeap.pkg.initTime G.n +
      PriorityQueue.FibonacciHeap.pkg.insertTime G.n + 28 +
      min G.n (G.m + 1) * (PriorityQueue.FibonacciHeap.pkg.extractTime G.n +
        PriorityQueue.FibonacciHeap.pkg.emptyTime G.n + 20) +
      min G.n G.m * (PriorityQueue.FibonacciHeap.pkg.insertTime G.n + 20) +
      G.m * (PriorityQueue.FibonacciHeap.pkg.decreaseTime G.n + 20) + 1 ≤
      640 * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1)) := by
  dsimp only [PriorityQueue.FibonacciHeap.pkg, PriorityQueue.FibonacciHeap.tInit,
    PriorityQueue.FibonacciHeap.tEmpty, PriorityQueue.FibonacciHeap.tIns,
    PriorityQueue.FibonacciHeap.tDec, PriorityQueue.FibonacciHeap.tExt]
  let k := min G.n (G.m + 1)
  let L := Nat.log 2 G.n + 1
  have hn : 1 ≤ G.n := by have := G.source.isLt; omega
  have hk : 1 ≤ k := le_min hn (Nat.succ_pos G.m)
  have hL : 1 ≤ L := Nat.succ_pos _
  have hkL : 1 ≤ k * L := Nat.mul_pos hk hL
  have hext : k * (420 * L + 12 + 20) ≤ 452 * (k * L) := by
    have h32 : 420 * L + 12 + 20 ≤ 452 * L := by omega
    calc
      k * (420 * L + 12 + 20) ≤ k * (452 * L) := Nat.mul_le_mul_left k h32
      _ = 452 * (k * L) := by ring
  have hins : min G.n G.m * (130 + 20) ≤ 150 * G.m := by
    have := Nat.min_le_right G.n G.m
    omega
  change 26 + 130 + 28 + k * (420 * L + 12 + 20) + min G.n G.m * (130 + 20) +
    G.m * (340 + 20) + 1 ≤ 640 * (G.m + k * L)
  omega

/-- **Correctness and running time of structured Dijkstra with a Fibonacci heap.** -/
theorem fibDijkstra_spec {G : ListInstance} {w : ℕ}
    (hw : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    ∃ y, ExecWithin w fibDijkstra (.init G.encode) y
        (640 * (G.m + min G.n (G.m + 1) * (Nat.log 2 G.n + 1))) ∧
      ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨y, he, hd⟩ :=
    dijkstraCode_exec PriorityQueue.FibonacciHeap.pkg G w hw (fits_fib_space hw)
  exact ⟨y, he.mono (Nat.le_of_succ_le (fibonacciHeap_dijkstra_bound G)), hd⟩

/-- **Dijkstra's algorithm with a Fibonacci heap in `O(m + min(n, m + 1) (⌊log₂ n⌋ + 1))` time.**
The compiled flat program meets `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciSpec` with `K = 640`. -/
theorem fibonacciSpec : FibonacciSpec (fibDijkstra.program OuterReg.zero) 640 := by
  intro G w hw
  obtain ⟨t, steps, hr, hh, hsteps, hd⟩ :=
    dijkstra_of_pq_spec PriorityQueue.FibonacciHeap.pkg G w hw (fits_fib_space hw)
  exact ⟨t, steps, hr, hh,
    (Nat.add_le_add_right hsteps 1).trans (fibonacciHeap_dijkstra_bound G), hd⟩

/-- **Dijkstra's algorithm with a Fibonacci heap in `O(m + n (⌊log₂ n⌋ + 1))` time.** The compiled
flat program meets `Cslib.Algorithms.WordRAM.Dijkstra.FibonacciLinearSpec` with `K = 640`. -/
theorem fibonacciLinearSpec : FibonacciLinearSpec (fibDijkstra.program OuterReg.zero) 640 :=
  fibonacciSpec.toLinearSpec

/-- **Reachable-vertex Fibonacci-heap Dijkstra theorem.** -/
theorem fibonacciSpecStatement : FibonacciSpecStatement :=
  ⟨15 + PriorityQueue.FibonacciHeap.rFib, fibDijkstra.program OuterReg.zero, 640, fibonacciSpec⟩

/-- **Fibonacci-heap Dijkstra main theorem.** Some word-RAM program over the exact basis computes
all shortest-path distances from the source of a weighted directed graph with `n` vertices and `m`
edges, given by adjacency lists, within `O(m + n (⌊log₂ n⌋ + 1))` instructions. -/
theorem fibonacciStatement : FibonacciStatement :=
  ⟨15 + PriorityQueue.FibonacciHeap.rFib, fibDijkstra.program OuterReg.zero, 640,
    fibonacciLinearSpec⟩

end Cslib.Algorithms.WordRAM.Dijkstra
