/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Dijkstra.FibonacciStatement
import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci

/-!
# Dijkstra's Algorithm with a Fibonacci Heap in `O(m + n (⌊log₂ n⌋ + 1))` Time

The unchanged reachable-vertex and textbook endpoint statements now follow from
`Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci.exists_program_state`. One native exact-basis
flat program and instruction factor precede every graph and word size. The original graph
encoding, word envelope and shortest-path semantics are unchanged. Its actual input prefix,
body and halt are charged, and the stronger endpoint retains the complete final source memory
and frontier. Initialization reserves the input's zero tail without a linear clearing pass.

The old `fibDijkstra` implementation and its implementation-specific `fibDijkstra_spec`,
`fibonacciSpec` and `fibonacciLinearSpec` helpers at coefficient `640` are superseded. That
coefficient is not asserted for the native witness; the original public statements already
quantify over one uniform factor. The separate indexed Fibonacci execution core is retained for
its remaining clients.

## Main results

* `fibonacciSpecStatement`: the original sharper reachable-vertex endpoint.
* `fibonacciStatement`: the original textbook `O(m + n log n)` endpoint.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987], Section 4 (pp. 609–610).
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 24.3 (p. 662).
-/

public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

/-- **Reachable-vertex Fibonacci-heap Dijkstra theorem.** -/
theorem fibonacciSpecStatement : FibonacciSpecStatement := by
  obtain ⟨r, C, pc, prog, _, he⟩ :=
    Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci.exists_program_state
  refine ⟨r, prog, C, ?_⟩
  intro G w hw
  obtain ⟨y, steps, hrun, hhalt, _, htime, hdist⟩ := he G w hw
  exact ⟨⟨pc, y⟩, steps, hrun, ⟨0, hhalt⟩, htime, hdist⟩

/-- **Fibonacci-heap Dijkstra main theorem.** Some word-RAM program over the exact basis computes
all shortest-path distances from the source of a weighted directed graph with `n` vertices and `m`
edges, given by adjacency lists, within `O(m + n (⌊log₂ n⌋ + 1))` instructions. -/
theorem fibonacciStatement : FibonacciStatement := by
  obtain ⟨r, prog, C, h⟩ := fibonacciSpecStatement
  exact ⟨r, prog, C, h.toLinearSpec⟩

end Cslib.Algorithms.WordRAM.Dijkstra
