/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Dijkstra.HeapStatement
import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Binary

/-!
# Dijkstra's algorithm with a natively realized binary heap

The existing `LogLinearStatement` is a projection of the native memory-client endpoint
`Cslib.Algorithms.Lean.Dijkstra.Native.Binary.exists_program_state`. One exact-basis flat program
and instruction factor precede every runtime graph and word size. The original word envelope,
output addresses and shortest-path semantics are unchanged; the bound includes the input
prefix, native body and final halt. The underlying endpoint also retains the complete final
memory and frontier of the original memory program.

The old structured `heapDijkstra` implementation and its implementation-specific helpers
`heapDijkstra_spec` and `logLinearSpec`, with literal coefficients `200` and `230`, are
superseded. Those coefficients are not asserted for the new native witness. The unchanged
public endpoint already quantifies over one uniform constant.

## Main results

* `logLinearStatement`: the original log-linear statement, proved through native realization.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

/-- **Log-linear main theorem.** Some word-RAM program over the exact basis computes all
shortest-path distances from the source of a weighted directed graph with `n` vertices and `m`
edges, given by adjacency lists, within `O((m + 1) (⌊log₂ n⌋ + 1))` instructions. -/
theorem logLinearStatement : LogLinearStatement := by
  obtain ⟨r, C, pc, prog, _, he⟩ :=
    Cslib.Algorithms.Lean.Dijkstra.Native.Binary.exists_program_state
  refine ⟨r, prog, C, ?_⟩
  intro G w hw
  obtain ⟨y, steps, hrun, hhalt, _, htime, hdist⟩ := he G w hw
  exact ⟨⟨pc, y⟩, steps, hrun, ⟨0, hhalt⟩, htime, hdist⟩

end Cslib.Algorithms.WordRAM.Dijkstra
