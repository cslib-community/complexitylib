/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Algorithms.Lean.Dijkstra.Memory

/-!
# Dijkstra's algorithm with a binary heap, run on the word RAM's input convention

The graph of `ComplexityTests/Dijkstra.lean`, with a parallel edge and a shorter path through a
third vertex, is written in the input convention and given to `Dijkstra.Memory.run` at word size
`16`. The tests check the distances it leaves past the input, the admissibility of every memory
operation, its exact memory cost against the proved bound `memCost 3 4 = 520`, and that
`run_spec` applies to this graph.
-/

open Cslib.WordRAM Cslib.DataStructure
open Cslib.Algorithms.WordRAM.Dijkstra (ListInstance encodeDist)
open Cslib.Algorithms.Lean.Dijkstra.Memory

set_option linter.hashCommand false

namespace DijkstraMemoryTests

/-- Edges `0 → 1` of weights `4` and `5`, `0 → 2` of weight `1`, and `2 → 1` of weight `2`, from
source `0`. The distances are `0`, `3` and `1`. -/
def graph : ListInstance where
  n := 3
  adj := ![[(1, 4), (2, 1), (1, 5)], [], [(1, 2)]]
  source := 0

/-- The input words: `n`, the source, four offsets and four edges. -/
example : graph.encode = [3, 0, 0, 3, 3, 4, 1, 4, 2, 1, 1, 5, 1, 2] := by decide

/-- The memory of the input convention. -/
def input : Memory.State := Memory.State.init graph.encode

-- The cells just past the input hold the encoded distances `0 + 1`, `3 + 1` and `1 + 1`.
#guard (List.finRange 3).map (fun v =>
  ((Memory.spec 16).clientState input run).mem (graph.outAddr v)) = [1, 4, 2]

-- Every memory operation of the run is admissible at word size `16`.
#guard decide ((Memory.spec 16).ValidHistory input ((Memory.spec 16).clientHistory input run))

-- Its exact memory cost, within `memCost 3 4 = 520`.
#guard (Memory.spec 16).totalCost Memory.charge input
  ((Memory.spec 16).clientHistory input run) = 75

example : memCost 3 4 = 520 := by decide

/-- The word size `16` holds `8 (n + m + 2) (W + 2) = 504`, so `run_spec` applies. -/
theorem fits : Fits 16 (8 * (graph.n + graph.m + 2) * (graph.maxWeight + 2)) := by decide

/-- By `run_spec`, the cell of vertex `1` holds its encoded distance. -/
example : ((Memory.spec 16).clientState input run).mem (graph.outAddr ⟨1, by decide⟩) =
    encodeDist (graph.dist graph.source ⟨1, by decide⟩) :=
  (run_spec graph fits).2.1 _

/-- A word size too small for the input: `504` does not fit eight bits. -/
example : ¬Fits 8 (8 * (graph.n + graph.m + 2) * (graph.maxWeight + 2)) := by decide

end DijkstraMemoryTests
