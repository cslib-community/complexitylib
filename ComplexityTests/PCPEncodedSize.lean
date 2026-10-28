/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import Complexity.Computability.PCP.Encoded.Size
import Complexity.Computability.PCP.Encoded.Constraints

/-! Full encoded graph sizes, alternative descriptor encodings, and essential bounds. -/

namespace ComplexityTests.PCPEncodedSize

open Cslib.PCP.Encoded Turing.MultiTapeTM

private def graph (word : List Bool) : Graph (List Bool) :=
  ⟨2, [⟨0, 1, word⟩, ⟨1, 1, []⟩, ⟨0, 1, [true]⟩]⟩

-- Distinct loop and parallel-edge entries keep all endpoint and list framing costs.
example : (Graph.encoding encBits (graph [true, false, true])).length = 44 := by decide
example : (Graph.encoding (encList encBool) (graph [true, false, true])).length = 60 := by
  decide

example : (Graph.encoding encBits (Graph.mk 0 [])).length = 1 := by decide
example : (Graph.encoding encBits (Graph.mk 7 [])).length = 15 := by decide

-- The formula also accounts for arbitrarily long descriptors, without a finite-type assumption.
example (word : List Bool) : (Graph.encoding encBits (graph word)).length =
    2 * word.length + 38 := by
  simp only [Graph.length_encoding, graph, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, encBits_apply, List.length_nil, List.length_cons]
  ring

example (word : List Bool) :
    (Graph.encoding encBits (graph word)).length ≤
      2 * (graph word).vertices + 1 + (graph word).edges.length *
        (8 * (graph word).vertices + 2 * (word.length + 1) + 5) := by
  apply Graph.WellFormed.length_encoding_le
  · simp [Graph.WellFormed, graph]
  · intro edge hedge
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl <;> simp

-- Both descriptor size and endpoint bounds are essential hypotheses.
example : ¬ (Graph.encoding encBits (Graph.mk 0 [⟨1, 1, []⟩])).length ≤ 6 := by decide
example : ¬ (Graph.encoding encBits
    (Graph.mk 1 [⟨0, 0, List.replicate 10 true⟩])).length ≤ 16 := by decide

private def tableGraph : Graph (Bool → Bool → Bool) :=
  (graph []).mapConstraints (fun _ a b => a == b)

-- The general bound can be reused for fixed tables without another specialized source lemma.
example :
    (Graph.encoding (encPi (encPi encBool)) tableGraph).length ≤
      2 * tableGraph.vertices + 1 + tableGraph.edges.length *
        (8 * tableGraph.vertices + 2 * (Fintype.card Bool * (6 * Fintype.card Bool + 1)) + 5) := by
  have hg : tableGraph.WellFormed := by
    simp [tableGraph, graph, Graph.WellFormed, Graph.mapConstraints]
  exact hg.length_encoding_le _ _ fun edge _ => Graph.length_constraintTable_le edge.constraint

end ComplexityTests.PCPEncodedSize
