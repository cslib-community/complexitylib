/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver for polynomial-time graph counting)

import CslibFrontier.Computability.Complexity.Problems.Graph.WeightedSpanningTrees
import CslibFrontier.Computability.Complexity.Problems.Graph.Arborescences
import CslibFrontier.Computability.Complexity.Problems.Graph.EulerianCircuits

/-!
# Kernel-checked tests for polynomial-time graph counting via determinants

Nonvacuous tests for `WeightedSpanningTrees`, `Arborescences`, and `EulerianCircuits`, checking
exact counts via kernel reduction (`decide`) alongside their `ComputableInPolyTime` certificates.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.MatrixTreePolyTime

open Cslib.Complexity Turing MultiTapeTM

section WeightedSpanningTrees

private def weightedTri : WeightedGraph :=
  { vertices := [0, 1, 2], edges := [⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨2, 0, 5⟩] }

private def signedWeightedTri : WeightedGraph :=
  { vertices := [0, 1, 2], edges := [⟨0, 1, -2⟩, ⟨1, 2, 3⟩, ⟨2, 0, 5⟩] }

private def parallelLoopEdge : WeightedGraph :=
  { vertices := [0, 1], edges := [⟨0, 0, 99⟩, ⟨0, 1, 2⟩, ⟨1, 0, 3⟩] }

-- Distinct positive weights `2, 3, 5` on `K₃`: weighted spanning-tree sum `2*3 + 2*5 + 3*5 = 31`.
example : weightedTri.weightedSpanningTreeCount = 31 := by decide

-- Transfer via `weightedSpanningTreeCount_eq_finsum` to the mathematical `finsum` expression.
example :
    (∑ᶠ (T : SimpleGraph {v // v ∈ weightedTri.vertices})
        (_ : T ≤ weightedTri.toGraph.induced ∧ T.IsTree),
      ∏ᶠ e ∈ T.edgeSet, weightedTri.symWeight (e.map Subtype.val)) = 31 := by
  rw [← WeightedGraph.weightedSpanningTreeCount_eq_finsum]
  decide

-- Negative weight `-2` gives `(-2)*3 + (-2)*5 + 3*5 = -1`.
example : signedWeightedTri.weightedSpanningTreeCount = -1 := by decide

-- Self-loops are ignored and parallel / reversed pairs sum additively (`2 + 3 = 5`).
example : parallelLoopEdge.pairWeight 0 1 = 5 ∧
    parallelLoopEdge.weightedSpanningTreeCount = 5 := by decide

-- Empty vertex list has weighted spanning-tree sum `0`.
example :
    ({ vertices := [], edges := [⟨0, 1, 5⟩] } : WeightedGraph).weightedSpanningTreeCount = 0 := by
  decide

example :
    ComputableInPolyTime
      (fun WG : WeightedGraph =>
        ∑ᶠ (T : SimpleGraph {v // v ∈ WG.vertices}) (_ : T ≤ WG.toGraph.induced ∧ T.IsTree),
          ∏ᶠ e ∈ T.edgeSet, WG.symWeight (e.map Subtype.val))
      encWeightedGraph encIntBin :=
  WeightedGraph.computableInPolyTime_finsum_isTree

end WeightedSpanningTrees

section Arborescences

private def bal4Graph : Graph :=
  ⟨[0, 1, 2, 3], [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (2, 0)]⟩

private def doubled2Cycle : Graph :=
  ⟨[0, 1], [(0, 1), (0, 1), (1, 0), (1, 0)]⟩

private def unbalancedMulti : Graph :=
  ⟨[0, 1], [(0, 1), (0, 1), (1, 0)]⟩

private def loopAndIsolated : Graph :=
  ⟨[0, 1], [(0, 0)]⟩

-- Simple digraph: balanced asymmetric 4-vertex digraph has `2` in-arborescences at every root
-- and `0` at undeclared vertex `99`.
example : bal4Graph.digraphInArborescenceCount 0 = 2 ∧
    bal4Graph.digraphInArborescenceCount 1 = 2 ∧
    bal4Graph.digraphInArborescenceCount 2 = 2 ∧
    bal4Graph.digraphInArborescenceCount 3 = 2 ∧
    bal4Graph.digraphInArborescenceCount 99 = 0 := by decide

example (h0 : 0 ∈ bal4Graph.1) :
    Nat.card {T : Digraph {v // v ∈ bal4Graph.1} //
      T ≤ bal4Graph.toDigraph ∧ T.IsInArborescence ⟨0, h0⟩} = 2 := by
  have h := bal4Graph.digraphInArborescenceCount_eq_natCard 0
  rw [dite_eq_left h0] at h
  exact h.symm.trans (by decide)

-- Multidigraph counts distinguish parallel arcs (`2` on doubled 2-cycle), unbalanced root
-- dependence (`1` at `0` vs `2` at `1`), and isolated vertices (`0`).
example : doubled2Cycle.multiInArborescenceCount 0 = 2 ∧
    doubled2Cycle.multiInArborescenceCount 1 = 2 ∧
    unbalancedMulti.multiInArborescenceCount 0 = 1 ∧
    unbalancedMulti.multiInArborescenceCount 1 = 2 ∧
    loopAndIsolated.multiInArborescenceCount 0 = 0 ∧
    loopAndIsolated.multiInArborescenceCount 99 = 0 := by decide

example (h0 : 0 ∈ doubled2Cycle.1) :
    Nat.card {f : {v : {v // v ∈ doubled2Cycle.1} // v ≠ ⟨0, h0⟩} →
        Fin doubled2Cycle.validArcs.length //
      Cslib.Multidigraph.IsInArborescence doubled2Cycle.arcSrc doubled2Cycle.arcTgt
        ⟨0, h0⟩ f} = 2 := by
  have h := doubled2Cycle.multiInArborescenceCount_eq_natCard 0
  rw [dite_eq_left h0] at h
  exact h.symm.trans (by decide)

example :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if hr : p.2 ∈ p.1.1 then
          Nat.card {T : Digraph {v // v ∈ p.1.1} //
            T ≤ p.1.toDigraph ∧ T.IsInArborescence ⟨p.2, hr⟩}
        else 0)
      (encPair encGraph encNat) encNat :=
  Graph.computableInPolyTime_natCard_digraphIsInArborescence

example :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if hr : p.2 ∈ p.1.1 then
          Nat.card {f : {v : {v // v ∈ p.1.1} // v ≠ ⟨p.2, hr⟩} → Fin p.1.validArcs.length //
            Cslib.Multidigraph.IsInArborescence p.1.arcSrc p.1.arcTgt ⟨p.2, hr⟩ f}
        else 0)
      (encPair encGraph encNat) encNat :=
  Graph.computableInPolyTime_natCard_multiIsInArborescence

end Arborescences

section EulerianCircuits

private def twoCycleWithLoop : Graph :=
  ⟨[0, 1], [(0, 1), (1, 0), (0, 0)]⟩

private def bidirectedK3 : Graph :=
  ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0), (0, 2), (2, 1), (1, 0)]⟩

-- BEST counts: doubled `2`-cycle has `2`, `2`-cycle + loop has `1`, bidirected `K₃` has `3`,
-- loop + isolated vertex has `1` circuit (via `activeVertices`), unbalanced has `0`,
-- and out-of-range index has `0`.
example : doubled2Cycle.eulerianCircuitCount 0 = 2 ∧
    doubled2Cycle.eulerianCircuitCount 2 = 2 ∧
    twoCycleWithLoop.eulerianCircuitCount 0 = 1 ∧
    bidirectedK3.eulerianCircuitCount 0 = 3 ∧
    bidirectedK3.eulerianCircuitCount 3 = 3 ∧
    loopAndIsolated.eulerianCircuitCount 0 = 1 ∧
    unbalancedMulti.eulerianCircuitCount 0 = 0 ∧
    doubled2Cycle.eulerianCircuitCount 10 = 0 := by decide

example (he : 0 < loopAndIsolated.validArcs.length) :
    Nat.card {l : List (Fin loopAndIsolated.validArcs.length) //
      Cslib.Multidigraph.IsEulerianCircuit loopAndIsolated.arcSrc loopAndIsolated.arcTgt
        ⟨0, he⟩ l} = 1 := by
  have h := loopAndIsolated.eulerianCircuitCount_eq_natCard 0
  rw [dite_eq_left he] at h
  exact h.symm.trans (by decide)

example :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if he : p.2 < p.1.validArcs.length then
          Nat.card {l : List (Fin p.1.validArcs.length) //
            Cslib.Multidigraph.IsEulerianCircuit p.1.arcSrc p.1.arcTgt ⟨p.2, he⟩ l}
        else 0)
      (encPair encGraph encNat) encNat :=
  Graph.computableInPolyTime_natCard_isEulerianCircuit

end EulerianCircuits

end CslibFrontierTests.MatrixTreePolyTime
