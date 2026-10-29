/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import Complexity.Computability.PCP.Encoded.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Tactic.PolyTime

/-! Logarithmic graph loops using the existing iteration calculus and complete encoding bounds. -/

namespace ComplexityTests.PCPEncodedIteration

open Cslib.PCP.Encoded Turing.MultiTapeTM

-- The loop remains an application of the existing calculus; the graph lemmas supply its bound.
example {C Input : Type} {enc : C ↪ List Bool} {input : Input ↪ List Bool}
    {graph : Input → Graph C} {step : Graph C → Graph C} {valid : Graph C → Prop}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding enc))
    (hstep : ComputableInPolyTime step (Graph.encoding enc) (Graph.encoding enc))
    (factor descriptorBound : ℕ)
    (hbase : ∀ x, valid (graph x)) (hvalid : ∀ g, valid g → valid (step g))
    (hwellFormed : ∀ g, valid g → g.WellFormed)
    (hdescriptors : ∀ g, valid g → ∀ edge ∈ g.edges,
      (enc edge.constraint).length ≤ descriptorBound)
    (hgrowth : ∀ g, valid g →
      (step g).vertices + (step g).edges.length ≤ factor * (g.vertices + g.edges.length)) :
    ComputableInPolyTime
      (fun x => step^[Nat.clog 2 (graph x).edges.length] (graph x)) input (Graph.encoding enc) := by
  refine .of_tidy ?_
  have hcount : ComputableInPolyTime (fun x => Nat.clog 2 (graph x).edges.length) input encUnary :=
    by fun_prop
  apply ComputableTidilyInPolyTime.iterate hcount.tidy hgraph.tidy hstep.tidy
    (Graph.polyBounded_iterationSize_clog hgraph factor descriptorBound)
  exact fun x _ hi => Graph.iterate_length_encoding_le factor descriptorBound
    hvalid hwellFormed hdescriptors hgrowth (hbase x) hi

private def doubleEdges (g : Graph Bool) : Graph Bool := ⟨g.vertices, g.edges ++ g.edges⟩

private theorem isPolyTime_doubleEdges : ComputableInPolyTime doubleEdges
    (Graph.encoding encBool) (Graph.encoding encBool) := by
  unfold doubleEdges
  polytime

private theorem wellFormed_doubleEdges {g : Graph Bool} (hg : g.WellFormed) :
    (doubleEdges g).WellFormed := by
  simpa only [Graph.WellFormed, doubleEdges, List.mem_append, or_self, forall_const] using hg

private theorem growth_doubleEdges (g : Graph Bool) :
    (doubleEdges g).vertices + (doubleEdges g).edges.length ≤
      2 * (g.vertices + g.edges.length) := by
  simp only [doubleEdges, List.length_append]
  lia

-- Arbitrary computed well-formed graphs can be iterated, retaining their original input encoding.
example {Input : Type} {input : Input ↪ List Bool} {graph : Input → Graph Bool}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding encBool))
    (hwellFormed : ∀ x, (graph x).WellFormed) :
    ComputableInPolyTime
      (fun x => doubleEdges^[Nat.clog 2 (graph x).edges.length] (graph x))
      input (Graph.encoding encBool) := by
  refine .of_tidy ?_
  have hcount : ComputableInPolyTime (fun x => Nat.clog 2 (graph x).edges.length) input encUnary :=
    by fun_prop
  apply ComputableTidilyInPolyTime.iterate hcount.tidy hgraph.tidy isPolyTime_doubleEdges.tidy
    (Graph.polyBounded_iterationSize_clog hgraph 2 1)
  exact fun x _ hi => Graph.iterate_length_encoding_le (valid := Graph.WellFormed) 2 1
    (fun _ => wellFormed_doubleEdges) (fun _ h => h) (by intros; simp)
    (fun g _ => growth_doubleEdges g) (hwellFormed x) hi

private def graph : Graph Bool :=
  ⟨2, [⟨0, 1, true⟩, ⟨1, 1, false⟩, ⟨0, 1, false⟩]⟩

example : (doubleEdges^[Nat.clog 2 graph.edges.length] graph).edges.length = 12 := by decide
example : (Graph.encoding encBool
    (doubleEdges^[Nat.clog 2 graph.edges.length] graph)).length = 153 := by
  rw [Graph.length_encoding]
  decide
example : (doubleEdges^[Nat.clog 2 graph.edges.length] graph).isWellFormed = true := by decide

-- Zero growth factors must still charge the initial state, even if the selected count is positive.
example : (Graph.encoding encBool graph).length ≤ Graph.iterationSize 0 1 2 graph := by
  exact Graph.iterate_length_encoding_le (step := fun _ => ⟨0, []⟩)
    (valid := Graph.WellFormed) 0 1 (by intros; simp [Graph.WellFormed]) (fun _ h => h)
    (by intros; simp) (by intros; simp) (by simp [Graph.WellFormed]) (show 0 ≤ 2 by decide)

-- Empty-edge inputs choose zero rounds and retain isolated declared vertices.
example : (doubleEdges^[Nat.clog 2 (Graph.mk 5 ([] : List (Edge Bool))).edges.length]
    ⟨5, []⟩).vertices = 5 := by decide

end ComplexityTests.PCPEncodedIteration
