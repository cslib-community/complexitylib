/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.Constraints
import Complexity.Tactic.PolyTime

/-! Fixed-alphabet tabulation of unbounded executable descriptors and exact graph interpretation. -/

namespace ComplexityTests.PCPEncodedConstraints

open Cslib Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

-- The source descriptor is an unbounded bit string, not a fixed finite type.
private def evalBits (bits : List Bool) (a b : Bool) : Bool :=
  bits[(if a then 2 else 0) + (if b then 1 else 0)]?.getD false

private theorem isPolyTime_evalBits :
    ComputableInPolyTime (fun p : List Bool × Bool × Bool => evalBits p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBool encBool)) encBool := by
  unfold evalBits
  polytime

private def graph : Graph (List Bool) :=
  ⟨2, [⟨0, 1, [true, false, true, true]⟩, ⟨1, 1, []⟩,
    ⟨0, 1, [false, true, false, false, true]⟩]⟩

private def normalized : Graph (Bool → Bool → Bool) := graph.mapConstraints evalBits

example : normalized.vertices = 2 ∧ normalized.edges.length = 3 := by decide

example : normalized.edges.map (fun e => (e.src, e.dst)) = [(0, 1), (1, 1), (0, 1)] := by
  decide

example : normalized.edges.map (fun e => e.constraint false true) = [false, false, true] := by
  decide

example : normalized.edges.map (fun e => e.constraint true false) = [true, false, false] := by
  decide

example : normalized.WellFormed := by
  rw [normalized, Graph.wellFormed_mapConstraints_iff]
  simp [Graph.WellFormed, graph]

example : (normalized.toGraph (fun table => table)).unsatVal = (graph.toGraph evalBits).unsatVal :=
  graph.unsatVal_mapConstraints evalBits (fun table => table)

example : (normalized.toGraph (fun table => table)).Satisfiable ↔
    (graph.toGraph evalBits).Satisfiable :=
  graph.satisfiable_mapConstraints_iff evalBits (fun table => table)

example : normalized.mapConstraints (fun table => table) = normalized :=
  Graph.mapConstraints_id normalized

example : ComputableInPolyTime (Graph.mapConstraints evalBits)
    (Graph.encoding encBits) (Graph.encoding (encPi (encPi encBool))) :=
  Graph.isPolyTime_tabulateConstraints isPolyTime_evalBits

-- Equivalent functional spelling uses constructor, projection, mapping, and finite-Pi certificates.
example : ComputableInPolyTime (fun g : Graph (List Bool) =>
      Graph.mk g.vertices (g.edges.map fun e => Edge.mk e.src e.dst (evalBits e.constraint)))
    (Graph.encoding encBits) (Graph.encoding (encPi (encPi encBool))) := by
  have htable := Graph.isPolyTime_constraintTable isPolyTime_evalBits
  fun_prop

example : (encPi (encPi encBool) (evalBits [true, false, true, true])).length = 26 := by
  decide

-- Table lookup is itself certified for runtime table and both runtime symbols.
example : ComputableInPolyTime
    (fun p : (Bool → Bool → Bool) × Bool × Bool => p.1 p.2.1 p.2.2)
    (encPair (encPi (encPi encBool)) (encPair encBool encBool)) encBool := by
  fun_prop

end ComplexityTests.PCPEncodedConstraints
