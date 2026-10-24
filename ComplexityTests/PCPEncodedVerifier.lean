/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.Verifier.Reduction
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Tactic.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-! Exact verifier behavior, padding, short words, repetition, and nonvacuous PCP contracts. -/

namespace ComplexityTests.PCPEncodedVerifier

open Cslib Cslib.PCP Cslib.PCP.Encoded Cslib.Complexity Turing.MultiTapeTM

private def decode (bits : Fin 1 → Bool) : Bool := bits 0

private def encode (bit : Bool) : Fin 1 → Bool := fun _ => bit

private def eval (constraint _ _ : Bool) : Bool := constraint

private def loop (constraint : Bool) : Graph Bool := ⟨1, [⟨0, 0, constraint⟩]⟩

private def mixed : Graph Bool := ⟨1, [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 0, true⟩]⟩

private def check := Graph.edgeVerifier 1 decode eval

private def repeatCheck := Graph.repeatedEdgeVerifier 1 3 decode eval

private theorem loop_wellFormed (bit : Bool) : (loop bit).WellFormed := by
  simp [Graph.WellFormed, loop]

private theorem loop_false_value : ((loop false).toGraph eval).unsatVal = 1 := by
  have hnot : ¬ ((loop false).toGraph eval).Satisfiable := by
    rintro ⟨σ, hσ⟩
    exact Bool.false_ne_true (hσ ⟨0, by decide⟩)
  apply le_antisymm (ConstraintGraph.unsatVal_le_one _)
  simpa [loop] using ((loop false).toGraph eval).inv_card_le_unsatVal hnot

example : (loop false).sampleEdge [] = some ⟨0, 0, false⟩ := by decide

example : mixed.sampleEdge [true, true] = none := by decide

example : mixed.sampleEdge (List.replicate 16 true) = none := by decide

example : check.coins mixed = 2 := by decide

example : check.queries (mixed, [false, false]) = [0, 0] := by decide

example : check.queries (mixed, [true, true]) = [0, 0] := by decide

example : check.accepts mixed [] [false, false] = false := by decide

example : check.accepts mixed [] [true, true] = true := by decide

example : check.accepts mixed [] (List.replicate 16 true) = true := by decide

example : check.accepts (loop false) [] [] = false := by decide

example : check.accepts (⟨0, []⟩ : Graph Bool) [] [] = true := by decide

example : repeatCheck.queries (mixed, [false, false, true, false, true, true]) =
    [0, 0, 0, 0, 0, 0] := by decide

example : repeatCheck.accepts mixed [] [true, false, true, true, false, false] = false := by decide

example : repeatCheck.accepts mixed [] [true, false, true, true, false, true] = true := by decide

-- This is the complete random-word count, including the accepting fourth padding index.
example : acceptCount (fun p => check.accepts p.1 [] p.2) mixed 2 = 3 := by decide

example : acceptCount (fun p => repeatCheck.accepts p.1 [] p.2) mixed 6 = 27 := by decide

example : 2 * acceptCount (fun p => repeatCheck.accepts p.1 [] p.2) mixed 6 ≤ 2 ^ 6 := by decide

example : (((BitString.uniformList 6).map
    (fun random => repeatCheck.accepts mixed [] random)) true).toReal = 27 / 64 := by
  rw [uniformList_acceptCount_toReal (fun p => repeatCheck.accepts p.1 [] p.2) mixed 6]
  norm_num [show acceptCount (fun p => repeatCheck.accepts p.1 [] p.2) mixed 6 = 27 by decide]

-- With a width-zero singleton alphabet, no proof bits are read; constraints are still checked.
example : (Graph.repeatedEdgeVerifier 0 2 (fun _ => ()) (fun c (_ _ : Unit) => c)).queries
    (loop false, []) = [] := by decide

example : (Graph.repeatedEdgeVerifier 0 2 (fun _ => ()) (fun c (_ _ : Unit) => c)).accepts
    (loop false) [] [] = false := by decide

example : (Graph.repeatedEdgeVerifier 1 0 decode eval).accepts (loop false) [] [] = true := by
  decide

-- Packed labels recover all declared vertices and keep the order of distinct endpoint blocks.
example : Graph.proofOfLabels 1 3 encode (fun n => n == 1) = [false, true, false] := by decide

example : (Graph.edgeVerifier 1 decode (fun (_ : Unit) a b => a == b)).queries
    (⟨2, [⟨0, 1, ()⟩]⟩, []) = [0, 1] := by decide

example : (Graph.edgeVerifier 1 decode (fun (_ : Unit) a b => a == b)).accepts
    ⟨2, [⟨0, 1, ()⟩]⟩ [false, true] [] = false := by decide

example : (Graph.edgeVerifier 1 decode (fun (_ : Unit) a b => a == b)).accepts
    ⟨2, [⟨0, 1, ()⟩]⟩ [] [] = true := by decide

example (proof : List Bool) :
    ((loop false).toGraph eval).unsatVal / 2 ≤
      (((BitString.uniformList 0).map (fun random => check.accepts
        (loop false) proof random)) false).toReal :=
  Graph.unsatVal_div_two_le_rejectProb 1 decode eval (loop false) proof

-- Ordinary expressions preserve the raw and framed random-word encodings.
attribute [local fun_prop] ComputableInPolyTime.tidy in
example : ComputableTidilyInPolyTime
    (fun p : Graph Bool × List Bool => p.1.sampleEdge p.2)
    (encPair (Graph.encoding encBool) encBits) (encOption (Edge.encoding encBool)) := by
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
example : ComputableTidilyInPolyTime
    (fun p : Graph Bool × List Bool => let graph := p.1; graph.sampleEdge p.2)
    (encPair (Graph.encoding encBool) encBits) (encOption (Edge.encoding encBool)) := by
  polytime

attribute [local fun_prop] ComputableInPolyTime.tidy in
example : ComputableTidilyInPolyTime
    (fun p : Graph Bool × List Bool => p.1.sampleEdge p.2)
    (encPair (Graph.encoding encBool) encBits) (encOption (Edge.encoding encBool)) := by
  polytime

attribute [local fun_prop] ComputableInPolyTime.tidy in
example : ComputableTidilyInPolyTime
    (fun p : Graph Bool × List Bool => let graph := p.1; graph.sampleEdge p.2)
    (encPair (Graph.encoding encBool) encBits) (encOption (Edge.encoding encBool)) := by
  fun_prop

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
example : ComputableTidilyInPolyTime
    (fun p : Graph Bool × List Bool => p.1.sampleEdge p.2)
    (encPair (Graph.encoding encBool) (encList encBool))
      (encOption (Edge.encoding encBool)) := by
  refine ComputableInPolyTime.tidy (Graph.isPolyTime_sampleEdge (.of_tidy (by fun_prop))
    (.of_tidy ?_))
  exact ComputableTidilyInPolyTime.listToBits.comp (by fun_prop)

attribute [local fun_prop] ComputableInPolyTime.tidy in
example {C α : Type} (enc : C ↪ List Bool) (alphabet : α ↪ List Bool)
    (decoder : (Fin 2 → Bool) → α) (evaluator : C → α → α → Bool)
    (heval : ComputableInPolyTime (fun p : C × α × α => evaluator p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    ComputableInPolyTime
      (fun p : Edge C × List Bool => p.1.proofVerdict 2 decoder evaluator p.2)
      (encPair (Edge.encoding enc) encBits) encBool := by
  fail_if_success solve | clear heval; fun_prop
  fun_prop

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
example {C : Type} (enc : C ↪ List Bool) (graph : ℕ → Graph C)
    (hgraph : ComputableTidilyInPolyTime graph encUnary (Graph.encoding enc)) :
    ComputableTidilyInPolyTime
      (fun n => (graph (n + 1)).sampleEdge (List.replicate n true))
      encUnary (encOption (Edge.encoding enc)) := by
  fail_if_success solve | clear hgraph; fun_prop
  polytime

example {C α : Type} (enc : C ↪ List Bool) (alphabet : α ↪ List Bool)
    (decoder : (Fin 2 → Bool) → α) (evaluator : C → α → α → Bool)
    (heval : ComputableTidilyInPolyTime (fun p : C × α × α => evaluator p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool) :
    (Graph.repeatedEdgeVerifier 2 3 decoder evaluator).PolyTime (Graph.encoding enc) :=
  Graph.polyTime_repeatedEdgeVerifier 2 3 decoder (.of_tidy heval)

-- Both members and nonmembers occur, and the nonmember graph has positive gap exactly one.
example : ({true} : Set Bool) ∈ PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) encBool := by
  apply Graph.mem_PCP_of_gapReduction (graph := loop) 1 encode decode (by intro x; rfl)
    (alphabet := encBool) (enc := encBool) (eval := eval)
    (.of_tidy (.of_finite _)) (.of_tidy (.of_finite _)) loop_wellFormed
    (gap := 1) ?_ (by norm_num) ?_
  · intro bit hbit
    have hbit : bit = true := hbit
    subst bit
    exact ⟨fun _ => false, fun i => by simp [loop, Graph.toGraph, ConstraintGraph.Satisfies, eval]⟩
  · intro bit hbit
    cases bit
    · exact loop_false_value.ge
    · exact (hbit (by simp)).elim

/-- info: 27 -/
#guard_msgs in
#eval acceptCount (fun p => repeatCheck.accepts p.1 [] p.2) mixed (repeatCheck.coins mixed)

end ComplexityTests.PCPEncodedVerifier
