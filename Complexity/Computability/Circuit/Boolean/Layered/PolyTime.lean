/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time operations on layered Boolean circuits

Node tags and binary wire indices are read from their actual encoding. Lookups use the binary
index calculus, which bounds an index before converting it to unary. Invalid references retain
the specified fallback without running for time proportional to the numerical index.

## Main results

* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_nodeCode`: read a node's code.
* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_nodeConst`,
  `computableInPolyTime_nodeCopy`, `computableInPolyTime_nodeNand`: construct nodes.
* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_nodeEval`: evaluate one node.
* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_evalLayer`: evaluate one layer.
* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_select`: select ordered outputs.
* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_outputWidth`: compute the final
  row width in unary, retaining the input width for an empty schedule.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

open Turing.MultiTapeTM

/-- Read the two tag bits and two binary wire indices without changing the encoding. -/
@[fun_prop]
theorem computableInPolyTime_nodeCode :
    ComputableInPolyTime Node.code encNode
      (encPair (encPair encBool encBool) (encPair encNat encNat)) :=
  .of_eq fun _ => rfl

/-- Construct a constant node. -/
@[fun_prop]
theorem computableInPolyTime_nodeConst :
    ComputableInPolyTime Node.const encBool encNode :=
  .of_finite _

/-- Construct a copy node, preserving the binary wire index. -/
@[fun_prop]
theorem computableInPolyTime_nodeCopy :
    ComputableInPolyTime Node.copy encNat encNode := by
  have h : ComputableInPolyTime (fun i : ℕ => ((true, false), i, 0)) encNat
      (encPair (encPair encBool encBool) (encPair encNat encNat)) := by fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Construct a NAND node, preserving both binary wire indices. -/
@[fun_prop]
theorem computableInPolyTime_nodeNand :
    ComputableInPolyTime (fun p : ℕ × ℕ => Node.nand p.1 p.2)
      (encPair encNat encNat) encNode := by
  have h : ComputableInPolyTime (fun p : ℕ × ℕ => ((true, true), p))
      (encPair encNat encNat) (encPair (encPair encBool encBool) (encPair encNat encNat)) := by
    fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Node evaluation is polynomial in the encoded input, including invalid binary wire indices. -/
@[fun_prop]
theorem computableInPolyTime_nodeEval {α : Type} {input : α ↪ List Bool}
    {node : α → Node} {inputs : α → List Bool}
    (hnode : ComputableInPolyTime node input encNode)
    (hinputs : ComputableInPolyTime inputs input encBits) :
    ComputableInPolyTime (fun a => (node a).eval (inputs a)) input encBool := by
  have hcode := computableInPolyTime_nodeCode.comp hnode
  have hfirst : ComputableInPolyTime
      (fun a => (inputs a).getD (node a).code.2.1 false) input encBool :=
    ComputableInPolyTime.listGetD_binary (encA := encBool) false hinputs (by fun_prop)
  have hsecond : ComputableInPolyTime
      (fun a => (inputs a).getD (node a).code.2.2 false) input encBool :=
    ComputableInPolyTime.listGetD_binary (encA := encBool) false hinputs (by fun_prop)
  have h : ComputableInPolyTime (fun a =>
      if (node a).code.1.1 then
        if (node a).code.1.2 then
          !((inputs a).getD (node a).code.2.1 false &&
            (inputs a).getD (node a).code.2.2 false)
        else (inputs a).getD (node a).code.2.1 false
      else (node a).code.1.2) input encBool :=
    hcode.fst'.fst'.ite
      (hcode.fst'.snd'.ite
        (ComputableInPolyTime.bool_not.comp
          (ComputableInPolyTime.bool_and.comp (hfirst.prod hsecond))) hfirst)
      hcode.fst'.snd'
  convert h using 1
  funext a
  cases node a <;> rfl

/-- Evaluate a computed layer, preserving the raw bit-string output encoding. -/
@[fun_prop]
theorem computableInPolyTime_evalLayer {α : Type} {input : α ↪ List Bool}
    {layer : α → List Node} {inputs : α → List Bool}
    (hlayer : ComputableInPolyTime layer input (encList encNode))
    (hinputs : ComputableInPolyTime inputs input encBits) :
    ComputableInPolyTime (fun a => evalLayer (inputs a) (layer a)) input encBits := by
  apply ComputableInPolyTime.listToBits.comp
  apply ComputableInPolyTime.mapWithInput hlayer
  apply computableInPolyTime_nodeEval <;> fun_prop

/-- Free output selection is polynomial even for malformed binary indices. -/
@[fun_prop]
theorem computableInPolyTime_select {α : Type} {input : α ↪ List Bool}
    {inputs : α → List Bool} {outputs : α → List ℕ}
    (hinputs : ComputableInPolyTime inputs input encBits)
    (houtputs : ComputableInPolyTime outputs input (encList encNat)) :
    ComputableInPolyTime (fun a => select (inputs a) (outputs a)) input encBits := by
  apply ComputableInPolyTime.listToBits.comp
  apply ComputableInPolyTime.mapWithInput houtputs
  exact ComputableInPolyTime.listGetD_binary false (by fun_prop) (by fun_prop)

/-- Read the last layer's length, or retain the computed input width for an empty schedule. -/
@[fun_prop]
theorem computableInPolyTime_outputWidth {α : Type} {input : α ↪ List Bool}
    {inputCount : α → ℕ} {layers : α → List (List Node)}
    (hn : ComputableInPolyTime inputCount input encUnary)
    (hlayers : ComputableInPolyTime layers input (encList (encList encNode))) :
    ComputableInPolyTime (fun a => outputWidth (inputCount a) (layers a)) input encUnary := by
  have heq (n : ℕ) (ls : List (List Node)) :
      outputWidth n ls = ((n :: ls.map List.length).reverse).headD 0 := by
    induction ls using List.reverseRecOn with
    | nil => simp
    | append_singleton ls layer _ => simp [outputWidth_append]
  have hlengths := (ComputableInPolyTime.length_list encNode).map.comp hlayers
  have h := (ComputableInPolyTime.headD (encA := encUnary) 0).comp
    ((hn.cons' hlengths).listReverseWithInput)
  simpa only [heq, Function.comp_def] using h

end Cslib.Circuits.Boolean.Layered
