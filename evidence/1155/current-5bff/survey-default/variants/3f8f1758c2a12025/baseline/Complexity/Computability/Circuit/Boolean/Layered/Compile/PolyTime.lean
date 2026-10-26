/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered.Compile
public import Complexity.Computability.Circuit.Boolean.Layered.PolyTime
public import Complexity.Computability.Circuit.Boolean.DepthTime.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time compilation into consecutive layers

The certificates follow the actual raw compiler: compute the depth table and selected-output
maximum, then generate both microlevels at each depth. The input count and internal enumeration
counters are unary; source wire references and emitted node references are binary. Every layer,
node, delimiter and output selector is included in the output encoding.

The construction is uniform in the input count, gate count and number of designated outputs.
It is polynomial-time on all raw code, without a well-formedness or promised-depth hypothesis.

## Main results

* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_prepareLayer`,
  `computableInPolyTime_finishLayer`: generate the two microlevels of a depth.
* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_schedule`: generate all levels.
* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_compile`: compute depths and emit
  the complete schedule and output selectors.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Decide whether a unary-numbered wire is already available, then emit its binary copy index. -/
@[fun_prop]
theorem computableInPolyTime_carry {depths : α → List ℕ} {level wire : α → ℕ}
    (hdepths : ComputableInPolyTime depths input (encList encUnary))
    (hlevel : ComputableInPolyTime level input encUnary)
    (hwire : ComputableInPolyTime wire input encUnary) :
    ComputableInPolyTime (fun a => carry (depths a) (level a) (wire a)) input encNode := by
  refine .of_tidy ?_
  have hdepths := hdepths.tidy
  have hlevel := hlevel.tidy
  have hwire := hwire.tidy
  exact (unary_lt' ((listGetD 0).comp (hdepths.prod hwire)) hlevel).ite_decide
    (computableInPolyTime_nodeCopy.tidy.comp (unary_to_binary.comp hwire))
    (const (Node.const false))

/-- Prepare the first intermediate, retaining binary source references. -/
@[fun_prop]
theorem computableInPolyTime_prepareFirst {gate : α → Op × List ℕ}
    (hgate : ComputableInPolyTime gate input encGate) :
    ComputableInPolyTime (fun a => prepareFirst (gate a)) input encNode := by
  have hgate := hgate.tidy
  refine .of_tidy ?_
  have harg (i : ℕ) : ComputableTidilyInPolyTime (fun a => (gate a).2.getD i 0)
      input encNat := (listGetD 0).comp (hgate.snd'.prod (const i))
  apply finite_cases (branch := fun op a => prepareFirst (op, (gate a).2)) hgate.fst'
  intro op
  cases op with
  | const b => exact const (Node.const b)
  | not | or =>
    simpa only [prepareFirst, Function.comp_def] using
      computableInPolyTime_nodeNand.tidy.comp ((harg 0).prod (harg 0))
  | and =>
    simpa only [prepareFirst, Function.comp_def] using
      computableInPolyTime_nodeNand.tidy.comp ((harg 0).prod (harg 1))

/-- Prepare the second intermediate, retaining the binary source reference. -/
@[fun_prop]
theorem computableInPolyTime_prepareSecond {gate : α → Op × List ℕ}
    (hgate : ComputableInPolyTime gate input encGate) :
    ComputableInPolyTime (fun a => prepareSecond (gate a)) input encNode := by
  have hgate := hgate.tidy
  refine .of_tidy ?_
  have harg : ComputableTidilyInPolyTime (fun a => (gate a).2.getD 1 0) input encNat :=
    (listGetD 0).comp (hgate.snd'.prod (const 1))
  apply finite_cases (branch := fun op a => prepareSecond (op, (gate a).2)) hgate.fst'
  intro op
  cases op with
  | const _ | not | and => exact const (Node.const false)
  | or =>
    simpa only [prepareSecond, Function.comp_def] using
      computableInPolyTime_nodeNand.tidy.comp (harg.prod harg)

/-- Finish a gate, computing scratch positions in unary before emitting binary indices. -/
@[fun_prop]
theorem computableInPolyTime_finish {inputCount gateCount gateIndex : α → ℕ}
    {op : α → Op} (hn : ComputableInPolyTime inputCount input encUnary)
    (hg : ComputableInPolyTime gateCount input encUnary)
    (hj : ComputableInPolyTime gateIndex input encUnary)
    (hop : ComputableInPolyTime op input encOp) :
    ComputableInPolyTime
      (fun a => finish (inputCount a) (gateCount a) (gateIndex a) (op a)) input encNode := by
  have hn := hn.tidy
  have hg := hg.tidy
  have hj := hj.tidy
  have hop := hop.tidy
  refine .of_tidy ?_
  have hfirst : ComputableTidilyInPolyTime
      (fun a => inputCount a + gateCount a + gateIndex a) input encNat :=
    unary_to_binary.comp (by fun_prop)
  have hsecond : ComputableTidilyInPolyTime
      (fun a => inputCount a + 2 * gateCount a + gateIndex a) input encNat :=
    unary_to_binary.comp (by fun_prop)
  apply finite_cases
    (branch := fun op a => finish (inputCount a) (gateCount a) (gateIndex a) op) hop
  intro op
  cases op with
  | const _ | not =>
    simpa only [finish, Function.comp_def] using computableInPolyTime_nodeCopy.tidy.comp hfirst
  | and =>
    simpa only [finish, Function.comp_def] using
      computableInPolyTime_nodeNand.tidy.comp (hfirst.prod hfirst)
  | or =>
    simpa only [finish, Function.comp_def] using
      computableInPolyTime_nodeNand.tidy.comp (hfirst.prod hsecond)

/-- Generate a preparation layer, charging the complete framed node list. -/
@[fun_prop]
theorem computableInPolyTime_prepareLayer {inputCount level : α → ℕ}
    {gates : α → List (Op × List ℕ)} {depths : α → List ℕ}
    (hn : ComputableInPolyTime inputCount input encUnary)
    (hgates : ComputableInPolyTime gates input (encList encGate))
    (hdepths : ComputableInPolyTime depths input (encList encUnary))
    (hlevel : ComputableInPolyTime level input encUnary) :
    ComputableInPolyTime
      (fun a => prepareLayer (inputCount a) (gates a) (depths a) (level a))
      input (encList encNode) := by
  refine .of_tidy ?_
  have hn := hn.tidy
  have hgates := hgates.tidy
  have hdepths := hdepths.tidy
  have hlevel := hlevel.tidy
  have hcount := (length_list encGate).comp hgates
  have hread : ComputableTidilyInPolyTime
      (fun p : α × ℕ => (gates p.1).getD p.2 (.const false, []))
      (encPair input encUnary) encGate := by fun_prop
  have hactive : ComputableTidilyInPolyTime
      (fun p : α × ℕ => decide ((depths p.1).getD (inputCount p.1 + p.2) 0 = level p.1))
      (encPair input encUnary) encBool := by
    apply decide_eq' (encB := encUnary) <;> fun_prop
  have hmain : ComputableTidilyInPolyTime (fun a =>
      (List.range (inputCount a + (gates a).length)).map (carry (depths a) (level a)))
      input (encList encNode) := by
    apply mapWithInput (range.comp (by fun_prop))
    apply ComputableInPolyTime.tidy
    apply computableInPolyTime_carry <;> exact .of_tidy (by fun_prop)
  have hfirst : ComputableTidilyInPolyTime (fun a => (List.range (gates a).length).map fun j =>
      if (depths a).getD (inputCount a + j) 0 = level a then
        prepareFirst ((gates a).getD j (.const false, [])) else Node.const false)
      input (encList encNode) := by
    apply mapWithInput (range.comp hcount)
    exact hactive.ite_decide (computableInPolyTime_prepareFirst (.of_tidy hread)).tidy
      (const (Node.const false))
  have hsecond : ComputableTidilyInPolyTime (fun a => (List.range (gates a).length).map fun j =>
      if (depths a).getD (inputCount a + j) 0 = level a then
        prepareSecond ((gates a).getD j (.const false, [])) else Node.const false)
      input (encList encNode) := by
    apply mapWithInput (range.comp hcount)
    exact hactive.ite_decide (computableInPolyTime_prepareSecond (.of_tidy hread)).tidy
      (const (Node.const false))
  exact listAppend' (listAppend' hmain hfirst) hsecond

/-- Generate a finishing layer, including copies and all cleared scratch slots. -/
@[fun_prop]
theorem computableInPolyTime_finishLayer {inputCount level : α → ℕ}
    {gates : α → List (Op × List ℕ)} {depths : α → List ℕ}
    (hn : ComputableInPolyTime inputCount input encUnary)
    (hgates : ComputableInPolyTime gates input (encList encGate))
    (hdepths : ComputableInPolyTime depths input (encList encUnary))
    (hlevel : ComputableInPolyTime level input encUnary) :
    ComputableInPolyTime
      (fun a => finishLayer (inputCount a) (gates a) (depths a) (level a))
      input (encList encNode) := by
  refine .of_tidy ?_
  have hn := hn.tidy
  have hgates := hgates.tidy
  have hdepths := hdepths.tidy
  have hlevel := hlevel.tidy
  have hcount := (length_list encGate).comp hgates
  have hread : ComputableTidilyInPolyTime
      (fun p : α × ℕ => (gates p.1).getD p.2 (.const false, []))
      (encPair input encUnary) encGate := by fun_prop
  have hactive : ComputableTidilyInPolyTime
      (fun p : α × ℕ => decide ((depths p.1).getD (inputCount p.1 + p.2) 0 = level p.1))
      (encPair input encUnary) encBool := by
    apply decide_eq' (encB := encUnary) <;> fun_prop
  have hinputs : ComputableTidilyInPolyTime
      (fun a => (List.range (inputCount a)).map Node.copy) input (encList encNode) := by
    apply mapWithInput (range.comp hn)
    exact computableInPolyTime_nodeCopy.tidy.comp (unary_to_binary.comp (snd input encUnary))
  have hfinish : ComputableTidilyInPolyTime
      (fun p : α × ℕ => finish (inputCount p.1) (gates p.1).length p.2
        ((gates p.1).getD p.2 (.const false, [])).1) (encPair input encUnary) encNode :=
    (computableInPolyTime_finish (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by
      fun_prop)) (.of_tidy hread.fst')).tidy
  have hcarry : ComputableTidilyInPolyTime
      (fun p : α × ℕ => carry (depths p.1) (level p.1) (inputCount p.1 + p.2))
      (encPair input encUnary) encNode :=
    (computableInPolyTime_carry (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))
      (.of_tidy (by fun_prop))).tidy
  have hg : ComputableTidilyInPolyTime (fun a => (List.range (gates a).length).map fun j =>
      if (depths a).getD (inputCount a + j) 0 = level a then
        finish (inputCount a) (gates a).length j ((gates a).getD j (.const false, [])).1
      else carry (depths a) (level a) (inputCount a + j)) input (encList encNode) := by
    apply mapWithInput (range.comp hcount)
    exact hactive.ite_decide hfinish hcarry
  have hscratch : ComputableTidilyInPolyTime
      (fun a => List.replicate (2 * (gates a).length) (Node.const false))
      input (encList encNode) := replicate (by fun_prop) (const (Node.const false))
  exact listAppend' (listAppend' hinputs hg) hscratch

/-- Generate both microlevels at every computed unary depth, charging their full encoding. -/
@[fun_prop]
theorem computableInPolyTime_schedule {inputCount depth : α → ℕ}
    {gates : α → List (Op × List ℕ)} {depths : α → List ℕ}
    (hn : ComputableInPolyTime inputCount input encUnary)
    (hgates : ComputableInPolyTime gates input (encList encGate))
    (hdepths : ComputableInPolyTime depths input (encList encUnary))
    (hdepth : ComputableInPolyTime depth input encUnary) :
    ComputableInPolyTime
      (fun a => schedule (inputCount a) (gates a) (depths a) (depth a))
      input (encList (encList encNode)) := by
  have hn := hn.tidy
  have hgates := hgates.tidy
  have hdepths := hdepths.tidy
  have hdepth := hdepth.tidy
  refine .of_tidy ?_
  apply flatMapWithInput (range.comp hdepth)
  apply cons'
  · apply ComputableInPolyTime.tidy
    apply computableInPolyTime_prepareLayer <;> exact .of_tidy (by fun_prop)
  · apply cons'
    · apply ComputableInPolyTime.tidy
      apply computableInPolyTime_finishLayer <;> exact .of_tidy (by fun_prop)
    · exact const []

/-- Compile arbitrary raw code in native polynomial time. The input count is unary; all source
references and output selectors are binary. Depth computation and the entire emitted schedule
are included, with no validity premise or fixed input/output arity. -/
@[fun_prop]
theorem computableInPolyTime_compile {inputCount : α → ℕ}
    {code : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime inputCount input encUnary)
    (hcode : ComputableInPolyTime code input encCode) :
    ComputableInPolyTime (fun a => compile (inputCount a) (code a)) input encCompiled :=
  (computableInPolyTime_schedule hn hcode.fst'
    (computableInPolyTime_wireDepthsCode hn hcode.fst')
    (computableInPolyTime_depthCode hn hcode)).prod hcode.snd'

end Cslib.Circuits.Boolean.Layered
