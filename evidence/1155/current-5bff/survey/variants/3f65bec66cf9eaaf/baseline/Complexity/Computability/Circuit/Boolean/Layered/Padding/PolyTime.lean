/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered.Padding
public import Complexity.Computability.Circuit.Boolean.Layered.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time padding of layered Boolean circuits

The input width and target layer count use unary encodings. Existing and generated node
references use binary encodings, and the full nested list encoding charges every copied node
and layer delimiter. The certificates apply to all schedules, including invalid references and
schedules longer than the target.

## Main results

* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_identityLayer`: generate a row
  of binary-indexed copies from a unary width.
* `Cslib.Circuits.Boolean.Layered.computableInPolyTime_padTo`: compute the final width
  and append the actual copy layers in uniform polynomial time.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Enumerate the row in unary and encode each copy node's wire index in binary. -/
@[fun_prop]
theorem computableInPolyTime_identityLayer {width : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary) :
    ComputableInPolyTime (fun a => identityLayer (width a)) input (encList encNode) := by
  have hwidth := hwidth.tidy
  refine .of_tidy ?_
  simpa only [identityLayer, Function.comp_def] using
    (computableInPolyTime_nodeCopy.tidy.comp unary_to_binary).map.comp (range.comp hwidth)

/-- Padding is polynomial in the complete encoded input, including its unary target. -/
@[fun_prop]
theorem computableInPolyTime_padTo {inputCount target : α → ℕ}
    {layers : α → List (List Node)}
    (hn : ComputableInPolyTime inputCount input encUnary)
    (htarget : ComputableInPolyTime target input encUnary)
    (hlayers : ComputableInPolyTime layers input (encList (encList encNode))) :
    ComputableInPolyTime (fun a => padTo (inputCount a) (target a) (layers a))
      input (encList (encList encNode)) := by
  have hn := hn.tidy
  have htarget := htarget.tidy
  have hlayers := hlayers.tidy
  refine .of_tidy ?_
  have hlength := (length_list (encList encNode)).comp hlayers
  have hcopies := (computableInPolyTime_identityLayer
    (computableInPolyTime_outputWidth (.of_tidy hn) (.of_tidy hlayers))).tidy
  exact hlayers.listAppend' (replicate (by fun_prop) hcopies)

end Cslib.Circuits.Boolean.Layered
