/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Polynomial-time option operations

Option elimination reuses the degree-bounded encoding operations. Both the optional value and
its fallback may be computed from the input; no inhabitant of the value type is required.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionSome`: construct an optional value.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionGetD`: read an option with a fallback
  supplied as part of the input.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionGetDWithInput`: the composition rule.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionIsSome`: test a computed optional value.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionElimWithInput`: branch on an optional
  value while retaining the original input, including empty value types.

The plain forms `Turing.MultiTapeTM.ComputableInPolyTime.optionSome`, `.optionGetD`,
`.optionGetDWithInput`, `.optionIsSome` and `.optionElimWithInput` are in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives`, which
this file publicly imports. So is `Turing.MultiTapeTM.ComputableInPolyTime.optionMapWithInput`,
which maps an optional value with a callback certified jointly with its captured original input;
it has no tidy form here.

## References

Uses Christian Reitwiessner's option encoding and degree-bounded machine calculus.
-/

public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Construct an optional value with the standard option encoding. -/
@[fun_prop]
theorem optionSome (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (some (α := α)) enc (encOption enc) :=
  of_linear (Internal.NormalForm.linear OptionEncoding.some)

/-- Test whether a computed option contains a value, without requiring a default value. -/
@[fun_prop]
theorem optionIsSome {value : α → Option β}
    (hvalue : ComputableTidilyInPolyTime value encA (encOption encB)) :
    ComputableTidilyInPolyTime (fun a => (value a).isSome) encA encBool :=
  (ComputableTidilyInDegree.isSome encB).computableTidilyInPolyTime.comp hvalue

/-- Read an option with a fallback supplied as part of the input. -/
@[fun_prop]
theorem optionGetD (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : Option α × α => p.1.getD p.2)
      (encPair (encOption enc) enc) enc :=
  (ComputableInPolyTime.optionGetD enc).tidy

/-- Read a computed option with a computed fallback, using their shared value encoding. -/
@[fun_prop]
theorem optionGetDWithInput {value : α → Option β} {fallback : α → β}
    (hvalue : ComputableTidilyInPolyTime value encA (encOption encB))
    (hfallback : ComputableTidilyInPolyTime fallback encA encB) :
    ComputableTidilyInPolyTime (fun a => (value a).getD (fallback a)) encA encB :=
  (optionGetD encB).comp (hvalue.prod hfallback)

/-- Branch on a computed option, charging its full value and any captured original input. -/
@[fun_prop]
theorem optionElimWithInput {γ : Type} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hvalue : ComputableTidilyInPolyTime value encA (encOption encB))
    (hfallback : ComputableTidilyInPolyTime fallback encA encC)
    (hbody : ComputableTidilyInPolyTime (fun p : α × β => body p.1 p.2)
      (encPair encA encB) encC) :
    ComputableTidilyInPolyTime
      (fun a => (value a).elim (fallback a) (body a)) encA encC :=
  (ComputableInPolyTime.optionElimWithInput hvalue.computableInPolyTime
    hfallback.computableInPolyTime hbody.computableInPolyTime).tidy

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
