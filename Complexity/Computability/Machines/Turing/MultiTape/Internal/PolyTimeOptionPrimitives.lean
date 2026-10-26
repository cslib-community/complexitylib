/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# Direct plain polynomial-time option operations

The option encoding machines supply construction and fixed-default elimination. Composition
retains every encoded input, including captured arguments and a runtime fallback. Empty value
types need no inhabitant assumption.

## Main results

* `ComputableInPolyTime.optionSome`: construct an optional value.
* `ComputableInPolyTime.optionIsSome`: test a computed optional value.
* `ComputableInPolyTime.optionGetD`: read an option with a runtime fallback.
* `ComputableInPolyTime.optionGetDWithInput`, `.optionElimWithInput`: retain captured inputs.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Construct an optional value with the standard option encoding. -/
@[fun_prop]
theorem optionSome (enc : α ↪ List Bool) :
    ComputableInPolyTime (some (α := α)) enc (encOption enc) :=
  ComputableInDegree.optionSome.computableInPolyTime

/-- Test whether a computed option contains a value, without requiring a default value. -/
@[fun_prop]
theorem optionIsSome {value : α → Option β}
    (hvalue : ComputableInPolyTime value encA (encOption encB)) :
    ComputableInPolyTime (fun a => (value a).isSome) encA encBool :=
  (ComputableInDegree.isSome encB).computableInPolyTime.comp hvalue

/-- Read an option with a fallback supplied as part of the input. -/
@[fun_prop]
theorem optionGetD (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : Option α × α => p.1.getD p.2)
      (encPair (encOption enc) enc) enc := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    have hread := ComputableInPolyTime.ite (encC := encBool)
      ((ComputableInDegree.isSome enc).computableInPolyTime.comp (fst (encOption enc) enc))
      ((ComputableInDegree.getD fallback).computableInPolyTime.comp (fst (encOption enc) enc))
      (snd (encOption enc) enc)
    convert hread using 1
    funext ⟨value, d⟩
    cases value <;> rfl

/-- Read a computed option with a computed fallback, using their shared value encoding. -/
@[fun_prop]
theorem optionGetDWithInput {value : α → Option β} {fallback : α → β}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hfallback : ComputableInPolyTime fallback encA encB) :
    ComputableInPolyTime (fun a => (value a).getD (fallback a)) encA encB :=
  (optionGetD encB).comp (hvalue.prod hfallback)

/-- Branch on a computed option, charging its full value and any captured original input. -/
@[fun_prop]
theorem optionElimWithInput {γ : Type} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hvalue : ComputableInPolyTime value encA (encOption encB))
    (hfallback : ComputableInPolyTime fallback encA encC)
    (hbody : ComputableInPolyTime (fun p : α × β => body p.1 p.2)
      (encPair encA encB) encC) :
    ComputableInPolyTime
      (fun a => (value a).elim (fallback a) (body a)) encA encC := by
  rcases isEmpty_or_nonempty β with h | h
  · convert hfallback using 1
    funext a
    cases value a with
    | none => rfl
    | some b => exact isEmptyElim b
  · obtain ⟨b⟩ := h
    have hget : ComputableInPolyTime (fun a => (value a).getD b) encA encB :=
      (ComputableInDegree.getD b).computableInPolyTime.comp hvalue
    have hbranch := ComputableInPolyTime.ite (encC := encBool) hvalue.optionIsSome
      (hbody.comp (id'.prod hget)) hfallback
    convert hbranch using 1
    funext a
    dsimp only [Function.comp_def]
    cases value a <;> rfl

end Turing.MultiTapeTM.ComputableInPolyTime
