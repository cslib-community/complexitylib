/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Lean.Elab.Command


import Diag1155.Measure
/-! Shared Option automation, including empty value types and encoded runtime defaults. -/

diag1155_install
open Turing.MultiTapeTM

example {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (some (α := α)) enc (encOption enc) := by fun_prop

example {α β : Type} {a : α ↪ List Bool} {b : β ↪ List Bool} {value : α → Option β}
    (hvalue : ComputableInPolyTime value a (encOption b)) :
    ComputableInPolyTime (fun x => (value x).isSome) a encBool := by fun_prop

example {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : Option α × α => p.1.getD p.2)
      (encPair (encOption enc) enc) enc := by fun_prop

example (enc : Empty ↪ List Bool) :
    ComputableInPolyTime (fun p : Option Empty × Empty => p.1.getD p.2)
      (encPair (encOption enc) enc) enc := by fun_prop

example : (none : Option Bool).getD false = false := rfl
example : (some true : Option Bool).getD false = true := rfl
example : (some false : Option Bool).getD true = false := rfl

example {α : Type} (a : α ↪ List Bool) (e : Empty ↪ List Bool)
    {value : α → Option Empty} (hvalue : ComputableInPolyTime value a (encOption e)) :
    ComputableInPolyTime (fun x => (value x).isSome) a encBool := by fun_prop

example {α β : Type} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {value : α → Option β} {fallback : α → β}
    (hvalue : ComputableInPolyTime value a (encOption b))
    (hfallback : ComputableInPolyTime fallback a b) :
    ComputableInPolyTime (fun x => (value x).getD (fallback x)) a b := by fun_prop

example {α β γ : Type} {a : α ↪ List Bool} {b : β ↪ List Bool} {c : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hvalue : ComputableInPolyTime value a (encOption b))
    (hfallback : ComputableInPolyTime fallback a c)
    (hbody : ComputableInPolyTime (fun p : α × β => body p.1 p.2) (encPair a b) c) :
    ComputableInPolyTime (fun x => (value x).elim (fallback x) (body x)) a c := by fun_prop

-- The body uses both its captured original input and the fetched optional value.
example {α β : Type} {a : α ↪ List Bool} {b : β ↪ List Bool} {value : α → Option β}
    {fallback : α → α × β} (hvalue : ComputableInPolyTime value a (encOption b))
    (hfallback : ComputableInPolyTime fallback a (encPair a b)) :
    ComputableInPolyTime (fun x => (value x).elim (fallback x) (fun y => (x, y)))
      a (encPair a b) := by fun_prop

example {α γ : Type} {a : α ↪ List Bool} {e : Empty ↪ List Bool} {c : γ ↪ List Bool}
    {value : α → Option Empty} {fallback : α → γ} {body : α → Empty → γ}
    (hvalue : ComputableInPolyTime value a (encOption e))
    (hfallback : ComputableInPolyTime fallback a c)
    (hbody : ComputableInPolyTime (fun p : α × Empty => body p.1 p.2) (encPair a e) c) :
    ComputableInPolyTime (fun x => (value x).elim (fallback x) (body x)) a c := by fun_prop

example {α β : Type} {_a : α ↪ List Bool} {_b : β ↪ List Bool}
    {_value : α → Option β} {_fallback : α → β}
    (_hvalue : ComputableInPolyTime _value _a (encOption _b)) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun x => (_value x).getD (_fallback x)) _a _b := by fun_prop
  trivial

example {α β γ : Type} {_a : α ↪ List Bool} {_b : β ↪ List Bool} {_c : γ ↪ List Bool}
    {_value : α → Option β} {_fallback : α → γ} {_body : α → β → γ}
    (_hvalue : ComputableInPolyTime _value _a (encOption _b))
    (_hfallback : ComputableInPolyTime _fallback _a _c) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun x => (_value x).elim (_fallback x) (_body x)) _a _c := by
      fun_prop
  trivial

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
