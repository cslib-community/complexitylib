/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Lean.Elab.Command

/-! Shared Option automation, including empty value types and encoded runtime defaults. -/
open Turing.MultiTapeTM

example {α β γ : Type} (enc : α ↪ List Bool) {a : α ↪ List Bool} {b : β ↪ List Bool}
    {c : γ ↪ List Bool} (e : Empty ↪ List Bool)
    {value : α → Option β} (hvalue : ComputableInPolyTime value a (encOption b))
    {valueE : α → Option Empty} (hvalueE : ComputableInPolyTime valueE a (encOption e))
    {fallbackB _ufallbackB : α → β} (hfallbackB : ComputableInPolyTime fallbackB a b)
    {fallbackC : α → γ} (hfallbackC : ComputableInPolyTime fallbackC a c)
    {fallbackP : α → α × β} (hfallbackP : ComputableInPolyTime fallbackP a (encPair a b))
    {body _ubody : α → β → γ}
    (hbody : ComputableInPolyTime (fun p : α × β => body p.1 p.2) (encPair a b) c)
    {bodyE : α → Empty → γ}
    (hbodyE : ComputableInPolyTime (fun p : α × Empty => bodyE p.1 p.2) (encPair a e) c) :
    ComputableInPolyTime (some (α := α)) enc (encOption enc) ∧
    ComputableInPolyTime (fun x => (value x).isSome) a encBool ∧
    ComputableInPolyTime (fun p : Option α × α => p.1.getD p.2)
      (encPair (encOption enc) enc) enc ∧
    ComputableInPolyTime (fun p : Option Empty × Empty => p.1.getD p.2)
      (encPair (encOption e) e) e ∧
    (none : Option Bool).getD false = false ∧
    (some true : Option Bool).getD false = true ∧
    (some false : Option Bool).getD true = false ∧
    ComputableInPolyTime (fun x => (valueE x).isSome) a encBool ∧
    ComputableInPolyTime (fun x => (value x).getD (fallbackB x)) a b ∧
    ComputableInPolyTime (fun x => (value x).elim (fallbackC x) (body x)) a c ∧
    ComputableInPolyTime (fun x => (value x).elim (fallbackP x) (fun y => (x, y)))
      a (encPair a b) ∧
    ComputableInPolyTime (fun x => (valueE x).elim (fallbackC x) (bodyE x)) a c := by
  fail_if_success
    have : ComputableInPolyTime (fun x => (value x).getD (_ufallbackB x)) a b := by fun_prop
  fail_if_success
    have : ComputableInPolyTime (fun x => (value x).elim (fallbackC x) (_ubody x)) a c := by
      fun_prop
  exact ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop, rfl, rfl, rfl,
    by fun_prop, by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
