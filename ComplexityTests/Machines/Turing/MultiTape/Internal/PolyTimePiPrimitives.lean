/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives

/-! # Direct finite tables with captured inputs and empty types -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

example {α Index Value : Type} [Fintype Index] [DecidableEq Index]
    {input : α ↪ List Bool} {enc : Value ↪ List Bool} {indexEncoding : Index ↪ List Bool}
    (emptyEnc : Empty ↪ List Bool)
    {values : α → Index → Value} {index : α → Index} {value left right : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding)
    (hvalue : ComputableInPolyTime value input enc)
    (hl : ComputableInPolyTime left input enc)
    (hr : ComputableInPolyTime right input enc) :
    ComputableInPolyTime (fun a => values a (index a)) input enc ∧
    ComputableInPolyTime (fun a => Function.update (values a) (index a) (value a))
      input (encPi enc) ∧
    ComputableInPolyTime (fun _ : List Bool => fun i : Empty => Empty.elim i)
      encBits (encPi enc) ∧
    ComputableInPolyTime (fun vs : Bool → Empty => vs false) (encPi emptyEnc) emptyEnc ∧
    ComputableInPolyTime (fun a => fun b : Bool => if b then left a else right a)
      input (encPi enc) := by
  refine ⟨?_, ?_, ComputableInPolyTime.pi fun i => Empty.elim i,
    ComputableInPolyTime.pi_apply emptyEnc false, ?_⟩
  · fail_if_success (clear hvalues; fun_prop)
    fail_if_success (clear hindex; fun_prop)
    exact ComputableInPolyTime.pi_apply' hvalues hindex
  · fail_if_success (clear hvalue; fun_prop)
    fun_prop
  · apply ComputableInPolyTime.pi
    intro b
    cases b
    · exact hr
    · exact hl
