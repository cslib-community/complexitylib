/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives


import Diag1155.Measure
/-! # Direct finite tables with captured inputs and empty types -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

example {α Index Value : Type} [Fintype Index]
    {input : α ↪ List Bool} {enc : Value ↪ List Bool} {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding) :
    ComputableInPolyTime (fun a => values a (index a)) input enc := by
  fail_if_success (clear hvalues; fun_prop)
  fail_if_success (clear hindex; fun_prop)
  exact ComputableInPolyTime.pi_apply' hvalues hindex

example {α Index Value : Type} [Fintype Index] [DecidableEq Index]
    {input : α ↪ List Bool} {enc : Value ↪ List Bool} {indexEncoding : Index ↪ List Bool}
    {values : α → Index → Value} {index : α → Index} {value : α → Value}
    (hvalues : ComputableInPolyTime values input (encPi enc))
    (hindex : ComputableInPolyTime index input indexEncoding)
    (hvalue : ComputableInPolyTime value input enc) :
    ComputableInPolyTime (fun a => Function.update (values a) (index a) (value a))
      input (encPi enc) := by
  fail_if_success (clear hvalue; fun_prop)
  fun_prop

-- An empty index does not require an inhabitant of the value type.
example {Value : Type} (encoding : Value ↪ List Bool) :
    ComputableInPolyTime (fun _ : List Bool => fun i : Empty => Empty.elim i)
      encBits (encPi encoding) :=
  ComputableInPolyTime.pi fun i => Empty.elim i

-- Fixed lookup retains the empty-value case without a default-value hypothesis.
example (encoding : Empty ↪ List Bool) :
    ComputableInPolyTime (fun values : Bool → Empty => values false) (encPi encoding) encoding :=
  ComputableInPolyTime.pi_apply encoding false

example {α Value : Type} {input : α ↪ List Bool} {encoding : Value ↪ List Bool}
    {left right : α → Value}
    (hl : ComputableInPolyTime left input encoding)
    (hr : ComputableInPolyTime right input encoding) :
    ComputableInPolyTime (fun a => fun b : Bool => if b then left a else right a)
      input (encPi encoding) := by
  apply ComputableInPolyTime.pi
  intro b
  cases b
  · exact hr
  · exact hl

/--
info: 'Turing.MultiTapeTM.ComputableInPolyTime.pi_apply'' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.pi_apply'

/--
info: 'Turing.MultiTapeTM.ComputableInPolyTime.pi_update'' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.pi_update'
