/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives


import Diag1155.Measure
/-! NEW depth-four Boolean representative, not the lost historical reviewer probe.
Every guard/branch has the same full captured input. The deepest branch certificate is required.
-/
open Turing.MultiTapeTM

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example {α : Type} {input : α ↪ List Bool} {p q r s left right : α → Bool}
    (hp : ComputableInPolyTime p input encBool) (hq : ComputableInPolyTime q input encBool)
    (hr : ComputableInPolyTime r input encBool) (hs : ComputableInPolyTime s input encBool)
    (hleft : ComputableInPolyTime left input encBool)
    (hright : ComputableInPolyTime right input encBool) :
    ComputableInPolyTime (fun a =>
      if p a then (if q a then (if r a then (if s a then left a else right a)
        else right a) else right a) else right a) input encBool := by
  fun_prop

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example {α : Type} {input : α ↪ List Bool} {p q r s left right : α → Bool}
    (_hp : ComputableInPolyTime p input encBool) (_hq : ComputableInPolyTime q input encBool)
    (_hr : ComputableInPolyTime r input encBool) (_hs : ComputableInPolyTime s input encBool)
    (_hleft : ComputableInPolyTime left input encBool)
    (_hright : ComputableInPolyTime right input encBool) : True := by
  fail_if_success
    clear _hleft
    have : ComputableInPolyTime (fun a =>
        if p a then (if q a then (if r a then (if s a then left a else right a)
          else right a) else right a) else right a) input encBool := by
      fun_prop
  trivial
