/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Computed unary operands retain the complete common input and both certificates.
Positive and missing-left/right controls use the same explicit 256-step search bound;
these are configured-search controls, not a claim about default exhaustive rejection cost.
-/

open Turing.MultiTapeTM

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a + right a) input encUnary := by
  fun_prop (maxSteps := 256)

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) : True := by
  fail_if_success
    clear _hleft
    have : ComputableInPolyTime (fun a => left a + right a) input encUnary := by
      fun_prop (maxSteps := 256)
  trivial

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) : True := by
  fail_if_success
    clear _hright
    have : ComputableInPolyTime (fun a => left a + right a) input encUnary := by
      fun_prop (maxSteps := 256)
  trivial

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a - right a) input encUnary := by
  fun_prop (maxSteps := 256)

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) : True := by
  fail_if_success
    clear _hleft
    have : ComputableInPolyTime (fun a => left a - right a) input encUnary := by
      fun_prop (maxSteps := 256)
  trivial

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) : True := by
  fail_if_success
    clear _hright
    have : ComputableInPolyTime (fun a => left a - right a) input encUnary := by
      fun_prop (maxSteps := 256)
  trivial

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a * right a) input encUnary := by
  fun_prop (maxSteps := 256)

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) : True := by
  fail_if_success
    clear _hleft
    have : ComputableInPolyTime (fun a => left a * right a) input encUnary := by
      fun_prop (maxSteps := 256)
  trivial

set_option maxHeartbeats 200000 in
-- Keep the original heartbeat budget, with the same explicit search bound on both controls.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (_hleft : ComputableInPolyTime left input encUnary)
    (_hright : ComputableInPolyTime right input encUnary) : True := by
  fail_if_success
    clear _hright
    have : ComputableInPolyTime (fun a => left a * right a) input encUnary := by
      fun_prop (maxSteps := 256)
  trivial
