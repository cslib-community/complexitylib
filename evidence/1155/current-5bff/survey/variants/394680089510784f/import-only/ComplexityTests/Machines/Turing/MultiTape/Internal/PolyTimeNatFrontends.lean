/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends


import Diag1155.Measure
/-! # Direct landed unary comparison, range and bit-access interfaces -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

example {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a => List.range (n a)) input (encList encUnary) :=
  ComputableInPolyTime.unary_range' hn

example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encUnary)
    (hr : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool := by
  fail_if_success (clear hl; fun_prop)
  fail_if_success (clear hr; fun_prop)
  fun_prop

example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encUnary)
    (hr : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool := by
  fun_prop

example {α : Type} {input : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n input encNat)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (n a).testBit (i a)) input encBool := by
  fail_if_success (clear hn; fun_prop)
  fail_if_success (clear hi; fun_prop)
  fun_prop

example {α : Type} {input : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (n a).testBit (i a)) input encBool := by
  fail_if_success (clear hn; fun_prop)
  fail_if_success (clear hi; fun_prop)
  fun_prop

example : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat :=
  ComputableInPolyTime.unary_to_binary

example : (List.range 0 : List ℕ) = [] := rfl
example : decide (0 < 0) = false := rfl
example : decide (0 ≤ 0) = true := rfl
example : Nat.testBit 0 100 = false := by decide
example : Nat.testBit 8 3 = true := by decide
example : Nat.testBit 8 4 = false := by decide

/--
info: 'Turing.MultiTapeTM.ComputableInPolyTime.unary_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.unary_le

/--
info: 'Turing.MultiTapeTM.ComputableInPolyTime.binary_testBit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.binary_testBit


-- The registered identity is automatic; opaque computed callbacks retain the direct generic
-- composition API. Only the proved unary-to-binary direction is available.
example : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat := by fun_prop

example {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime n input encNat := by
  fail_if_success (clear hn; fun_prop)
  exact ComputableInPolyTime.unary_to_binary.comp hn

example : True := by
  fail_if_success
    have : ComputableInPolyTime (fun n : ℕ => n) encNat encUnary := by fun_prop
  trivial
