/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-! # Direct landed unary comparison, range and bit-access interfaces -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

example {α : Type} {input : α ↪ List Bool} {n left right i : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hnNat : ComputableInPolyTime n input encNat)
    (hl : ComputableInPolyTime left input encUnary)
    (hr : ComputableInPolyTime right input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => List.range (n a)) input (encList encUnary) ∧
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool ∧
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool ∧
    ComputableInPolyTime (fun a => (n a).testBit (i a)) input encBool ∧
    ComputableInPolyTime (fun a => (n a).testBit (i a)) input encBool ∧
    ComputableInPolyTime (fun n : ℕ => n) encUnary encNat ∧
    (List.range 0 : List ℕ) = [] ∧
    decide (0 < 0) = false ∧
    decide (0 ≤ 0) = true ∧
    Nat.testBit 0 100 = false ∧
    Nat.testBit 8 3 = true ∧
    Nat.testBit 8 4 = false ∧
    ComputableInPolyTime (fun n : ℕ => n) encUnary encNat ∧
    ComputableInPolyTime n input encNat := by
  fail_if_success
    have : ComputableInPolyTime (fun n : ℕ => n) encNat encUnary := by fun_prop
  refine ⟨ComputableInPolyTime.unary_range' hn, ?_, by fun_prop, ?_, ?_,
    ComputableInPolyTime.unary_to_binary, rfl, rfl, rfl,
    by decide, by decide, by decide, by fun_prop, ?_⟩
  · fail_if_success (clear hl; fun_prop)
    fail_if_success (clear hr; fun_prop)
    fun_prop
  · clear hn
    fail_if_success (clear hnNat; fun_prop)
    fail_if_success (clear hi; fun_prop)
    fun_prop
  · clear hnNat
    fail_if_success (clear hn; fun_prop)
    fail_if_success (clear hi; fun_prop)
    fun_prop
  · clear hnNat
    fail_if_success (clear hn; fun_prop)
    exact ComputableInPolyTime.unary_to_binary.comp hn
