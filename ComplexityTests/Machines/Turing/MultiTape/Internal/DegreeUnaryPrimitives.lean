/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives
import Lean.Elab.Command

/-! Unary certificates and their zero, one, and unbounded runtime-parameter boundaries. -/
open Turing.MultiTapeTM
example (n : ℕ) :
    ComputableInDegree (· + 1) encUnary encUnary 1 1 ∧
    ComputableInDegree (· - 1) encUnary encUnary 1 1 ∧
    encUnary (0 + 1) = [true] ∧
    encUnary (0 - 1) = [] ∧
    encUnary (1 - 1) = [] ∧
    encUnary (1 + 1) = [true, true] ∧
    (encUnary (n + 1)).length = n + 1 ∧
    (encUnary (n - 1)).length = n - 1 ∧
    ComputableInDegree (fun n => decide (n = 0)) encUnary encBool 1 1 ∧
    encBool (decide (0 = 0)) = [true] ∧
    encBool (decide (1 = 0)) = [false] ∧
    encBool (decide (n + 1 = 0)) = [false] := by
  fail_if_success
    have : ComputableInDegree (· + 1) encUnary encUnary 0 1 := .unary_succ
  exact ⟨.unary_succ, .unary_pred, rfl, rfl, rfl, rfl, by simp, by simp,
    .unary_isZero, rfl, rfl, by simp⟩

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolySpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
