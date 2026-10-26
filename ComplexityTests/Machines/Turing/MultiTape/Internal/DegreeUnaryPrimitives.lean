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
example : ComputableInDegree (· + 1) encUnary encUnary 1 1 := .unary_succ
example : ComputableInDegree (· - 1) encUnary encUnary 1 1 := .unary_pred
example : encUnary (0 + 1) = [true] := rfl
example : encUnary (0 - 1) = [] := rfl
example : encUnary (1 - 1) = [] := rfl
example : encUnary (1 + 1) = [true, true] := rfl
example (n : ℕ) : (encUnary (n + 1)).length = n + 1 := by simp
example (n : ℕ) : (encUnary (n - 1)).length = n - 1 := by simp

example : ComputableInDegree (fun n => decide (n = 0)) encUnary encBool 1 1 := .unary_isZero
example : encBool (decide (0 = 0)) = [true] := rfl
example : encBool (decide (1 = 0)) = [false] := rfl
example (n : ℕ) : encBool (decide (n + 1 = 0)) = [false] := by simp

-- The original degree-one cost is retained; no constant-time rule is silently substituted.
example : True := by
  fail_if_success
    have : ComputableInDegree (· + 1) encUnary encUnary 0 1 := .unary_succ
  trivial

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO, `Turing.MultiTapeTM.ComputableTidilyInSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolySpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
