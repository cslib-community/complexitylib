/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops

/-! # A runtime-word fold with explicit independent time/workspace budgets -/

@[expose] public section
open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.exists_onWords,
      `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp_linear,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterateWhile,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus: {name}"

namespace ComplexityTests.Internal.OLoops

-- The input word and number of rounds vary. Only the accumulator and callback domains are fixed.
theorem parity : ComputableInO (fun w : List Bool => w.foldl Bool.xor false) encBits encBool
    (fun w => w.length + w.length + (w.length + 1) * (4 + 1 + w.length))
    (fun w => w.length + 0 + 4 + 1 + w.length) := by
  have hlist : ComputableInO (fun w : List Bool => w) encBits encBits
      List.length List.length := .of_eq fun _ => rfl
  have hinit : ComputableInO (fun _ : List Bool => false) encBits encBool
      List.length (fun _ => 0) := .constZero false
  have hstep : ComputableInO (fun p : Bool × Bool => Bool.xor p.1 p.2)
      (encPair encBool encBool) encBool
      (fun p => (encPair encBool encBool p).length)
      (fun p => (encPair encBool encBool p).length) := .of_linear (.of_finite _)
  apply ComputableInO.foldl hlist hinit hstep (R := fun _ => 4) (Q := fun _ => 4)
    (B := fun _ => 1)
  · intro w i _
    simp
  · intro w i _
    simp
  · intro w i _
    simp

/-- The complete runtime input includes both the polarity flag and the word. -/
def context : Bool × List Bool ↪ List Bool := encPair encBool encBits

def capturedStep (flag state bit : Bool) : Bool := state && if flag then bit else !bit

-- The captured flag is an encoded runtime value; one callback handles both polarities.
theorem captured : ComputableInO (fun p : Bool × List Bool => p.2.foldl (capturedStep p.1) true)
    context encBool
    (fun p => (context p).length + (context p).length + (context p).length +
      (p.2.length + 1) * (10 + 1 + (encBool p.1).length + (encBits p.2).length))
    (fun p => (context p).length + (context p).length + 0 + 10 + 1 +
      (encBool p.1).length + (encBits p.2).length) := by
  have hpar : ComputableInO Prod.fst context encBool
      (fun p => (context p).length) (fun p => (context p).length) := .fst _ _
  have hlist : ComputableInO Prod.snd context encBits
      (fun p => (context p).length) (fun p => (context p).length) := .snd _ _
  have hinit : ComputableInO (fun _ : Bool × List Bool => true) context encBool
      (fun p => (context p).length) (fun _ => 0) := .constZero true
  have hstep : ComputableInO (fun p : (Bool × Bool) × Bool => capturedStep p.1.1 p.1.2 p.2)
      (encPair (encPair encBool encBool) encBool) encBool
      (fun p => (encPair (encPair encBool encBool) encBool p).length)
      (fun p => (encPair (encPair encBool encBool) encBool p).length) := .of_linear (.of_finite _)
  apply ComputableInO.foldlWith hpar hlist hinit hstep
    (R := fun _ => 10) (Q := fun _ => 10) (B := fun _ => 1)
  · intro p i _
    simp
  · intro p i _
    simp
  · intro p i _
    simp

-- Concrete foldl traces and why a uniform efficient round is not itself a reachable-state bound.
example :
    [true, false].foldl (capturedStep true) true = false ∧
    [false, false].foldl (capturedStep false) true = true ∧
    ([] : List Bool).foldl Bool.xor false = false ∧
    [true, false, true].foldl Bool.xor false = false ∧
    ¬ (∀ word : List Bool, ∀ i ≤ word.length,
      (((word.take i).foldl (fun state _ => state ++ state) [true]).length ≤ 1)) := by
  refine ⟨rfl, rfl, rfl, rfl, fun h => ?_⟩
  have := h [false] 1 (by decide)
  simp at this

end ComplexityTests.Internal.OLoops
