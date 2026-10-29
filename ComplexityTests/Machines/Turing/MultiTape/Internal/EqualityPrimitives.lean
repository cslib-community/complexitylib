/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Lean.Elab.Command

/-! Direct word comparison, including empty inputs and unequal-length words. -/

open Turing.MultiTapeTM

example {α : Type} [DecidableEq α] (enc : α ↪ List Bool) (left right : List Bool)
    {β γ : Type*} {input : β ↪ List Bool} {output : γ ↪ List Bool}
    {f : β → γ} {e : ℕ} (h : ComputableInDegree f input output 0 e) :
    ComputableInO (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool
      (fun p => (p.1.length + 1) * (p.1.length + p.2.length + 1))
      (fun p => p.1.length + p.2.length + 1) ∧
    ComputableInO (fun p : α × α => decide (p.1 = p.2)) (encPair enc enc) encBool
      (fun p => ((enc p.1).length + 1) * ((enc p.1).length + (enc p.2).length + 1))
      (fun p => (encPair enc enc p).length) ∧
    EqWords.step ([], true) false = ([], false) ∧
    EqWords.step ([true, false], true) true = ([false], true) ∧
    EqWords.step ([true], true) false = ([], false) ∧
    ((left.foldl EqWords.step (right, true)).2 &&
      (left.foldl EqWords.step (right, true)).1.isEmpty) = decide (left = right) ∧
    ComputableInO f input output (fun _ => 1) (fun _ => 1) := by
  refine ⟨.eqWords, .eq enc, rfl, rfl, rfl, ?_, ?_⟩
  · simpa using EqWords.foldl_result left right true
  · simpa using h.inO

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
