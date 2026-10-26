/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Tactic.PPT
public import Complexity.Tactic.PolyTime

/-! # Classification memo scope without projecting unrelated search rules -/

public section
open Turing.MultiTapeTM
open Lean Elab Tactic

namespace ComplexityTests.PPTMemoScope

/-- An opaque routine has only a global construction certificate. -/
@[irreducible] def rawRoutine (word : List Bool) : List Bool := word.reverse

/-- Global construction evidence remains available to ordinary search. -/
@[fun_prop] theorem rawRoutine_raw : ComputableTidilyInPolyTime rawRoutine encBits encBits := by
  unfold rawRoutine
  exact ComputableInPolyTime.bitsReverse.tidy

/-- A complete-arity alias tests fresh local proposition handling inside the memo scope. -/
abbrev RawAlias {α β : Type*} (f : α → β) (input : α ↪ List Bool) (output : β ↪ List Bool) :=
  ComputableTidilyInPolyTime f input output

/-- The result has no global automation certificate. -/
@[irreducible] def localResult (word : List Bool) : List Bool := word

-- The memo alone filters neither ordinary FunProp nor the builtin local-application descriptor.
example (h : ComputableTidilyInPolyTime rawRoutine encBits encBits →
    ComputableInPolyTime localResult encBits encBits) :
    ComputableInPolyTime localResult encBits encBits := by
  run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
    Lean.Elab.Tactic.evalTactic (← `(tactic| fail_if_success polytime))
    Lean.Elab.Tactic.evalTactic (← `(tactic| aesop (rule_sets := [PolyTime])))

example : ComputableInPolyTime rawRoutine encBits encBits := by
  run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
    Lean.Elab.Tactic.evalTactic (← `(tactic| fun_prop))

-- Complete local facts remain usable; clearing one cannot be masked by a cached proof.
example (routine : List Bool → List Bool)
    (h : RawAlias routine encBits encBits → ComputableInPolyTime localResult encBits encBits)
    (hf : RawAlias routine encBits encBits) :
    ComputableInPolyTime localResult encBits encBits := by
  run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
    Lean.Elab.Tactic.evalTactic (← `(tactic| fail_if_success (clear hf; polytime)))
    Lean.Elab.Tactic.evalTactic (← `(tactic| polytime))

-- Exceptions restore the scoped environment before ordinary global construction search.
example : ComputableInPolyTime rawRoutine encBits encBits := by
  run_tac do
    try
      Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
        throwError "expected memo-scope exception"
    catch _ => pure ()
    Lean.Elab.Tactic.evalTactic (← `(tactic| fail_if_success polytime))
    Lean.Elab.Tactic.evalTactic (← `(tactic| fun_prop))

end ComplexityTests.PPTMemoScope
