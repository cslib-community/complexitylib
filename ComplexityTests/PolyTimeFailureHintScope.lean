/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Tactic.PolyTime
import all Complexity.Tactic.PolyTime

/-! # Failure-hint scope and exceptional exits

These internal controls seed real backend failures inside the invocation wrapper, including
nested invocations. Lean's own exception constructors exercise resource and interrupt exits
without changing search limits or relying on machine-dependent resource exhaustion.
-/

open Lean Meta Elab Tactic Turing.MultiTapeTM Cslib.Tactic.PolyTime

namespace ComplexityTests.PolyTimeFailureHintScope

/-- Exercise a failed backend attempt and retain only the invocation's diagnostic state. -/
private meta def seedHint (type : Expr) : TacticM Unit := do
  let saved ← saveState
  try
    let goal ← mkFreshExprSyntheticOpaqueMVar type
    setGoals [goal.mvarId!]
    let result ← observing <| Internal.funPropWithPlainBoundary 256
    unless result matches .error _ do throwError "expected the backend to fail"
  finally
    saved.restore

private meta def failureMessage (action : TacticM Unit) : TacticM String := do
  let .error ex ← observing action | throwError "expected failure"
  ex.toMessageData.toString

private meta def checkHint (message expected unexpected : String) : TacticM Unit := do
  unless message.contains "polytime could not certify a subterm" && message.contains expected &&
      !message.contains unexpected do
    throwError "incorrect invocation hint\n{message}"

/-- Only this test observer catches all exceptions; the production wrapper uses normal catch. -/
private meta def observeAll (action : TacticM Unit) : TacticM (Except Exception Unit) :=
  (inferInstance : MonadAlwaysExcept Exception TacticM).except.tryCatch
    (do action; pure (.ok ())) (fun ex => pure (.error ex))

elab (name := checkFailureScope) "check_failure_scope " outer:term ", " inner:term : tactic => do
  let outer ← Term.elabType outer
  let inner ← Term.elabType inner
  let message ← failureMessage <| withFailureHint do
    let nested ← failureMessage <| withFailureHint do
      seedHint inner
      throwError "nested failure"
    checkHint nested "innerMissing" "outerMissing"
    -- The first nested invocation must restore the outer collector before it is populated.
    seedHint outer
    let nested ← failureMessage <| withFailureHint do
      seedHint inner
      throwError "nested failure"
    checkHint nested "innerMissing" "outerMissing"
    throwError "outer failure"
  checkHint message "outerMissing" "innerMissing"
  -- A successful invocation can have failed routes; neither exit may leave a collector behind.
  withFailureHint (seedHint outer)
  unless (failureHint.getState (← getEnv)).isNone do
    throwError "failure hint escaped its invocation"
  let message ← failureMessage <| withFailureHint (throwError "unseeded failure")
  unless message == "unseeded failure" do throwError "unexpected unseeded hint\n{message}"
  let raises : Array (TacticM Unit × (Exception → Bool)) := #[
    ((do Core.throwMaxHeartbeat `polytimeFailureHint `maxHeartbeats 1000),
      Exception.isMaxHeartbeat),
    (throwMaxRecDepthAt (← getRef), Exception.isMaxRecDepth),
    (throwInterruptException, Exception.isInterrupt)]
  for (raise, isExpected) in raises do
    let .error original ← observeAll raise | throwError "expected a resource or interrupt exception"
    let .error wrapped ← observeAll <| withFailureHint do
      seedHint outer
      raise
      | throwError "expected the wrapped exception"
    unless isExpected wrapped &&
        (← wrapped.toMessageData.toString) == (← original.toMessageData.toString) do
      throwError "the failure wrapper changed a resource or interrupt exception"
    unless (failureHint.getState (← getEnv)).isNone do
      throwError "failure hint escaped an exceptional exit"

local allow_unused_tactic checkFailureScope

#guard_msgs in
example (outerMissing innerMissing : List Bool → Bool) :
    (outerMissing, innerMissing) = (outerMissing, innerMissing) := by
  check_failure_scope (ComputableInPolyTime outerMissing encBits encBool),
    (ComputableInPolyTime innerMissing encBits encBool)
  rfl

end ComplexityTests.PolyTimeFailureHintScope
