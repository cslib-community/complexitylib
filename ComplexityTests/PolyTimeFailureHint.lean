/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime

/-! # Polynomial-time failure hints

Ordinary imported clients exercise missing callbacks, captured variables and recovery into a
successful proof. Each failed invocation must report its own subterm, without leaking into a
subsequent invocation or changing the successful tactic's output.
-/

open Lean Meta Elab Tactic Turing.MultiTapeTM

namespace ComplexityTests.PolyTimeFailureHint

/-- Check a real failed invocation while preserving the surrounding proof and its goals. -/
private meta def checkFailure (type : Expr) (required forbidden : Array String) : TacticM Unit := do
  let saved ← saveState
  try
    let goal ← mkFreshExprSyntheticOpaqueMVar type
    setGoals [goal.mvarId!]
    let result ← observing <| Term.withoutErrToSorry <| withoutRecover <|
      evalTactic (← `(tactic| polytime))
    let .error ex := result | throwError "expected polytime to fail"
    let message ← ex.toMessageData.toString
    let marker := "polytime could not certify a subterm"
    let [_, hint] := message.splitOn marker | throwError "expected one failure hint\n{message}"
    let hint := marker ++ hint
    for text in required do
      unless hint.contains text do
        throwError "missing diagnostic fragment {text}\n{message}"
    for text in forbidden do
      if hint.contains text then
        throwError "unexpected diagnostic fragment {text}\n{message}"
  finally
    saved.restore

elab (name := checkPolytimeFailure)
    "check_polytime_failure " target:term " containing " "[" required:str,* "]"
    " excluding " "[" forbidden:str,* "]" : tactic => do
  checkFailure (← Term.elabType target)
    (required.getElems.map (·.getString)) (forbidden.getElems.map (·.getString))

local allow_unused_tactic checkPolytimeFailure

-- A callback is certified when supplied, and is named when its certificate is missing.
example (missingCallback : List Bool → Bool) : missingCallback = missingCallback := by
  check_polytime_failure
    (ComputableInPolyTime (fun word => !(missingCallback word)) encBits encBool)
    containing ["polytime could not certify a subterm", "missingCallback", "encBits"]
    excluding ["unknown free variable"]
  rfl

#guard_msgs in
example (callback : List Bool → Bool)
    (hcallback : ComputableInPolyTime callback encBits encBool) :
    ComputableInPolyTime (fun word => !(callback word)) encBits encBool := by
  polytime

-- Captured parameters remain readable after the backend has closed its telescope.
example (missingCaptured : List Bool → List Bool → Bool) : missingCaptured = missingCaptured := by
  check_polytime_failure
    (ComputableInPolyTime (fun pair : List Bool × List Bool =>
      !(missingCaptured pair.1 pair.2)) (encPair encBits encBits) encBool)
    containing ["polytime could not certify a subterm", "missingCaptured", "encPair"]
    excluding ["unknown free variable"]
  rfl

-- Repeated invocations in one elaboration may not retain a prior callback's failure.
example (firstMissing secondMissing : List Bool → Bool) :
    (firstMissing, secondMissing) = (firstMissing, secondMissing) := by
  check_polytime_failure (ComputableInPolyTime firstMissing encBits encBool)
    containing ["polytime could not certify a subterm", "firstMissing", "encBits", "encBool"]
    excluding ["secondMissing"]
  check_polytime_failure (ComputableInPolyTime secondMissing encBits encBool)
    containing ["polytime could not certify a subterm", "secondMissing"] excluding ["firstMissing"]
  rfl

-- A failed alternative leaves ordinary successful certificate search available and silent.
#guard_msgs in
example (callback : List Bool → Bool)
    (hcallback : ComputableInPolyTime callback encBits encBool) :
    ComputableInPolyTime (fun word => !(callback word)) encBits encBool := by
  fail_if_success (clear hcallback; polytime)
  polytime

end ComplexityTests.PolyTimeFailureHint
