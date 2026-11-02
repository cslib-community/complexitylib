/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import ComplexityResults
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-! Registry references resolve through imports; failed commands do not add partial records. -/

register_result "registry-fixture" where
  title := "Parameterized mapping"
  topic := "regression fixture"
  sources := [{ paper := AroraBarak09, theorem := "Fixture only", locator := unverified }]
  theorems := [Turing.MultiTapeTM.ComputableInSpace.mapWith]
  scope := "A checked existing theorem used to exercise registry elaboration."

/-- error: result ID must contain lowercase letters, digits or hyphens -/
#guard_msgs in
register_result "bad--id" where
  title := "Malformed ID"
  topic := "regression fixture"
  sources := [{ paper := AroraBarak09, theorem := unverified, locator := unverified }]
  theorems := [Nat.succ]
  scope := "Rejected before registration."

/-- error: duplicate result ID: registry-fixture -/
#guard_msgs in
register_result "registry-fixture" where
  title := "Duplicate"
  topic := "regression fixture"
  sources := [{ paper := AroraBarak09, theorem := unverified, locator := unverified }]
  theorems := [Turing.MultiTapeTM.ComputableInSpace.mapWith]
  scope := "Rejected."

/-- error: duplicate registered theorem: Turing.MultiTapeTM.ComputableInSpace.mapWith -/
#guard_msgs in
register_result "registry-duplicate" where
  title := "Duplicate theorem"
  topic := "regression fixture"
  sources := [{ paper := AroraBarak09, theorem := unverified, locator := unverified }]
  theorems := [Turing.MultiTapeTM.ComputableInSpace.mapWith]
  scope := "Rejected."

/-- error: Unknown constant `Missing.registryTheorem` -/
#guard_msgs in
register_result "registry-missing" where
  title := "Missing name"
  topic := "regression fixture"
  sources := [{ paper := AroraBarak09, theorem := unverified, locator := unverified }]
  theorems := [Missing.registryTheorem]
  scope := "Rejected."

/-- error: registered declarations must be propositions -/
#guard_msgs in
register_result "registry-nonprop" where
  title := "A function is not a theorem"
  topic := "regression fixture"
  sources := [{ paper := AroraBarak09, theorem := unverified, locator := unverified }]
  theorems := [Nat.succ]
  scope := "Rejected."

private theorem hiddenRegistry : True := True.intro

/-- error: private declarations cannot be registered -/
#guard_msgs in
register_result "registry-private" where
  title := "A private declaration"
  topic := "regression fixture"
  sources := [{ paper := AroraBarak09, theorem := unverified, locator := unverified }]
  theorems := [hiddenRegistry]
  scope := "Rejected."

open Lean Elab Command in
run_cmd do
  let registered := ComplexityResults.entries.getState (← getEnv)
  unless (registered.filter (·.id == "registry-fixture")).size == 1 do
    throwError "the valid fixture was not registered exactly once"
  if registered.any (fun entry => ["registry-duplicate", "registry-missing", "registry-nonprop",
      "registry-private"].contains entry.id) then
    throwError "a rejected command left a partial registry record"
