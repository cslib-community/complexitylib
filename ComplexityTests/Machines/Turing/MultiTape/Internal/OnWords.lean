/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.OnWords

/-! # The selected-tape helpers stay below the higher tidy calculus -/

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.exists_onWords] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus: {name}"

run_elab do
  for name in #[`Turing.MultiTapeTM.transformsTapes_outputToWord,
      `Turing.MultiTapeTM.transformsTapes_inputFromWord_fun,
      `Turing.MultiTapeTM.transformsTapes_onWords] do
    discard <| Lean.getConstInfo name

-- The moved public machine retains its exposed program data, not just a run equivalence.
example {k : ℕ} {Symbol State : Type*} (tm : Turing.MultiTapeTM k Symbol State)
    (mark : Symbol) : tm.onWords mark = tm.outputToWord.inputFromWord mark := rfl
