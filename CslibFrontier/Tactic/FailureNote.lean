/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public meta import Lean.Elab.Tactic

/-!
# Failure notes for search tactics

When a search tactic fails, the error comes from its backend: an exhausted Aesop search or a
`fun_prop` premise without a rule. `withFailureNote` keeps that error and appends a note saying
what the tactic needs from the user, as `polytime` does with its failure hint. The search is
unchanged, and resource limits and interrupts pass through without a note.

## Main definitions

* `Cslib.Tactic.withFailureNote`: run a tactic and append a note to its error.
-/

public meta section

namespace Cslib.Tactic

open Lean Elab Tactic

/-- Run `tac`. If it fails with an error, rethrow that error with `note` appended. Lean does not
let this `catch` intercept resource limits or interrupts. -/
def withFailureNote (note : MessageData) (tac : TacticM Unit) : TacticM Unit :=
  try tac catch ex =>
    match ex with
    | .error ref msg => throw <| .error ref (msg ++ .note note)
    | .internal .. => throw ex

end Cslib.Tactic
