/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Option
public import CslibFrontier.Tactic.FailureNote
public import CslibFrontier.Tactic.OptionMatch

/-!
# Degree certificates by composition

`degree` proves a goal `ComputableInDegree f encIn encOut d e` from the `fun_prop` rules of the
operations in `f`. It rewrites each `match` on an option to `Option.elim`, then runs `fun_prop`,
which discharges the degree side conditions of its composition rules with `lia`.

Like `fun_prop`, it does not unfold definitions: unfold a definition first, or register a named
certificate for it with `fun_prop`. On another goal it fails at once, and when the search fails
the `fun_prop` error ends with a note saying so.

## Main definitions

* `degree`: prove a degree certificate by composition.
-/

public section

namespace Turing.MultiTapeTM

/-- Prove `ComputableInDegree f encIn encOut d e` by composing the `fun_prop` rules of the
operations in `f`, after rewriting option matches to `Option.elim`. -/
syntax (name := degreeTac) "degree" : tactic

open Lean Elab Tactic in
/-- Elaborate `degree`: check the goal, then compose with `fun_prop`. -/
@[tactic degreeTac] meta def evalDegree : Tactic := fun _ => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ComputableInDegree do
    throwError "degree expects a goal `ComputableInDegree f encIn encOut d e`, \
      got{indentExpr target}"
  Cslib.Tactic.withFailureNote m!"degree composes `@[fun_prop]` rules for `ComputableInDegree` \
      and does not unfold definitions. Unfold a local definition first, or prove a certificate \
      for the operation named above and tag it `@[fun_prop]`." do
    evalTactic (← `(tactic| try option_match_to_elim))
    evalTactic (← `(tactic| fun_prop (disch := first | apply le_refl | lia)))

end Turing.MultiTapeTM
