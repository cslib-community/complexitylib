/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public import CslibFrontier.Tactic.FailureNote
public meta import Lean.Elab.Tactic

/-!
# Composing explicit workspace certificates

`space` proves a `ComputableInSpace` goal by the existing budget-preserving `fun_prop` rules.
`space [f, g]` unfolds the indicated program definitions. Local routine certificates are reused;
unproved size inequalities and iteration invariants are not guessed. An input-length side
condition must be reflexive or supplied in the context. When the search fails, the `fun_prop`
error ends with a note naming these inputs.

This tactic does not assert logarithmic space in the original input: the goal specifies the
encoding and budget. In particular, a Savitch callback is linear-space in the stored state,
while a separate invariant bounds that state's length by a quadratic logarithm.

## Main definitions

* `space`: compose certificates within the goal's explicit workspace budget.
-/

public meta section

open Lean Elab Tactic Turing.MultiTapeTM

/-- Compose explicit space certificates, optionally unfolding the named program definitions. -/
syntax (name := spaceTac) "space" (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| space $[[$defs,*]]?) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``Turing.MultiTapeTM.ComputableInSpace do
      throwError "space expects a ComputableInSpace goal with an explicit budget"
    let defs := (defs.map (·.getElems)).getD #[]
    Cslib.Tactic.withFailureNote m!"space composes `@[fun_prop]` rules for `ComputableInSpace` \
        within the goal's budget. Supply a certificate for each local routine, unfold a program \
        definition with `space [f]`, and supply a nontrivial input-length allowance \
        `(fun a => (encIn a).length) ≼ S` as a hypothesis." do
      evalTactic (← `(tactic| fun_prop (config := { maxSteps := 256 })
        (disch := first | assumption | exact BigOLe.refl _) [$defs,*]))

end
