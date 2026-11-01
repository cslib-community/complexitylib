/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
public import Complexity.Tactic.LogSpace.Init
public import Complexity.Tactic.PolyTime.Init

/-!
# Synthesizing bounded logspace computations

`logspace` combines the existing plain `fun_prop` calculus with bounded answer-vector
construction. A local hypothesis `∀ a, r a ≤ k` selects the constant bound in
`ComputableInLogSpace.mapToBits_range_of_le`; the count and indexed callback still need their
own certificates with the exact input and output encodings. In particular, this rule does not
claim arbitrary polynomially long answer vectors are logspace computable.

Local routine certificates are tried through recomputing logspace composition, including calls
on prepared tuple arguments. Search stays in `ComputableInLogSpace`: it never converts a goal
to polynomial time or to a tidy predicate. Importing this module adds no `fun_prop` transition.

## Main definitions

* `logspace`: close a plain logspace goal using local bounds, routine certificates and composition.
-/

public section

namespace Cslib.Tactic.LogSpace

open Turing.MultiTapeTM Lean Meta Elab Tactic

namespace Internal

/-- Curried callbacks let unification determine the indexed program from a map body.
This kernel declaration is public because runtime tactic application uses ordinary imports. -/
theorem mapToBitsRange {α : Type} {enc : α ↪ List Bool}
    {r : α → ℕ} {f : α → ℕ → Bool} (k : ℕ)
    (hr : ComputableInLogSpace r enc encUnary) (hrk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace (fun p : α × ℕ => f p.1 p.2)
      (encPair enc encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map (f a)) enc encBits :=
  ComputableInLogSpace.mapToBits_range_of_le k hr hrk hf

end Internal

/-- Preserve each matching supplied bound as a separate search alternative. Selecting the bound
first determines the count function and constant without guessing either from a data goal. -/
@[aesop unsafe 90% tactic (rule_sets := [LogSpace])]
private meta def boundedAnswers : Aesop.RuleTac := fun input => input.goal.withContext do
  let target := (← instantiateMVars (← input.goal.getType)).consumeMData
  unless target.isAppOf ``ComputableInLogSpace do throwError "expected a logspace goal"
  let initial ← saveState
  let mut applications := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let bound ← forallTelescopeReducing decl.type fun xs body =>
      pure (!xs.isEmpty && body.isAppOf ``LE.le)
    unless bound do continue
    try
      let goals ← input.goal.applyConst ``Internal.mapToBitsRange
      let some boundGoal ← goals.findM? fun goal => do
          isDefEq (← goal.getType) decl.type
        | throwError "bound does not match"
      boundGoal.assign decl.toExpr
      let goals ← goals.filterM fun goal => return !(← goal.isAssigned)
      if ← Aesop.hasSorry (mkMVar input.goal) then throwError "admitted bound"
      let goals ← goals.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
      applications := applications.push {
        goals
        postState := ← saveState
        scriptSteps? := none
        successProbability? := none }
    catch _ => pure ()
    finally initial.restore
  if applications.isEmpty then throwError "no matching constant bound"
  return ⟨applications⟩

-- Expose tuple preparation when one component needs a bounded construction.
attribute [aesop unsafe 85% apply (rule_sets := [LogSpace])] ComputableInLogSpace.pair

/-- Reuse local routines before unfolding their implementation. -/
@[aesop unsafe 100% tactic (rule_sets := [LogSpace])]
private meta def knownCall : Aesop.RuleTac :=
  Cslib.Tactic.applyKnownCall ``ComputableInLogSpace 2 ``ComputableInLogSpace.comp `f `hg

/-- Composition closes ordinary leaves; bounded construction is a separate alternative. -/
@[aesop unsafe 95% tactic (rule_sets := [LogSpace])]
private meta def compositional : TacticM Unit := withMainContext do
  unless (← getMainTarget).isAppOf ``ComputableInLogSpace do
    throwError "expected a logspace goal"
  Term.withoutErrToSorry <| withoutRecover do
    evalTactic (← `(tactic| solve | fun_prop (config := { maxSteps := 256 })))

end Cslib.Tactic.LogSpace

open Lean Meta Elab Tactic in
/-- Prove a plain logspace certificate using composition and supplied constant bounds. -/
elab "logspace" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Turing.MultiTapeTM.ComputableInLogSpace do
    throwError "expected a plain logspace certificate"
  evalTactic (← `(tactic| solve |
    aesop (config := { terminal := true, enableSimp := false })
      (rule_sets := [LogSpace])))

end
