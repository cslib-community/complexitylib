/- Diagnostic-only behavioral counter/state control for post-original unsupportedSyntax. -/
module
import Mathlib.Tactic.FunProp
meta import Lean.Elab.Command
meta import Lean.Elab.Tactic.Basic


import Diag1155.Measure

diag1155_install
open Lean Elab Command Tactic Meta

-- The fixture changes ONLY the tactic-dispatch value at the real existing origin. No
-- FunProp property/function/transition rules are changed. Both baseline and measured
-- variants execute the same controlled single-original case, in a restored environment.
run_elab do
  let env ← getEnv
  let kind := `Mathlib.Meta.FunProp.funPropTacStx
  let entries := tacticElabAttribute.getEntries env kind
  let originals := entries.filter fun e => !(`Diag1155.Current).isPrefixOf e.declName
  let [original] := originals | throwError "expected exactly one original"
  let forwarding := entries.filter fun e => (`Diag1155.Current).isPrefixOf e.declName
  let invocations ← IO.mkRef 0
  let controlled : Tactic := fun _ => do
    invocations.modify (· + 1)
    (← getMainGoal).assign (mkConst ``True.intro)
    throwUnsupportedSyntax
  let replacement := { original with value := controlled }
  withEnv (tacticElabAttribute.ext.modifyState env fun state =>
      { state with table := state.table.insert kind (forwarding ++ [replacement]) }) do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let failed ← try
      let _ ← Tactic.run goal.mvarId! (evalTactic (← `(tactic| fun_prop)))
      pure false
    catch _ => pure true
    unless failed do throwError "unsupported original was accepted"
    unless (← invocations.get) == 1 do throwError "original was invoked more than once"
    if ← goal.mvarId!.isAssigned then throwError "unsupported original state was not restored"

private def privateWord (word : List Bool) : List Bool := word
private theorem privateWord_id (word : List Bool) : privateWord word = word := rfl
public theorem namedReflexive (word : List Bool) : word = word := privateWord_id word
