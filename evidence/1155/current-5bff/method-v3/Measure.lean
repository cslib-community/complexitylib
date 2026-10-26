/- Diagnostic-only #1155 dispatch forwarding. No FunProp/Aesop/program table changes. -/
module
public meta import Diag1155.MeasureBase
public meta import Lean.Elab.Command

public section
open Lean Elab Tactic
namespace Diag1155.Current

/-- Install forwarding only after the original file imports have established their syntax kinds.
The diagnostic environment alone is changed; compiled original dependencies are never rewritten. -/
elab "diag1155_install" : command => do
  for kind in #[`Cslib.Tactic.PolyTime.tacticPolytime,
      `Mathlib.Meta.FunProp.funPropTacStx, `Cslib.Tactic.PPT.tacticPpt] do
    if (← getEnv).contains kind then
      let entry : KeyedDeclsAttribute.AttributeEntry Tactic := {
        key := kind
        declName := ``measure
        value := measure
        isBuiltin := false
      }
      modifyEnv fun env => tacticElabAttribute.ext.modifyState env (·.insert entry)

end Diag1155.Current
