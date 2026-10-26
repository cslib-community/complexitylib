/- Diagnostic-only #1155 dispatch forwarding. No FunProp/Aesop/program table changes. -/
module
public meta import Diag1155.MeasureBase

open Lean Elab Tactic
namespace Diag1155.Current

-- no_fallback prevents the original handler from being retried after a genuine failure.
-- unsupportedSyntax still falls through when the dispatch shape is not covered.
@[tactic Cslib.Tactic.PolyTime.tacticPolytime, no_fallback]
meta def measurePolytime : Tactic := measure

@[tactic Mathlib.Meta.FunProp.funPropTacStx, no_fallback]
meta def measureFunProp : Tactic := measure

@[tactic Cslib.Tactic.PPT.tacticPpt, no_fallback]
meta def measurePpt : Tactic := measure

end Diag1155.Current
