/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public meta import Lean.Elab.Tactic

/-!
# Option matches as eliminators

`fun_prop` cannot see through a `match`: its auxiliary matcher is a constant of the defining
function, and it does not reduce on a stuck discriminant. Rules are therefore stated for
`Option.elim`. The tactic `option_match_to_elim` rewrites every non-dependent two-way `match` on an
option in the goal, under binders and nested, to `Option.elim`, so that a definition written with
`match` needs no separate statement in terms of tests and defaults.

`Option.map` and `Option.any` unfold to such a `match`, so `unfold Option.map` reaches them.
`Option.bind` unfolds to a `match` on two discriminants, so the tactic rewrites `Option.bind`
itself. An alternative that takes a pattern apart, such as `some (a, b)`, is left unchanged, since
`Option.elim` has a single argument.
-/

public meta section

namespace Cslib.Tactic

open Lean Meta Elab Tactic

/-- Prove `lhs = rhs` by case analysis on the option `discr`. This runs inside `simp`, whose
reducible transparency would not unfold `Option.elim`. -/
private def eqByCases (lhs rhs discr : Expr) : MetaM Expr := withDefault do
  let goal ← mkFreshExprMVar (← mkEq lhs rhs)
  let (fvars, generalized) ← goal.mvarId!.generalize #[{ expr := discr }]
  for subgoal in ← generalized.cases fvars[0]! do
    subgoal.mvarId.refl
  instantiateMVars goal

/-- The `Option.elim` form of `Option.bind` or of a non-dependent two-way `match` on an option,
with its proof. The alternatives may come in either order. -/
private def optionMatch? (e : Expr) : MetaM (Option Simp.Result) := do
  if e.isAppOfArity ``Option.bind 4 then
    let #[_, β, discr, f] := e.getAppArgs | return none
    let rhs ← mkAppOptM ``Option.elim
      #[none, ← inferType e, discr, ← mkNone β, f]
    return some { expr := rhs, proof? := some (← eqByCases e rhs discr) }
  let some m ← matchMatcherApp? e | return none
  unless m.discrs.size == 1 && m.alts.size == 2 && m.remaining.isEmpty do return none
  let discr := m.discrs[0]!
  let .app (.const ``Option _) α ← whnfR (← inferType discr) | return none
  let dependent ← lambdaTelescope m.motive fun xs body =>
    return body.containsFVar xs[0]!.fvarId!
  if dependent then return none
  let β ← inferType e
  for (noneIdx, someIdx) in [(0, 1), (1, 0)] do
    let alt := m.alts[noneIdx]!
    let .forallE _ dom _ _ ← whnf (← inferType alt) | continue
    unless ← isDefEq dom (mkConst ``Unit) do continue
    try
      let rhs ← mkAppOptM ``Option.elim
        #[α, β, discr, alt.beta #[mkConst ``Unit.unit], m.alts[someIdx]!]
      return some { expr := rhs, proof? := some (← eqByCases e rhs discr) }
    catch _ => continue
  return none

/-- Rewrite every `Option.bind` and non-dependent two-way `match` on an option in the goal to
`Option.elim`. -/
syntax (name := optionMatchToElim) "option_match_to_elim" : tactic

@[inherit_doc optionMatchToElim]
elab_rules : tactic | `(tactic| option_match_to_elim) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let methods : Simp.Methods := {
      pre := fun e => do
        match ← optionMatch? e with
        | some r => return .visit r
        | none => return .continue }
    let (result, _) ← Simp.main target (← Simp.mkContext) (methods := methods)
    if result.expr == target then
      throwError "option_match_to_elim: no option match in the goal"
    replaceMainGoal [← applySimpResultToTarget goal target result]

end Cslib.Tactic
