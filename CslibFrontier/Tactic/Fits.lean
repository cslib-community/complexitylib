/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Defs
public meta import Lean.Elab.Tactic.Omega

/-!
# Closing word-size bounds

`Cslib.WordRAM.Fits w v` states `v < 2 ^ w`, and word-RAM proofs need many such side conditions,
one per value an instruction writes. `fits` proves them by linear arithmetic: it unfolds `Fits` in
the goal and in every hypothesis that mentions it, then runs `omega`. The hypotheses are found by
their statements, not by their names, so a bound follows from whichever word-size facts are in
context, without first choosing the fact to weaken with `Fits.of_le`.

Only hypotheses whose statements contain `Fits` are unfolded: they are added to the context in
unfolded form, and the others are left to `omega` as they are. Each power of two `2 ^ e` among
them is added as positive, which `omega` does not know by itself. `fits [h₁, h₂]` also adds the
statements of the given terms, such as a product bound that `omega` cannot derive.

The tactic fails on a goal that is not a word-size bound, naming the plain `omega` that is then the
right call, and when `omega` cannot close the unfolded goal, showing that goal and saying whether
any hypothesis `Fits w v` was found.

## Main definitions

* `fits`: prove `Fits w v`, or `v < 2 ^ w`, by `omega` from the word-size facts in context.
-/

public meta section

namespace Cslib.Tactic.Fits

open Lean Meta Elab Tactic

/-- `e` with `Cslib.WordRAM.Fits` unfolded everywhere. -/
private def unfoldFits (e : Expr) : CoreM Expr :=
  deltaExpand e (· == ``Cslib.WordRAM.Fits)

/-- Whether `e` mentions `Cslib.WordRAM.Fits`. -/
private def mentionsFits (e : Expr) : Bool :=
  (e.find? (·.isConstOf ``Cslib.WordRAM.Fits)).isSome

/-- Whether `e` is a power of two `2 ^ k` on natural numbers. -/
private def isPowerOfTwo (e : Expr) : Bool :=
  match_expr e with
  | HPow.hPow α β _ _ b _ => α.isConstOf ``Nat && β.isConstOf ``Nat && b.nat? == some 2
  | _ => false

/-- Whether `e` is a word-size bound: it mentions `Fits`, or it is `v < 2 ^ k`. -/
private def isWordBound (e : Expr) : Bool :=
  mentionsFits e || match_expr e with
    | LT.lt _ _ _ b => isPowerOfTwo b
    | _ => false

/-- The hypotheses whose statements mention `Fits`, with `Fits` unfolded in their statements. -/
private def fitsHypotheses : MetaM (Array Hypothesis) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let type ← instantiateMVars d.type
    unless mentionsFits type do return acc
    unless ← isProp type do return acc
    return acc.push { userName := d.userName, type := ← unfoldFits type, value := d.toExpr }

/-- The facts `0 < 2 ^ e` for the powers of two in `es`. `omega` reads `2 ^ e` as an atom without
knowing that it is positive, which a bound such as `Fits w (2 ^ e - 1)` needs. -/
private def powerFacts (es : Array Expr) : MetaM (Array Hypothesis) := do
  let powers ← IO.mkRef (#[] : Array Expr)
  for e in es do
    forEachExpr e fun t => do
      if isPowerOfTwo t && !(← powers.get).contains t then powers.modify (·.push t)
  (← powers.get).filterMapM fun t => do
    let_expr HPow.hPow _ _ _ _ _ k := t | return none
    let type ← mkAppM ``LT.lt #[mkNatLit 0, t]
    let value := mkApp (mkConst ``Nat.two_pow_pos) k
    unless ← isDefEq type (← inferType value) do return none
    return some { userName := `this, type, value }

/-- `fits` proves a word-size bound `Fits w v`, or `v < 2 ^ w`, by linear arithmetic. It unfolds
`Fits` in the goal and in each hypothesis that mentions it, and runs `omega`; hypotheses are found
by their statements, whatever their names.

* `fits [h₁, h₂]` also uses the statements of the terms `h₁` and `h₂`, unfolded likewise, for
  facts `omega` cannot derive, such as bounds on products.

It fails on a goal that is not a word-size bound, for which plain `omega` is the right call. -/
syntax (name := fits) "fits" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| fits $[[$terms,*]]?) => focus <| withMainContext do
    let g ← getMainGoal
    let target ← instantiateMVars (← g.getType)
    unless isWordBound target.cleanupAnnotations do
      throwError "fits: the goal is not a word-size bound `Fits w v` or `v < 2 ^ w`; use \
        `omega` for other arithmetic.{indentExpr target}"
    let mut facts ← fitsHypotheses
    let found := facts.size
    for t in (terms.map (·.getElems)).getD #[] do
      let e ← elabTerm t none
      let type ← unfoldFits (← instantiateMVars (← inferType e))
      facts := facts.push { userName := `this, type, value := e }
    let target ← unfoldFits target
    facts := facts ++ (← powerFacts (facts.map (·.type) |>.push target))
    let g ← g.replaceTargetDefEq target
    let (_, g) ← g.assertHypotheses facts
    replaceMainGoal [g]
    try
      evalTactic (← `(tactic| omega))
    catch ex =>
      let found := if found == 0 then m!"There is no hypothesis `Fits w v` in context."
        else m!"Hypotheses that mention `Fits`: {found}."
      throwError "fits: `omega` could not prove the bound. {found} Products are atoms, so give \
        bounds on them with `fits [h]`.\n{g}\n{ex.toMessageData}"

end Cslib.Tactic.Fits

end
