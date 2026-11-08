/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Defs
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

The simplification procedure `Cslib.WordRAM.reduceFits` rewrites `Fits w v` to `True` when `omega`
proves it from the hypotheses that mention `Fits` alone, so that a `simp` call deciding whether
written values fit a word, as in `ram_eval`, needs no named `Fits` facts. It leaves the other
hypotheses out to keep its cost independent of the length of the context.

## Main definitions

* `fits`: prove `Fits w v`, or `v < 2 ^ w`, by `omega` from the word-size facts in context.
* `Cslib.WordRAM.reduceFits`: the same proof, from the `Fits` hypotheses, as a `simp` procedure.
-/

public meta section

namespace Cslib.Tactic.Fits

open Lean Meta Elab Tactic

/-- `e` with `Cslib.WordRAM.Fits` unfolded everywhere. -/
def unfoldFits (e : Expr) : CoreM Expr :=
  deltaExpand e (· == ``Cslib.WordRAM.Fits)

/-- Whether `e` mentions `Cslib.WordRAM.Fits`. -/
def mentionsFits (e : Expr) : Bool :=
  (e.find? (·.isConstOf ``Cslib.WordRAM.Fits)).isSome

/-- Whether `e` is a power of two `2 ^ k` on natural numbers. -/
def isPowerOfTwo (e : Expr) : Bool :=
  match_expr e with
  | HPow.hPow α β _ _ b _ => α.isConstOf ``Nat && β.isConstOf ``Nat && b.nat? == some 2
  | _ => false

/-- Whether `e` is a word-size bound: it mentions `Fits`, or it is `v < 2 ^ k`. -/
def isWordBound (e : Expr) : Bool :=
  mentionsFits e || match_expr e with
    | LT.lt _ _ _ b => isPowerOfTwo b
    | _ => false

/-- The hypotheses whose statements mention `Fits`, with `Fits` unfolded in their statements. -/
def fitsHypotheses : MetaM (Array Hypothesis) := do
  (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let type ← instantiateMVars d.type
    unless mentionsFits type do return acc
    unless ← isProp type do return acc
    return acc.push { userName := d.userName, type := ← unfoldFits type, value := d.toExpr }

/-- The facts `0 < 2 ^ e` for the powers of two in `es`. `omega` reads `2 ^ e` as an atom without
knowing that it is positive, which a bound such as `Fits w (2 ^ e - 1)` needs. -/
def powerFacts (es : Array Expr) : MetaM (Array Hypothesis) := do
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

/-- The most hypotheses that mention `Fits` for which `prove?` tries `omega`. Beyond it, as in
proofs that state one generated fact per written value, `prove?` only looks for a hypothesis of the
same statement: `omega` over many large facts, once per value written, would cost more than the
statements save. -/
def maxFacts : ℕ := 16

/-- The heartbeats `prove?` may spend on one bound, in thousands, as for `maxHeartbeats`: a bound
that `omega` does not settle quickly, for instance through case splits on divisions, is left to
the given simp lemmas rather than slowing every evaluation, which may try hundreds of bounds. -/
def maxHeartbeats : ℕ := 200

/-- A proof of the word-size bound `target` by `omega` from the hypotheses that mention `Fits`,
unfolded, or `none`. Unlike `fits` it uses no other hypotheses and adds no positivity facts, so
that its cost does not grow with a long context; it runs inside `simp` (`reduceFits`), possibly
on every value a program writes. -/
def prove? (target : Expr) : MetaM (Option Expr) := do
  let target ← instantiateMVars target
  unless isWordBound target.cleanupAnnotations do return none
  let target' := target.cleanupAnnotations
  let exact? ← (← getLCtx).findDeclRevM? fun d => do
    if d.isImplementationDetail then return none
    return if (← instantiateMVars d.type).cleanupAnnotations == target' then some d.toExpr else none
  if exact?.isSome then return exact?
  let count ← (← getLCtx).foldlM (init := 0) fun n d =>
    return if !d.isImplementationDetail && mentionsFits d.type then n + 1 else n
  if count == 0 || count > maxFacts then return none
  let facts ← fitsHypotheses
  let saved ← saveState
  let budget (x : MetaM (Option Expr)) : MetaM (Option Expr) :=
    withCurrHeartbeats <| withTheReader Core.Context
      (fun ctx => { ctx with maxHeartbeats := maxHeartbeats * 1000 }) x
  let attempt : MetaM (Option Expr) := do
    let unfolded ← unfoldFits target
    let proofs ← facts.mapM fun h => mkExpectedTypeHint h.value h.type
    let g ← mkFreshExprSyntheticOpaqueMVar unfolded
    let some g' ← g.mvarId!.falseOrByContra | throwError "fits: no goal"
    g'.withContext do
      let some neg := (← getLCtx).lastDecl | throwError "fits: no negated goal"
      Lean.Elab.Tactic.Omega.omega (neg.toExpr :: proofs.toList) g'
    return some (← mkExpectedTypeHint (← instantiateMVars g) target)
  tryCatchRuntimeEx (budget attempt) fun _ => do
    saved.restore
    return none

/-- Rewrite a word-size bound `Fits w v` to `True` when `prove?` proves it. -/
def reduceFitsStep : Simp.Simproc := fun e => do
  unless e.isAppOfArity ``Cslib.WordRAM.Fits 2 do return .continue
  let some h ← prove? e | return .continue
  return .done { expr := mkConst ``True, proof? := some (← mkEqTrue h) }

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

public section

namespace Cslib.WordRAM

/-- `simp` procedure that rewrites a word-size bound `Fits w v` to `True` when `omega` proves it
from the hypotheses `Fits w' v'` in context. `ram_eval` and `ram_exact_eval` use it to decide
which written values fit a word. -/
simproc_decl reduceFits (Fits _ _) := Cslib.Tactic.Fits.reduceFitsStep

end Cslib.WordRAM

end
