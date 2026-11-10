/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Tactic.Realize

/-!
# Absorbed loop rules and `realize` tactic extension for `RealizesBounded`

Absorbed `iterate₀` and `while₀` rules for `Cslib.WordRAM.Realization.RealizesBounded`, together
with an `elab_rules` extension allowing `by realize` to synthesize `RealizesBounded` certificates
directly without modifying `CslibFrontier.Tactic.Realize` or affecting ordinary `Realizes` goals.

## Main results

* `Cslib.WordRAM.Realization.RealizesBounded.iterate₀`,
  `Cslib.WordRAM.Realization.RealizesBounded.while₀`: absorbed frontier-bounded iteration and
  `boundedWhile` certificates when each step issues at least one memory query.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.RealizesBounded

open Cslib.DataStructure

/-- Absorbed frontier-bounded `iterate₀` rule when every body issues at least one memory query. -/
theorem iterate₀ {δ : Type} {k l : ℕ} {σ : Type}
    (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → (δ × σ) → Memory.State → Prop}
    (h : RealizesBounded .exact body
      ((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding)
      output safe (fun _ _ => 0))
    (hquery : ∀ x s, 1 ≤ memoryCost (body x) s) :
    RealizesBounded .exact (fun d : (δ × σ) × ℕ => iterate body d.1.1 d.2 d.1.2)
      ((((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w d s => iterationSafe body safe w d.1.1 d.2 d.1.2 s) (fun _ _ => 0) :=
  (iterateRuntime input output h).mono_mul 1 fun ((d, a), fuel) s => by
    have := iterationWork_zero_le body hquery d fuel a s
    dsimp only
    omega

/-- Absorbed frontier-bounded `while₀` rule when every body issues at least one memory query. -/
theorem while₀ {δ σ : Type} {B : Basis} {k l : ℕ}
    (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ)) (cond : Cond (k + l))
    (cutoff : δ × σ → ℕ) {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    (h : RealizesBounded B body (appendWords input output) output safe (fun _ _ => 0))
    (hquery : ∀ x s, 1 ≤ memoryCost (body x) s) :
    RealizesBounded B (fun (d, a) => boundedWhile
      (fun d a => test cond ((appendWords input output) (d, a))) body d (cutoff (d, a)) a)
      (appendWords input output) output
      (fun w (d, a) s => whileSafe
        (fun d a => test cond ((appendWords input output) (d, a))) body safe w d
        (cutoff (d, a)) a s)
      (fun _ _ => 0) :=
  (whileBounded input output cond cutoff h).mono_mul 1 fun (d, a) s => by
    have := whileWork_zero_le (fun d a => test cond ((appendWords input output) (d, a))) body
      hquery d (cutoff (d, a)) a s
    dsimp only
    omega

end Cslib.WordRAM.Realization.RealizesBounded

public meta section

namespace Cslib.WordRAM

open Lean Meta Elab Tactic Cslib.WordRAM.Realization in
/-- Map a `Realizes` proof-combinator constant to its `RealizesBounded` counterpart. -/
def mapRealizesConst (c : Name) : Option Name :=
  [(``Realizes.consequence, ``RealizesBounded.consequence),
   (``Realizes.consequence_valid, ``RealizesBounded.consequence_valid),
   (``Realizes.congr, ``RealizesBounded.congr), (``Realizes.reindex, ``RealizesBounded.reindex),
   (``Realizes.mono_mul, ``RealizesBounded.mono_mul), (``Realizes.pure₀, ``RealizesBounded.pure₀),
   (``Realizes.bind₀_of_run, ``RealizesBounded.bind₀_of_run),
   (``Realizes.read, ``RealizesBounded.read), (``Realizes.write, ``RealizesBounded.write),
   (``Realizes.alloc, ``RealizesBounded.alloc),
   (``Realizes.allocDirty, ``RealizesBounded.allocDirty),
   (``Realizes.branch₀, ``RealizesBounded.branch₀),
   (``Realizes.iterate₀, ``RealizesBounded.iterate₀),
   (``Realizes.while₀, ``RealizesBounded.while₀)].lookup c

open Lean Meta Elab Tactic Cslib.WordRAM.Realization in
/-- Translate the `Realizes` proof spine to `RealizesBounded` without touching client terms. -/
partial def translateRealizesProof (shadowMap : Std.HashMap FVarId FVarId) (e : Expr) :
    Expr :=
  let toBounded (t : Expr) : Expr := mkAppN (.const ``RealizesBounded []) t.getAppArgs
  match e with
  | .fvar fid => shadowMap[fid]?.map .fvar |>.getD e
  | .lam n t b bi => .lam n t (translateRealizesProof shadowMap b) bi
  | .mdata md b => .mdata md (translateRealizesProof shadowMap b)
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``id && args.size == 2 && args[0]!.isAppOfArity ``Realizes 10 then
      mkApp2 fn (toBounded args[0]!) (translateRealizesProof shadowMap args[1]!)
    else if fn.isConstOf ``Eq.mp && args.size == 4 && args[0]!.isAppOfArity ``Realizes 10 &&
        args[1]!.isAppOfArity ``Realizes 10 then
      let hEq := if args[2]!.isAppOfArity ``congrArg 6 then
        let cArgs := args[2]!.getAppArgs
        match cArgs[4]! with
        | .lam nm sTy body bi =>
          if body.isAppOfArity ``Realizes 10 then
            mkAppN args[2]!.getAppFn (cArgs.set! 4 (.lam nm sTy (toBounded body) bi))
          else args[2]!
        | _ => args[2]!
      else args[2]!
      mkApp4 fn (toBounded args[0]!) (toBounded args[1]!) hEq
        (translateRealizesProof shadowMap args[3]!)
    else match fn with
      | .const c us =>
        match mapRealizesConst c with
        | some c' => mkAppN (.const c' us) (args.map (translateRealizesProof shadowMap))
        | none => e
      | _ => e
  | _ => e

open Lean Meta Elab Tactic Cslib.WordRAM.Realization in
/-- Extend `realize` to `RealizesBounded` goals without editing
`CslibFrontier/Tactic/Realize.lean`. -/
elab_rules : tactic | `(tactic| realize) => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← whnfR (← goal.getType))
  unless target.isAppOfArity ``RealizesBounded 10 do
    throwUnsupportedSyntax
  let args := target.getAppArgs
  let mut shadowMap : Std.HashMap FVarId FVarId := {}
  let mut shadowIds : Array FVarId := #[]
  let mut rawRealizesIds : Array FVarId := #[]
  let mut gWork := goal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars (← whnfR decl.type)
    if ty.isAppOfArity ``Realizes 10 then
      rawRealizesIds := rawRealizesIds.push decl.fvarId
    else if ty.isAppOfArity ``RealizesBounded 10 then
      let val ← mkAppM ``RealizesBounded.toRealizes #[decl.toExpr]
      gWork ← gWork.assert (decl.userName.appendAfter "_realizes") (← inferType val) val
      let (fid, gNext) ← gWork.intro1P
      gWork := gNext
      shadowMap := shadowMap.insert fid decl.fvarId
      shadowIds := shadowIds.push fid
  gWork.withContext do
    let mAux ← mkFreshExprMVar (mkAppN (mkConst ``Realizes []) args)
    let mut mGoal := mAux.mvarId!
    for rId in rawRealizesIds.reverse do
      mGoal ← try mGoal.clear rId catch _ => pure mGoal
    setGoals [mGoal]
    evalTactic (← `(tactic| realize))
    let mut cleanGoals : Array MVarId := #[]
    for rg in (← getGoals) do
      let mut cg := rg
      for sfid in shadowIds.reverse do
        cg ← try cg.clear sfid catch _ => pure cg
      cleanGoals := cleanGoals.push cg
    let prfBounded := translateRealizesProof shadowMap (← instantiateMVars mAux)
    check prfBounded
    unless ← isDefEq (← inferType prfBounded) target do
      throwError "realize: translated proof does not match RealizesBounded goal"
    gWork.assign prfBounded
    setGoals cleanGoals.toList

end Cslib.WordRAM
