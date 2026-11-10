
/- BEGIN FRONT PROBE (scratch instrumentation, not for commit) -/
section FrontProbe
open Lean Meta Elab Tactic

/-- Append one line to the probe log. -/
def FrontProbe.log (line : String) : IO Unit := do
  let some path ← IO.getEnv "FRONT_LOG" | return
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn line

def FrontProbe.hb : IO Nat := return (← IO.getNumHeartbeats) / 1000

/-- Match a local fact (or a family of facts) whose conclusion determines every argument. -/
def FrontProbe.localCert (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let saved ← saveState
    try
      let (xs, _, conclusion) ← forallMetaTelescopeReducing decl.type
      if ← withReducible (isDefEq conclusion target) then
        let args ← xs.mapM instantiateMVars
        unless args.any Expr.hasExprMVar do
          goal.assign (mkAppN decl.toExpr args)
          return true
    catch _ => pure ()
    saved.restore
  return false

def FrontProbe.effPred (target : Expr) : Option Name :=
  let t := target.consumeMData
  if t.isAppOf ``Turing.MultiTapeTM.ComputableInPolyTime then some ``Turing.MultiTapeTM.ComputableInPolyTime
  else if t.isAppOf ``Turing.MultiTapeTM.ComputableTidilyInPolyTime then
    some ``Turing.MultiTapeTM.ComputableTidilyInPolyTime
  else if t.isAppOf `Cslib.Probability.IsPPTOn then some `Cslib.Probability.IsPPTOn
  else none

mutual
/-- Deterministic front end: local fact, then named certificates (premises recursively by the
front end, no Aesop), then one `fun_prop` call with a small step budget. Returns the stage that
closed the goal, or throws naming the failure. -/
partial def FrontProbe.solve (fuel : Nat) (goal : MVarId) : TacticM String := goal.withContext do
  if fuel == 0 then throwError "front: depth exhausted"
  let target ← instantiateMVars (← goal.getType)
  if ← FrontProbe.localCert goal then return "local"
  let some pred := FrontProbe.effPred target
    | -- side condition: only reducible assumption / rfl
      let saved ← saveState
      try
        let gs ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic| first | with_reducible assumption | rfl | exact le_rfl | omega)))
        unless gs.isEmpty do throwError "front: side goal remains"
        return "side"
      catch _ =>
        saved.restore
        throwError "front: unsupported side goal {target}"
  -- (a) named certificates keyed on the goal head
  let key? ← try some <$> Cslib.Tactic.efficiencyKey target catch _ => pure none
  if let some key := key? then
    for (cert, _eager) in (Cslib.Tactic.certificateExt.getState (← getEnv)).getD key #[] do
      let saved ← saveState
      try
        let gs ← goal.applyConst cert
        for g in gs do
          unless ← g.isAssigned do
            discard <| FrontProbe.solve (fuel - 1) g
        if ← Aesop.hasSorry (mkMVar goal) then throwError "sorry"
        return "named"
      catch _ => saved.restore
  -- (b) one structural composition call with a small budget
  if pred == ``Turing.MultiTapeTM.ComputableTidilyInPolyTime then
    let gs ← Lean.Elab.Tactic.run goal
      (evalTactic (← `(tactic| solve | fun_prop (config := { maxSteps := 64 }))))
    unless gs.isEmpty do throwError "front: fun_prop left goals"
    return "funprop"
  let gs ← Lean.Elab.Tactic.run goal (Term.withoutErrToSorry <| withoutRecover <|
    Cslib.Tactic.PolyTime.Internal.funPropWithPlainBoundary 64)
  unless gs.isEmpty do throwError "front: fun_prop left goals"
  return "funprop"
end

def FrontProbe.firstLine (s : String) : String :=
  (((s.splitOn "\n").take 3 |> String.intercalate " | ").take 300).toString

def FrontProbe.esc (s : String) : String :=
  s.foldl (fun acc c => if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ " " else acc.push c) ""

def FrontProbe.front (hints : Array Ident) (pptMode : Bool) : TacticM String := do
  withMainContext do Cslib.Tactic.PolyTime.Internal.prepareGoal hints
  if pptMode then
    liftMetaTactic1 fun g => do
      let t ← instantiateMVars (← g.getType)
      let t' ← deltaExpand t (fun n => n == `Cslib.Probability.IsPPT)
      g.replaceTargetDefEq t'
  let g ← getMainGoal
  if (← instantiateMVars (← g.getType)).consumeMData.isAppOf `Cslib.Probability.IsOraclePPTOn then
    throwError "front: oracle goal (today's path is already fun_prop)"
  if ← FrontProbe.localCert g then return "local0"
  let r ← IO.mkRef ""
  Cslib.Tactic.PolyTime.Internal.withPlainRuleCache do r.set (← FrontProbe.solve 8 g)
  r.get

def FrontProbe.run (which : String) (orig : Tactic) (pptMode : Bool) : Tactic := fun stx => do
  let pos := (← getFileMap).toPosition (stx.getPos?.getD 0)
  let file ← getFileName
  let initial ← saveState
  let target ← instantiateMVars (← getMainTarget)
  let headStr := toString (target.consumeMData.getAppFn.constName?.getD `none)
  -- component costs (each from the same initial state)
  let h0 ← FrontProbe.hb
  try withCurrHeartbeats <| Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo (pure ()) catch _ => pure ()
  let h1 ← FrontProbe.hb
  initial.restore
  try withCurrHeartbeats <| Cslib.Tactic.PolyTime.Internal.withPlainRuleCache (pure ()) catch _ => pure ()
  let h2 ← FrontProbe.hb
  initial.restore
  -- front end
  let hints := if stx[1].getNumArgs == 3 then stx[1][1].getSepArgs.map (⟨·⟩ : Syntax → Ident)
    else #[]
  let fr ← IO.mkRef (Except.error "unset" : Except String String)
  let hw ← IO.mkRef (0 : Nat)
  let tw ← IO.mkRef (0 : Nat)
  let twok ← IO.mkRef false
  try withCurrHeartbeats <| Cslib.Tactic.PolyTime.Internal.withPlainRuleMemo do
      let inner ← saveState
      let a ← FrontProbe.hb
      let res ← tryCatchRuntimeEx (do pure (Except.ok (← withCurrHeartbeats <| FrontProbe.front hints pptMode)))
        (fun e => do pure (Except.error ((if e.isRuntime then "RUNTIME " else "") ++ (← e.toMessageData.toString))))
      let b ← FrontProbe.hb
      fr.set res; hw.set (b - a)
      inner.restore
      let a ← FrontProbe.hb
      tryCatchRuntimeEx (do withCurrHeartbeats (orig stx); twok.set true) (fun _ => pure ())
      let b ← FrontProbe.hb
      tw.set (b - a)
  catch _ => pure ()
  initial.restore
  let frontRes ← fr.get
  let h3 := 0
  let h4 ← hw.get
  -- today's tactic, committed
  let h5 ← FrontProbe.hb
  let todayRes ← try withCurrHeartbeats (orig stx); pure (Except.ok ()) catch e => pure (Except.error e)
  let h6 ← FrontProbe.hb
  let (fOk, fMsg) := match frontRes with | .ok s => (true, s) | .error m => (false, m)
  let tOk := match todayRes with | .ok _ => true | .error _ => false
  FrontProbe.log s!"\{\"file\":\"{file}\",\"line\":{pos.line},\"tac\":\"{which}\",\"head\":\"{headStr}\",\"memo\":{h1-h0},\"cache\":{h2-h1},\"front_ok\":{fOk},\"front\":\"{FrontProbe.esc (FrontProbe.firstLine fMsg)}\",\"front_hb\":{h4-h3},\"today_ok\":{tOk},\"today_hb\":{h6-h5},\"today_warm_hb\":{← tw.get},\"today_warm_ok\":{← twok.get}}"
  match todayRes with
  | .ok _ => pure ()
  | .error e => throw e

@[tactic Cslib.Tactic.PolyTime.polytimeTactic] def FrontProbe.polytime : Tactic :=
  FrontProbe.run "polytime" Cslib.Tactic.PolyTime.evalPolytime false

-- PPT BEGIN
@[tactic Cslib.Tactic.PPT.pptTactic] def FrontProbe.ppt : Tactic :=
  FrontProbe.run "ppt" Cslib.Tactic.PPT.evalPPT true
-- PPT END

end FrontProbe
/- END FRONT PROBE -/
