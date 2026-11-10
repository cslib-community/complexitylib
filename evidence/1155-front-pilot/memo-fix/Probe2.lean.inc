
/- BEGIN FRONT PROBE (scratch instrumentation, not for commit) -/
section FrontProbe
open Lean Meta Elab Tactic

def FrontProbe.log (line : String) : IO Unit := do
  let some path ← IO.getEnv "FRONT_LOG" | return
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn line

def FrontProbe.run (which : String) (orig : Tactic) : Tactic := fun stx => do
  let pos := (← getFileMap).toPosition (stx.getPos?.getD 0)
  let file ← getFileName
  let a ← IO.getNumHeartbeats
  let res ← tryCatchRuntimeEx (do orig stx; pure (Except.ok ())) (fun e => pure (Except.error e))
  let b ← IO.getNumHeartbeats
  let ok := match res with | .ok _ => true | .error _ => false
  FrontProbe.log s!"\{\"file\":\"{file}\",\"line\":{pos.line},\"col\":{pos.column},\"tac\":\"{which}\",\"ok\":{ok},\"hb\":{(b - a) / 1000}}"
  match res with
  | .ok _ => pure ()
  | .error e => throw e

@[tactic Cslib.Tactic.PolyTime.polytimeTactic] def FrontProbe.polytime : Tactic :=
  FrontProbe.run "polytime" Cslib.Tactic.PolyTime.evalPolytime

-- PPT BEGIN
@[tactic Cslib.Tactic.PPT.pptTactic] def FrontProbe.ppt : Tactic :=
  FrontProbe.run "ppt" Cslib.Tactic.PPT.evalPPT
-- PPT END

end FrontProbe
/- END FRONT PROBE -/
