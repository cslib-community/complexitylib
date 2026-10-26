/- Diagnostic-only #1155 instrumentation. No production dependency or proof provider. -/
module
public meta import Lean.Elab.Tactic.Basic
public import Lean.Util.Heartbeats
public import Lean.Data.Json

open Lean Elab Tactic
namespace Diag1155.Current

private meta def emit (fields : List (String × Json)) : IO Unit := do
  let some path ← IO.getEnv "DIAG1155_OUTPUT" | throw (IO.userError "missing output")
  IO.FS.withFile path .append fun h => h.putStrLn (Json.mkObj fields).compress

/-- Diagnostic dispatch only: require one original elaborator and no macro alternatives.
Unsupported dispatch falls through unchanged and remains explicitly unmeasured. -/
meta def measure (stx : Syntax) : TacticM Unit := do
  let enterHb ← IO.getNumHeartbeats
  let enterNs ← IO.monoNanosNow
  let env ← getEnv
  let originals := (tacticElabAttribute.getEntries env stx.getKind).filter fun entry =>
    !(`Diag1155.Current).isPrefixOf entry.declName
  let macros := macroAttribute.getEntries env stx.getKind
  unless originals.length == 1 && macros.isEmpty do
    emit [("phase", toJson "unsupported_dispatch"),
      ("kind", toJson stx.getKind.toString), ("original_count", toJson originals.length),
      ("macro_count", toJson macros.length)]
    throwUnsupportedSyntax
  let original := originals.head!
  let some run ← IO.getEnv "DIAG1155_RUN_ID" | throwError "missing run"
  let some provenance ← IO.getEnv "DIAG1155_PROVENANCE" | throwError "missing provenance"
  let tid ← IO.getTID
  let event := s!"{run}:{tid}:{enterNs}"
  let opts ← getOptions
  let fm ← getFileMap
  let beginPos := stx.getPos?
  let endPos := stx.getTailPos?
  let text := match beginPos, endPos with
    | some b, some e => String.Pos.Raw.extract fm.source b e
    | _, _ => ""
  let originalSource := match stx.getHeadInfo with
    | .original .. => true
    | _ => false
  let decl ← Term.getDeclName?
  emit [("phase", toJson "begin"), ("event_id", toJson event), ("run_id", toJson run),
    ("provenance", toJson provenance), ("thread_id", toJson tid.toNat),
    ("file", toJson (← getFileName)), ("module", toJson env.mainModule.toString),
    ("declaration", toJson (decl.map Name.toString)), ("kind", toJson stx.getKind.toString),
    ("start", toJson (beginPos.map (·.byteIdx))), ("end", toJson (endPos.map (·.byteIdx))),
    ("text", toJson text), ("original_source_info", toJson originalSource),
    ("macro_stack_depth", toJson (← readThe Term.Context).macroStack.length),
    ("original_handler", toJson original.declName.toString),
    ("maxHeartbeats_user", toJson (maxHeartbeats.get opts)),
    ("maxRecDepth", toJson (maxRecDepth.get opts)),
    ("async_option", toJson (Lean.Elab.async.get opts)),
    ("options_repr", toJson (reprStr opts)), ("goals_before", toJson (← getGoals).length)]
  let hb0 ← IO.getNumHeartbeats
  let ns0 ← IO.monoNanosNow
  let trace0 := (← getTraceState).traces.size
  -- Use the supported NON-backtracking catcher: external first/fail_if_success keeps
  -- responsibility for restoration, exactly as with the original elaborator.
  let result ← Tactic.tryCatch
    (do
      Term.withoutTacticIncrementality (!(← isIncrementalElab original.declName)) do
        withReader ({ · with elaborator := original.declName }) do
          withTacticInfoContext stx do
            original.value stx
            if !original.isBuiltin then
              recordExtraModUseFromDecl (isMeta := true) original.declName
      pure (Except.ok ()))
    (fun ex => pure (Except.error ex))
  let ns1 ← IO.monoNanosNow
  let hb1 ← IO.getNumHeartbeats
  let traces := (← getTraceState).traces.toArray
  -- No trace option is enabled here. A separate diagnostic run controls tracing.
  for trace in traces[trace0:] do
    emit [("phase", toJson "trace"), ("event_id", toJson event),
      ("message", toJson (← trace.msg.toString)),
      ("start", toJson (trace.ref.getPos?.map (·.byteIdx))),
      ("end", toJson (trace.ref.getTailPos?.map (·.byteIdx)))]
  let status := match result with
    | .ok _ => "returned"
    | .error ex => if ex.isMaxHeartbeat then "heartbeat_exception"
      else if ex.isMaxRecDepth then "recursion_exception"
      else if ex.isInterrupt then "interrupt_exception" else "exception"
  let remaining ← match result with
    | .ok _ => pure (some (← getUnsolvedGoals).length)
    | .error _ => pure none
  emit [("phase", toJson "end"), ("event_id", toJson event), ("run_id", toJson run),
    ("provenance", toJson provenance), ("thread_id", toJson tid.toNat),
    ("status", toJson status), ("goals_after", toJson remaining),
    ("raw_body_thread_heartbeats", toJson (hb1 - hb0)),
    ("raw_region_thread_heartbeats", toJson (hb1 - enterHb)),
    ("body_wall_nanoseconds", toJson (ns1 - ns0)),
    ("trace_entries", toJson (traces.size - trace0))]
  match result with
  | .ok _ => pure ()
  | .error ex => throw ex
end Diag1155.Current
