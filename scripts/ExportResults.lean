/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: local-only (result registry export tooling)
import CslibFrontierResults.Registry

/-! Export records stored by the compiled canonical Lean registry. -/

open Lean CslibFrontierResults

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `CslibFrontierResults }] {} (loadExts := true)
  let records := entries.getState env
  IO.println (Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("results", Json.arr (records.map Entry.json))]).compress
