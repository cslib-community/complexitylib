/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Chris Henson, Samuel Schlesinger
-/

module

import Lean
import Mathlib.Lean.CoreM
import Batteries.Data.List.Basic
import ImportGraph

/-!
# Check Init Imports

This script checks that all `CslibFrontier` modules (transitively) publicly import `Cslib.Init`,
exactly as cslib's own `CheckInitImports` requires of `Cslib` modules. Every module here is an
upstream candidate, so it must satisfy cslib's invariant already.
-/

public section

open Lean Core Elab Command

/-- Modules with technical constraints preventing a `Cslib.Init` import. -/
def exceptions : List Name := []

def main : IO UInt32 := do
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  CoreM.withImportModules #[`CslibFrontier] (searchPath := searchPath) (trustLevel := 1024) do
    let env ← getEnv
    let mut publicImports : NameMap (Array Name) := {}
    for name in env.header.moduleNames, data in env.header.moduleData do
      publicImports := publicImports.insert name <|
        data.imports.filter (·.isExported) |>.map (·.module)
    let graph := publicImports.transitiveClosure
    let noInitGraph :=
      graph.filter (fun name imports =>
        name.getRoot = `CslibFrontier ∧ name ≠ `CslibFrontier ∧ !imports.contains `Cslib.Init)
    let diff := noInitGraph.keys.diff exceptions
    if diff.length > 0 then
      IO.eprintln s!"error: the following modules do not publicly import `Cslib.Init`: {diff}"
    return diff.length.toUInt32
