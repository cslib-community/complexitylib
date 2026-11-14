/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Chris Henson, Samuel Schlesinger
-/

module

public import Lean.Setup
import Lean

/-!
# Check Init Imports

This script checks that all `CslibFrontier` modules (transitively) publicly import `Cslib.Init`,
exactly as cslib's own `CheckInitImports` requires of `Cslib` modules. Every module here is an
upstream candidate, so it must satisfy cslib's invariant already.
-/

public section

open Lean

/-- Modules with technical constraints preventing a `Cslib.Init` import. -/
def exceptions : List Name := []

/-- Find modules without a public-import path to `Cslib.Init`.

Walk backwards from the one required module instead of constructing the transitive closure
for every module. The visited set also makes the traversal independent of input order.
-/
def missingInitImports (modules : Array (Name × Array Import))
    (except : List Name := exceptions) : List Name := Id.run do
  let mut importers : NameMap (Array Name) := {}
  let mut names : NameSet := {}
  for (name, imports) in modules do
    names := names.insert name
    for imp in imports do
      if imp.isExported then
        names := names.insert imp.module
        importers := importers.insert imp.module <|
          ((importers.find? imp.module).getD #[]).push name
  let mut visited : NameSet := {}
  let mut pending := #[`Cslib.Init]
  while let some name := pending.back? do
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      pending := pending ++ (importers.find? name).getD #[]
  return names.toList.filter fun name =>
    name.getRoot == `CslibFrontier && name != `CslibFrontier &&
      !visited.contains name && !except.contains name

unsafe def main : IO UInt32 := do
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  searchPathRef.set searchPath
  withImportModules #[{ module := `CslibFrontier }] {} (trustLevel := 1024) fun env => do
    let modules := env.header.moduleNames.zip env.header.moduleData
      |>.map fun (name, data) => (name, data.imports)
    let diff := missingInitImports modules
    if diff.length > 0 then
      IO.eprintln s!"error: the following modules do not publicly import `Cslib.Init`: {diff}"
    return diff.length.toUInt32
