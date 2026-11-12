/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Foundations.Geometry.Polygonal.Join
import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitFan
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitOrder
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-!
Scoped standard-three-axiom and environment-linter audit of all stored declarations in the
route join, restriction and local fan modules, including private and generated declarations.
This does not replace independent mathematical review or claim the full
geometric/numerical equivalence.
-/

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  let targets : List Name :=
    [`CslibFrontier.Foundations.Geometry.Polygonal.Join,
     `CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitFan,
     `CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitOrder,
     `CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitRestriction,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Restriction,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitOrder]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut decls : Array Name := #[]
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if targets.contains moduleName then
      modules := modules + 1
      unless data.constNames.size == data.constants.size do
        throwError "polygonal restoration audit: malformed declaration table for {moduleName}"
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "polygonal restoration audit: missing stored declaration {name}"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "polygonal restoration audit: {name} depends on {disallowed}"
        decls := decls.push name
  unless modules == targets.length && !decls.isEmpty do
    throwError "polygonal restoration audit: missing owned modules or declarations"
  let mut initImporters : NameSet := ({} : NameSet).insert `Cslib.Init
  let mut changed := true
  while changed do
    changed := false
    for name in env.header.moduleNames, data in env.header.moduleData do
      if !initImporters.contains name &&
          data.imports.any (fun i => i.isExported && initImporters.contains i.module) then
        initImporters := initImporters.insert name
        changed := true
  for name in targets do
    unless initImporters.contains name do
      throwError "polygonal restoration audit: {name} does not publicly import Cslib.Init"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls checks
  for (linter, failures) in results do
    for (name, message) in failures.toList do
      throwError "polygonal restoration audit: {linter.name}: {name}: {message}"
