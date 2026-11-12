/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse
import CslibFrontier.Foundations.Geometry.Polygonal.NoncrossingOrder
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-!
Stored-declaration audit of every new library module in the finite polygonal converse.
Private/generated declarations are included. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. Environment linters and public `Cslib.Init` reachability
are checked on the same complete module list. Imported dependencies and executable
regression-test scaffolding are outside this scoped audit.
-/

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  let targets : List Name :=
    [`CslibFrontier.Foundations.Geometry.Polygonal.AngleOrder,
     `CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitFan,
     `CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitOrder,
     `CslibFrontier.Foundations.Geometry.Polygonal.NoncrossingOrder,
     `CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior,
     `CslibFrontier.Foundations.Geometry.Polygonal.RayOrder,
     `CslibFrontier.Foundations.Geometry.Polygonal.RayParityTransport,
     `CslibFrontier.Foundations.Geometry.Polygonal.RayParityGerms,
     `CslibFrontier.Foundations.Geometry.Polygonal.RayParityColors,
     `CslibFrontier.Foundations.Geometry.Polygonal.SegmentRays,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SegmentArrangement,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.FaceColors,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Sectors,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut decls : Array Name := #[]
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if targets.contains moduleName then
      modules := modules + 1
      unless data.constNames.size == data.constants.size do
        throwError "polygonal converse audit: malformed declaration table for {moduleName}"
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "polygonal converse audit: missing stored declaration {name}"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "polygonal converse audit: {name} depends on {disallowed}"
        decls := decls.push name
  unless modules == targets.length && !decls.isEmpty do
    throwError "polygonal converse audit: missing owned modules or declarations"
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
      throwError "polygonal converse audit: {name} does not publicly import Cslib.Init"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls checks
  for (linter, failures) in results do
    for (name, message) in failures.toList do
      throwError "polygonal converse audit: {linter.name}: {name}: {message}"
