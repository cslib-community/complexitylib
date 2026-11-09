/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-!
Scoped standard-three-axiom and environment-linter audit of all stored declarations in the
automatic circle split, source block and restoration route modules, including private and
generated declarations.
This does not replace independent mathematical review or claim the full
geometric/numerical equivalence.
-/

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  let targets : List Name :=
    [`CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Restoration,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationContacts,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationEdges,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationEmbedding,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationGerms,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationOrder,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationParameters,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationRoutes,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationSimplicity,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitLayout,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.EdgeTransport,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Restoration,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.SplitBlocks,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.SplitIntervals,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.SplitUnchanged,
     `CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters,
     `CslibFrontier.Foundations.Geometry.Polygonal.CircleChord,
     `CslibFrontier.Foundations.Geometry.Polygonal.CircleConnector,
     `CslibFrontier.Foundations.Geometry.Polygonal.CircleGaps,
     `CslibFrontier.Foundations.Geometry.Polygonal.CutGerms,
     `CslibFrontier.Foundations.Geometry.Polygonal.FiniteAngleOrder,
     `CslibFrontier.Foundations.Geometry.Polygonal.LineEnds,
     `CslibFrontier.Foundations.Geometry.Polygonal.RayOrder,
     `CslibFrontier.Foundations.GroupTheory.Perm.RemoveTwo,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.BouquetOrder]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut decls : Array Name := #[]
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if targets.contains moduleName then
      modules := modules + 1
      unless data.constNames.size == data.constants.size do
        throwError "polygonal forward audit: malformed declaration table for {moduleName}"
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "polygonal forward audit: missing stored declaration {name}"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "polygonal forward audit: {name} depends on {disallowed}"
        decls := decls.push name
  unless modules == targets.length && !decls.isEmpty do
    throwError "polygonal forward audit: missing owned modules or declarations"
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
      throwError "polygonal forward audit: {name} does not publicly import Cslib.Init"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls checks
  for (linter, failures) in results do
    for (name, message) in failures.toList do
      throwError "polygonal forward audit: {linter.name}: {name}: {message}"
