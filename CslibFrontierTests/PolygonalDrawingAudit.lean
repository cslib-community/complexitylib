/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Neighborhood
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Points
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.Loop
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-!
Scoped standard-three-axiom and environment-linter audit of stored declarations in the new
polygonal topics and the extracted single-loop constructor, including private/generated code.
This supplements the ordinary-import geometric regression clients; it is not an independent
mathematical review or a proof of the outstanding realization equivalence.
-/

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  let targets : List Name :=
    [`CslibFrontier.Foundations.Geometry.Polygonal.Route,
     `CslibFrontier.Foundations.Geometry.Polygonal.Segment,
     `CslibFrontier.Foundations.Geometry.Polygonal.Germs,
     `CslibFrontier.Foundations.Geometry.Polygonal.Neighborhood,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Neighborhood,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Points,
     `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic,
     `CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.Loop]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut decls : Array Name := #[]
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if targets.contains moduleName then
      modules := modules + 1
      unless data.constNames.size == data.constants.size do
        throwError "polygonal audit: malformed declaration table for {moduleName}"
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "polygonal audit: missing stored declaration {name}"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "polygonal audit: {name} depends on {disallowed}"
        decls := decls.push name
  unless modules == targets.length && !decls.isEmpty do
    throwError "polygonal audit: missing owned modules or declarations"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls checks
  for (linter, failures) in results do
    for (name, message) in failures.toList do
      throwError "polygonal audit: {linter.name}: {name}: {message}"
