/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-!
Scoped stored-declaration axiom and environment-linter audits for cycle exactness and finite
intersection parity. Private helpers and generated declarations are included. The allowed
axioms are the usual three; no named result claims a smaller axiom basis.
-/

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  let targets : List Name :=
    [`CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpace,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut decls : Array Name := #[]
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if targets.contains moduleName then
      modules := modules + 1
      unless data.constNames.size == data.constants.size do
        throwError "intersection audit: malformed declaration table for {moduleName}"
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "intersection audit: missing stored declaration {name}"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "intersection audit: {name} depends on {disallowed}"
        decls := decls.push name
  unless modules == 2 && !decls.isEmpty do
    throwError "intersection audit: expected both owned modules and their stored declarations"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls checks
  for (linter, failures) in results do
    for (name, message) in failures.toList do
      throwError "intersection audit: {linter.name}: {name}: {message}"
