/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Construction
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointGenus
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! Stored-declaration axiom, public-init and environment audits of the static closure delta.
Private and generated declarations are included; only the standard three axioms are allowed.
-/

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  let targets : List Name :=
    [`CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointGenus,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointGraph,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointRotation,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinComponents,
     `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus,
     `CslibFrontier.Foundations.GroupTheory.Perm.SelectedOrbitJoin,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Append,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Attachment,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AttachmentLabels,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BinaryAttachment,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BinaryMeet,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryAppend,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryIdentify,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryTransport,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ConstraintJoin,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Construction,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.DifferenceAttachment,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Disjoint,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.FlipAttachment,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ScopeJoin,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.UnaryAttachment,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut decls : Array Name := #[]
  let mut publicImports : NameMap (Array Name) := {}
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    publicImports := publicImports.insert moduleName <|
      data.imports.filter (·.isExported) |>.map (·.module)
    if targets.contains moduleName then
      modules := modules + 1
      unless data.constNames.size == data.constants.size do
        throwError "construction audit: malformed declaration table for {moduleName}"
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "construction audit: unavailable stored declaration {name}"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "construction audit: {name} depends on {disallowed}"
        decls := decls.push name
  unless modules == targets.length && !decls.isEmpty do
    throwError "construction audit: expected {targets.length} owned modules; found {modules}"
  -- Each visited module contributes its public outgoing edges once. The total number
  -- of all loaded import edges bounds the worklist, including repeated queued names.
  let edgeFuel := env.header.moduleData.foldl (fun n data => n + data.imports.size) 1
  for target in targets do
    let mut pending : List Name := [target]
    let mut visited : NameSet := {}
    let mut found := false
    for _ in [:edgeFuel] do
      match pending with
      | [] => break
      | name :: rest =>
        pending := rest
        if name == `Cslib.Init then
          found := true
          break
        unless visited.contains name do
          visited := visited.insert name
          pending := ((publicImports.find? name).getD #[]).toList ++ pending
    unless found do
      throwError "construction audit: {target} does not publicly import Cslib.Init"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls checks
  for (linter, failures) in results do
    for (name, message) in failures.toList do
      throwError "construction audit: {linter.name}: {name}: {message}"
  logInfo m!"Audited {modules} modules and {decls.size} stored declarations"
