/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Audit every declaration stored in the imported `CslibFrontier` modules, including private and
generated declarations and extensions in other namespaces. Transitive axiom dependencies must
be among `propext`, `Classical.choice` and `Quot.sound`. The root-import check ensures that all
library modules are reached. This adapts the original Complexitylib's `scripts/AxiomGuard.lean`.

The audit trusts compiled Lean artifacts; it is not an independent kernel checker. Allowing
`Classical.choice` does not establish computability. Examples and commands that leave no stored
declaration are outside its scope, as are the test modules themselves.

The named `#guard_msgs` checks below record the exact axioms of results that are meant to depend
on fewer axioms than the standard three, for example choice-free results. The global audit
already covers the standard set, so a named guard is added only for such a result, in the
epic's own test module rather than here.
-/

namespace ComplexityTests.Axioms

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut moduleCount : Nat := 0
  let mut declarationCount : Nat := 0
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if (`CslibFrontier).isPrefixOf moduleName then
      moduleCount := moduleCount + 1
      unless data.constNames.size == data.constants.size do
        throwError "axiom audit: malformed declaration table for {moduleName}"
      for name in data.constNames do
        declarationCount := declarationCount + 1
        unless (env.find? name).isSome do
          throwError "axiom audit: declaration {name} from {moduleName} is unavailable"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "axiom audit: {name} from {moduleName} depends on {disallowed}"
  unless moduleCount > 0 && declarationCount > 0 do
    throwError "axiom audit: no CslibFrontier declarations found"

/--
info: 'Cslib.Circuits.Fusion.length_andPairs' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.length_andPairs

/--
info: 'Cslib.Circuits.Fusion.Atom.preserves_map_iff' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.Atom.preserves_map_iff

/--
info: 'Cslib.Circuits.Program.cost_simulateProgram' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.cost_simulateProgram

/--
info: 'Cslib.Circuits.Circuit.cost_program_simulateWithContext' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_program_simulateWithContext

/--
info: 'Cslib.OracleComp.run_interpret_iterate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.OracleComp.run_interpret_iterate

/--
info: 'Turing.MultiTapeMachine.ntmEquiv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.ntmEquiv

/--
info: 'Cslib.RAM.haltsWithResult_iff_eval' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.haltsWithResult_iff_eval

/--
info: 'Cslib.Crypto.GoldreichLevin.checkCandidates_correct' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.checkCandidates_correct

end ComplexityTests.Axioms

/--
info: 'Cslib.OracleComp.map_run_interpret' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.OracleComp.map_run_interpret

/--
info: 'Cslib.IsMonadHom.stateT' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.IsMonadHom.stateT

/-- info: 'Cslib.OracleComp.IsCostBounded.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.OracleComp.IsCostBounded.bind

/--
info: 'Cslib.BitString.word_eq_of_padWord_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Cslib.BitString.word_eq_of_padWord_eq

/--
info: 'Cslib.RotationMap.TowerTable.valid_initial' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.valid_initial

/--
info: 'Cslib.RotationMap.TowerTable.length_iterate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.length_iterate

/--
info: 'Cslib.RotationMap.TowerTable.length_build' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.length_build

/--
info: 'Cslib.PCP.Encoded.Graph.isWellFormed_eq_true' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isWellFormed_eq_true

/--
info: 'Cslib.PCP.Encoded.Graph.checkEdge_eq_true_iff' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.checkEdge_eq_true_iff

/--
info: 'Cslib.PCP.Encoded.Graph.toFiniteGraph_map' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toFiniteGraph_map

/--
info: 'Cslib.PCP.Encoded.Graph.WellFormed.addTrivial' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.WellFormed.addTrivial

/--
info: 'Cslib.PCP.Encoded.Graph.WellFormed.addLoops' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.WellFormed.addLoops

/--
info: 'Cslib.PCP.Encoded.Graph.toGraph_eq_comap' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_eq_comap

/--
info: 'Cslib.PCP.Encoded.Graph.mem_cloud_iff' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.mem_cloud_iff

/--
info: 'Cslib.PCP.Encoded.Graph.toGraph_mapConstraints' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_mapConstraints

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_mapConstraints_iff' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_mapConstraints_iff

/--
info: 'Cslib.BitString.length_listXor' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.length_listXor

/--
info: 'Turing.MultiTapeTM.length_encList_reverse' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.length_encList_reverse

/--
info: 'Cslib.Crypto.GeneratorXor.length_generate' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.length_generate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.length_combinedGenerate' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.length_combinedGenerate

/-! ### Executable PCP powering, composition, and one amplification round -/

/-- info: 'Cslib.RotationMap.walkAtWithInput_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.RotationMap.walkAtWithInput_eq

/-- info: 'Cslib.RotationMap.powRotWithInput_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.RotationMap.powRotWithInput_eq

/-- info: 'Cslib.RotationMap.killedPowRotWithInput_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.RotationMap.killedPowRotWithInput_eq

/-- info: 'Cslib.PCP.RegularConstraintGraph.powerRelationWithInput_eq_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.RegularConstraintGraph.powerRelationWithInput_eq_true

/-- info: 'Cslib.PCP.Encoded.Graph.length_edges_powerPreprocess' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.length_edges_powerPreprocess

/--
info: 'Cslib.PCP.Encoded.Edge.length_encoding' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Edge.length_encoding

/--
info: 'Cslib.PCP.Encoded.Graph.length_encoding' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.length_encoding

/--
info: 'Cslib.Logic.PL.CNF.mem_vars_compact_lt' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.mem_vars_compact_lt

/-- info: 'Turing.MultiTapeTM.encSum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.encSum

/--
info: 'Cslib.PCP.Encoded.Graph.length_queries_repeatedEdgeVerifier' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.length_queries_repeatedEdgeVerifier

/--
info: 'Cslib.BitString.mem_enumList' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.mem_enumList

/--
info: 'Cslib.BitString.binaryValue_reverse_bits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.binaryValue_reverse_bits

/--
info: 'Cslib.Complexity.PCPVerifier.tableVerifier_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCPVerifier.tableVerifier_sound

/--
info: 'Cslib.Circuits.Circuit.cost_program_replicate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_program_replicate

/--
info: 'Cslib.Circuits.Circuit.cost_program_parallel' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_program_parallel

/--
info: 'Cslib.Circuits.Formula.eval_equalBits_iff' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.eval_equalBits_iff

/--
info: 'List.Perm.exists_ofFn_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms List.Perm.exists_ofFn_iff

/--
info: 'Cslib.BitonicSort.unrouteSort_routeSort' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.unrouteSort_routeSort

/--
info: 'Cslib.BitonicSort.routeSort_unrouteSort' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.routeSort_unrouteSort

/--
info: 'Cslib.BitonicSort.routeSort_sortTrace' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.routeSort_sortTrace

/--
info: 'Cslib.BitonicSort.unrouteSort_comp_sort' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.unrouteSort_comp_sort

/--
info: 'Cslib.BitonicSort.two_mul_mergeTraceSize' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.two_mul_mergeTraceSize

/--
info: 'Cslib.BitonicSort.four_mul_sortTraceSize' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.four_mul_sortTraceSize

/--
info: 'Cslib.BitonicSort.unrouteSort_rel_sort' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.unrouteSort_rel_sort

/-- info: 'Cslib.DecisionTree.eval_mapQueries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.DecisionTree.eval_mapQueries

/-- info: 'Cslib.DecisionTree.depth_mapQueries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.DecisionTree.depth_mapQueries

/-- info: 'Cslib.DecisionTree.leafCount_mapQueries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.DecisionTree.leafCount_mapQueries

/-- info: 'Cslib.Circuits.Circuit.cost_program_iterate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_program_iterate
