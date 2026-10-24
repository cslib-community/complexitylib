/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Audit every declaration stored in the imported `Complexity` modules, including private and
generated declarations and extensions in other namespaces. Transitive axiom dependencies must
be among `propext`, `Classical.choice` and `Quot.sound`. The root-import check ensures that all
library modules are reached. This adapts the original Complexitylib's `scripts/AxiomGuard.lean`.

The audit trusts compiled Lean artifacts; it is not an independent kernel checker. Allowing
`Classical.choice` does not establish computability. Examples and commands that leave no stored
declaration are outside its scope, as are the test modules themselves.

The named `#guard_msgs` checks below also record the exact axioms of headline theorems.
Add an entry whenever a main result is added to a public module.
-/

namespace ComplexityTests.Axioms

/--
info: 'Cslib.PCP.AssignmentTester.le_unsatVal_compose' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.AssignmentTester.le_unsatVal_compose

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_composeSelected' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_composeSelected

/--
info: 'Cslib.PCP.HadamardTester.exists_inputDist_div_le_one_sub_acceptProb_selected'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.exists_inputDist_div_le_one_sub_acceptProb_selected

/--
info: 'Cslib.PCP.Encoded.SelectedHadamardTester.isPolyTime_query' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.SelectedHadamardTester.isPolyTime_query

/--
info: 'Cslib.PCP.Encoded.SelectedHadamardTester.isPolyTime_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.SelectedHadamardTester.isPolyTime_accepts

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut moduleCount : Nat := 0
  let mut declarationCount : Nat := 0
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if (`Complexity).isPrefixOf moduleName then
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
    throwError "axiom audit: no Complexity declarations found"

/--
info: 'Cslib.Circuits.Monotone.membershipHomomorphism' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.membershipHomomorphism

/--
info: 'Cslib.Circuits.Monotone.eval_set_iff_computesFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.eval_set_iff_computesFrom

/--
info: 'Cslib.Circuits.Monotone.eval_setOf_iff_computesFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.eval_setOf_iff_computesFrom

/--
info: 'Cslib.Circuits.Monotone.ecomplexityFrom_boolIndicator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.ecomplexityFrom_boolIndicator

/--
info: 'Cslib.Circuits.Fusion.pairCover_lowerBound_of_computesFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.pairCover_lowerBound_of_computesFrom

/--
info: 'Cslib.Circuits.Fusion.pairCoverComplexity_le_ecomplexityFrom_bool' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.pairCoverComplexity_le_ecomplexityFrom_bool

/--
info: 'Cslib.Circuits.Fusion.Atom.preserves_semifilter' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.Atom.preserves_semifilter

/--
info: 'Cslib.Circuits.Fusion.SemifilterWitness.not_predicate_target' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.SemifilterWitness.not_predicate_target

/--
info: 'Cslib.Circuits.Fusion.PairCover.ofCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.ofCircuit

/--
info: 'Cslib.Circuits.Fusion.length_andPairs' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.length_andPairs

/--
info: 'Cslib.Circuits.Fusion.PairCover.length_ofCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.length_ofCircuit

/--
info: 'Cslib.Circuits.Fusion.pairCover_lowerBound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.pairCover_lowerBound

/--
info: 'Cslib.Circuits.Fusion.pairCoverComplexity_le_cost' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.pairCoverComplexity_le_cost

/--
info: 'Cslib.Circuits.Fusion.pairCoverComplexity_le_ecomplexityFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.pairCoverComplexity_le_ecomplexityFrom

/--
info: 'Cslib.Circuits.Circuit.ComputesFrom.map' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.ComputesFrom.map

/--
info: 'Cslib.Circuits.Circuit.computesFrom_map_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.computesFrom_map_iff

/--
info: 'Cslib.Circuits.ecomplexityFrom_map_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_map_le

/--
info: 'Cslib.Circuits.ecomplexityFrom_map_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_map_eq

/--
info: 'Cslib.Circuits.Fusion.Atom.preserves_map_iff' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.Atom.preserves_map_iff

/--
info: 'Cslib.Circuits.Fusion.programAtoms_map' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.programAtoms_map

/--
info: 'Cslib.Circuits.Fusion.Cover.cost_map' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.Cover.cost_map

/--
info: 'Cslib.Circuits.Fusion.coverComplexity_le_comap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.coverComplexity_le_comap

/--
info: 'Cslib.Circuits.Fusion.programAtoms_gate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.programAtoms_gate

/--
info: 'Cslib.Circuits.Fusion.programAtoms_append' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.programAtoms_append

/--
info: 'Cslib.Circuits.Fusion.programAtoms_comp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.programAtoms_comp

/--
info: 'Cslib.Circuits.Fusion.forall_programAtoms_simulate_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.forall_programAtoms_simulate_iff

/--
info: 'Cslib.Circuits.Fusion.forall_programAtoms_simulate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.forall_programAtoms_simulate

/--
info: 'Cslib.Circuits.Fusion.forall_programAtoms_withContext' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.forall_programAtoms_withContext

/--
info: 'Cslib.Circuits.Fusion.forall_programAtoms_simulateWithContext' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.forall_programAtoms_simulateWithContext

/--
info: 'Cslib.Circuits.Program.trace_induction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.trace_induction

/--
info: 'Cslib.Circuits.Program.trace_rel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.trace_rel

/--
info: 'Cslib.Circuits.Program.eval_rel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.eval_rel

/--
info: 'Cslib.Circuits.Fusion.programAtoms_isCover' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.programAtoms_isCover

/--
info: 'Cslib.Circuits.Fusion.Cover.cost_ofProgram' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.Cover.cost_ofProgram

/--
info: 'Cslib.Circuits.Fusion.coverComplexity_le_ecomplexityFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.coverComplexity_le_ecomplexityFrom

/--
info: 'Cslib.Circuits.Fusion.Cover.card_le_mul_cost' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.Cover.card_le_mul_cost

/--
info: 'Cslib.Circuits.Fusion.card_le_mul_program_cost' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.card_le_mul_program_cost

/--
info: 'Cslib.Circuits.Fusion.ceilDiv_card_le_circuit_cost' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.ceilDiv_card_le_circuit_cost

/--
info: 'Cslib.Circuits.SumOfTerms.card_le_mul_dictionaryCost' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.SumOfTerms.card_le_mul_dictionaryCost

/--
info: 'Cslib.Circuits.SumOfTerms.ceilDiv_card_le_termCost' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.SumOfTerms.ceilDiv_card_le_termCost

/--
info: 'Cslib.Circuits.SumOfTerms.card_le_termCost_of_separated' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.SumOfTerms.card_le_termCost_of_separated


/--
info: 'Cslib.Circuits.Formula.cost_toCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.cost_toCircuit

/--
info: 'Cslib.Circuits.Formula.eval_linearForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.eval_linearForm

/--
info: 'Cslib.Circuits.Formula.cost_linearForm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.cost_linearForm

/--
info: 'Cslib.Circuits.Waring.eval_compile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Waring.eval_compile

/--
info: 'Cslib.Circuits.Waring.polynomial_compile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Waring.polynomial_compile

/--
info: 'Cslib.Circuits.Waring.cost_program_compile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Waring.cost_program_compile

/--
info: 'Cslib.Circuits.Waring.mulCost_compile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Waring.mulCost_compile

/--
info: 'Cslib.Circuits.Waring.addCost_compile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Waring.addCost_compile

/--
info: 'Cslib.Circuits.Waring.size_compile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Waring.size_compile

/--
info: 'Cslib.Circuits.Waring.termMultiplicationCount_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Waring.termMultiplicationCount_le

/--
info: 'Cslib.Circuits.Program.cost_simulateProgram' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.cost_simulateProgram

/--
info: 'Cslib.Circuits.Circuit.eval_simulateWithContext' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.eval_simulateWithContext

/--
info: 'Cslib.Circuits.Circuit.cost_program_simulateWithContext' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_program_simulateWithContext

/--
info: 'Cslib.Circuits.eval_binaryPowerCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.eval_binaryPowerCircuit

/--
info: 'Cslib.Circuits.cost_program_binaryPowerCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.cost_program_binaryPowerCircuit

/--
info: 'Cslib.Circuits.size_binaryPowerCircuit_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.size_binaryPowerCircuit_le

/--
info: 'Cslib.Circuits.Program.rank_hessian_trace_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.rank_hessian_trace_le

/--
info: 'Cslib.Circuits.Circuit.hessian_rank_ceilDiv_two_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.hessian_rank_ceilDiv_two_le

/--
info: 'Cslib.Circuits.Circuit.eval_arithInterpretationWith_mvPolynomial' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.eval_arithInterpretationWith_mvPolynomial

/--
info: 'Cslib.Probability.IsOraclePPT.query_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsOraclePPT.query_bounds

/--
info: 'Cslib.Probability.IsOraclePPT.run_interpret_preprocess' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsOraclePPT.run_interpret_preprocess

/--
info: 'Cslib.RandomOracle.interpret_prob_eq_memoize_map' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.interpret_prob_eq_memoize_map

/--
info: 'Cslib.Crypto.prfIdealGame_eq_lazy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.prfIdealGame_eq_lazy

/--
info: 'Cslib.Crypto.prfIdealGame_eq_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.prfIdealGame_eq_cached

/--
info: 'Cslib.Crypto.isPPT_prfIdealGame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.isPPT_prfIdealGame

/--
info: 'Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsOraclePPTOn.run_interpret_preprocess

/--
info: 'Cslib.Probability.OracleSimulation.isPPTOn_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.OracleSimulation.isPPTOn_run

/--
info: 'Cslib.Probability.OracleSimulation.step_eq_run_interpret' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.OracleSimulation.step_eq_run_interpret

/--
info: 'Cslib.ProbOracleComp.eval_run_interpret' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbOracleComp.eval_run_interpret

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases

/--
info: 'Cslib.Probability.IsPPTOn.finite_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsPPTOn.finite_cases

/--
info: 'Turing.MultiTapeTM.length_encFiniteConfig_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.length_encFiniteConfig_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteCfg_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteCfg_step

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_receive

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_init

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_apply

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_update' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.pi_update

/--
info: 'Turing.MultiTapeTM.length_encPi_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.length_encPi_le

/--
info: 'Turing.MultiTapeTM.length_encBiTape_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.length_encBiTape_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.biTape_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.biTape_step

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.biTape_mk₁' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.biTape_mk₁

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.stackTape_cons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.stackTape_cons

/--
info: 'Cslib.Turing.BiTape.Represents.step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Turing.BiTape.Represents.step

/--
info: 'Turing.MultiTapeMachine.FiniteConfig.SpaceBound.receive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.FiniteConfig.SpaceBound.receive

/--
info: 'Turing.MultiTapeMachine.finiteRunFrom_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.finiteRunFrom_eq

/--
info: 'Cslib.OracleComp.run_interpret_iterate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.OracleComp.run_interpret_iterate

/--
info: 'Turing.MultiTapePTM.run_interpret_runConfigFrom_ofDeterministic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapePTM.run_interpret_runConfigFrom_ofDeterministic

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.isPPTOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.isPPTOn

/--
info: 'Cslib.Probability.IsPPTOn.length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsPPTOn.length_le

/--
info: 'Cslib.Probability.isPPTOn_uniform_bool' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.isPPTOn_uniform_bool

/--
info: 'Turing.MultiTapeMachine.tmEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.tmEquiv

/--
info: 'Turing.MultiTapeMachine.ntmEquiv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.ntmEquiv

/--
info: 'Turing.MultiTapeMachine.step_toNTM_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.step_toNTM_iff

/--
info: 'Turing.MultiTapeMachine.runConfigFrom_toTM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.runConfigFrom_toTM

/--
info: 'Turing.MultiTapeMachine.runConfigFrom_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.runConfigFrom_add

/--
info: 'Turing.MultiTapeMachine.interpret_runConfigFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.interpret_runConfigFrom

/--
info: 'Turing.MultiTapeMachine.length_output_runConfigFrom_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeMachine.length_output_runConfigFrom_le

/--
info: 'Cslib.Complexity.CookLevin.tableau_satisfiable_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CookLevin.tableau_satisfiable_iff

/--
info: 'Cslib.Complexity.CookLevin.reduce_mem_SAT_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CookLevin.reduce_mem_SAT_iff

/--
info: 'Cslib.Complexity.CookLevin.SAT_npComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CookLevin.SAT_npComplete

/--
info: 'Cslib.Complexity.IsVerifier.exists_decidesInTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IsVerifier.exists_decidesInTime

/--
info: 'Cslib.Complexity.decidableInPolyTime_of_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.decidableInPolyTime_of_mem_NP

/--
info: 'Cslib.Complexity.mem_NP_of_decidableInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_of_decidableInPolyTime

/--
info: 'Cslib.Complexity.mem_NP_iff_decidableInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_iff_decidableInPolyTime

/--
info: 'Cslib.Logic.ESO.Definable.queryLanguage_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.queryLanguage_mem_NP

/--
info: 'Cslib.Logic.ESO.Sentence.Layout.computableInPolyTime_verifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.Layout.computableInPolyTime_verifier

/--
info: 'Cslib.Complexity.SAT.isVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.isVerifier

/--
info: 'Cslib.Complexity.SAT.computableInPolyTime_verifier' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT.computableInPolyTime_verifier

/--
info: 'Cslib.Complexity.SAT.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.mem_NP

/--
info: 'Cslib.Complexity.UNSAT_mem_coNP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.UNSAT_mem_coNP

/--
info: 'Cslib.Complexity.mem_ThreeSAT_toThreeSAT_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.mem_ThreeSAT_toThreeSAT_iff

/--
info: 'Cslib.Complexity.ThreeSAT_npComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.ThreeSAT_npComplete

/--
info: 'Cslib.Complexity.IndependentSet_npComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IndependentSet_npComplete

/--
info: 'Cslib.Complexity.Clique_npComplete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Clique_npComplete

/--
info: 'Cslib.Logic.PL.CNF.satisfiable_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Logic.PL.CNF.satisfiable_relabel

/--
info: 'Cslib.PolynomiallyBounded.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.PolynomiallyBounded.polynomial_eval

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.PPoly.of_mem_P

/--
info: 'Cslib.Circuits.Boolean.PPoly.exists_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.PPoly.exists_not_mem

/--
info: 'Cslib.Complexity.SAT.toIndependentSet_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.SAT.toIndependentSet_mem_iff

/--
info: 'Cslib.Circuits.Boolean.PPoly.exists_of_mem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.PPoly.exists_of_mem_P

/--
info: 'Cslib.Circuits.Boolean.MachineSimulation.acceptedWithin_mem_PPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MachineSimulation.acceptedWithin_mem_PPoly

/--
info: 'Cslib.Complexity.Graph.compl_mem_Clique_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.Graph.compl_mem_Clique_iff

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_boundedError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_boundedError

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_mem_BPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_mem_BPP

/--
info: 'Cslib.card_filter_card_filter_le_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.card_filter_card_filter_le_le

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_oneSidedError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_oneSidedError

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_mem_RP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_mem_RP

/--
info: 'Cslib.Complexity.RP_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.RP_subset_NP

/--
info: 'Cslib.Circuits.Boolean.mem_PPoly_iff_exists_mem_SIZE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.mem_PPoly_iff_exists_mem_SIZE

/--
info: 'Cslib.Circuits.Boolean.complexity_le_of_boundedError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_of_boundedError

/--
info: 'Cslib.Circuits.Boolean.complexity_le_of_oneSidedError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_of_oneSidedError

/--
info: 'Cslib.Circuits.Boolean.PPoly.of_mem_coRP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.of_mem_coRP

/--
info: 'Cslib.containsSunflower_of_forall_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.containsSunflower_of_forall_card_le

/--
info: 'Cslib.Circuits.Approximation.Scheme.card_failures_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Approximation.Scheme.card_failures_le_cost

/--
info: 'Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_ecomplexity_clique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_ecomplexity_clique

/--
info: 'Cslib.Circuits.Monotone.choose_le_or_pow_le_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.choose_le_or_pow_le_mul_size

/--
info: 'Cslib.Circuits.Monotone.two_rpow_sqrt_lt_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.two_rpow_sqrt_lt_size

/--
info: 'Cslib.Circuits.Circuit.essential_le_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.essential_le_size

/--
info: 'Cslib.Circuits.Boolean.PPoly.exists_of_mem_BPP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.exists_of_mem_BPP

/--
info: 'Cslib.Circuits.Boolean.PPoly.exists_of_mem_RP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.PPoly.exists_of_mem_RP

/--
info: 'Cslib.Circuits.Boolean.SIZE_ssubset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SIZE_ssubset

/--
info: 'Cslib.Circuits.Monotone.exists_computes_clique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.exists_computes_clique

/--
info: 'Cslib.Circuits.Boolean.SIZE_pow_ssubset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SIZE_pow_ssubset

/--
info: 'Cslib.Circuits.Circuit.essential_le_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.essential_le_depth

/--
info: 'Cslib.Circuits.Monotone.edgeCount_le_two_pow_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.edgeCount_le_two_pow_depth

/--
info: 'Cslib.Circuits.Boolean.three_mul_le_cost_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.three_mul_le_cost_of_computes_parity

/--
info: 'Cslib.Circuits.Boolean.three_mul_le_complexity_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.three_mul_le_complexity_parity

/--
info: 'Cslib.Circuits.Boolean.isLeast_cost_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.isLeast_cost_parity

/--
info: 'Cslib.Circuits.Formula.sq_card_hammingEdges_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.sq_card_hammingEdges_le

/--
info: 'Cslib.Circuits.Boolean.isLeast_leafSize_parity_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.isLeast_leafSize_parity_two_pow

/--
info: 'Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_threshold

/--
info: 'Cslib.DecisionTree.complexity_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.complexity_parity

/--
info: 'Cslib.DecisionTree.complexity_le_certificateComplexityFor_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.complexity_le_certificateComplexityFor_mul

/--
info: 'Cslib.DecisionTree.card_le_complexity_of_forall_update_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.card_le_complexity_of_forall_update_ne

/--
info: 'Cslib.Circuits.Boolean.prod_card_subfunctions_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.prod_card_subfunctions_le

/--
info: 'Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_elementDistinctness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.mul_le_leafSize_of_computes_elementDistinctness

/--
info: 'Cslib.Circuits.Boolean.formulaDepth_eq_ecomplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.formulaDepth_eq_ecomplexity

/--
info: 'Cslib.Circuits.Boolean.exists_monoidProgram_computes_of_formulaDepth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_monoidProgram_computes_of_formulaDepth

/--
info: 'Cslib.Circuits.Boolean.exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_monoidProgram_alternatingGroup_computes_of_mem_NC_one

/--
info: 'Cslib.BranchingPrograms.MonoidProgram.Computes.exists_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BranchingPrograms.MonoidProgram.Computes.exists_formula

/--
info: 'Cslib.BranchingPrograms.MonoidProgram.exists_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BranchingPrograms.MonoidProgram.exists_formula

/--
info: 'Cslib.DecisionTree.eval_toDNF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.eval_toDNF

/--
info: 'Cslib.BitString.PartialAssignment.card_withFree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.PartialAssignment.card_withFree

/--
info: 'Cslib.Logic.PL.DNF.eval_canonicalTree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.eval_canonicalTree

/--
info: 'Cslib.Logic.PL.DNF.complexity_lt_of_forall_pathLength_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.complexity_lt_of_forall_pathLength_lt

/--
info: 'Cslib.Logic.PL.DNF.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.decode_encode

/--
info: 'Cslib.Logic.PL.DNF.card_switching_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.card_switching_le

/--
info: 'Turing.MultiTapeTM.runFrom_shadow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.runFrom_shadow

/--
info: 'Turing.MultiTapeTM.runFrom_clearShadowed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.runFrom_clearShadowed

/--
info: 'Turing.MultiTapeTM.exists_runPath_seq_space_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.exists_runPath_seq_space_le

/--
info: 'Turing.MultiTapeTM.exists_runPath_tidy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.exists_runPath_tidy

/--
info: 'Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace

/--
info: 'Cslib.BitString.PartialAssignment.card_extensions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.PartialAssignment.card_extensions

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_formula_computes_parity

/--
info: 'Cslib.Circuits.Boolean.parity_notMem_AC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.parity_notMem_AC0

/--
info: 'Cslib.PolynomiallyBounded.eventually_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PolynomiallyBounded.eventually_lt_two_pow

/--
info: 'Cslib.Circuits.Boolean.majority_notMem_AC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.majority_notMem_AC0

/--
info: 'Cslib.Circuits.Circuit.depth_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.depth_comp_le

/--
info: 'Cslib.Circuits.Circuit.depth_append_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.depth_append_le

/--
info: 'Cslib.Circuits.Boolean.ConstDepth.compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ConstDepth.compl

/--
info: 'Cslib.Circuits.Boolean.AC0_ssubset_TC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC0_ssubset_TC0

/--
info: 'Cslib.Circuits.Circuit.eval_mapOp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.eval_mapOp

/--
info: 'Cslib.Circuits.Boolean.Smolensky.exists_lowDegree_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.exists_lowDegree_approx

/--
info: 'Cslib.BitString.card_agree_parity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.card_agree_parity_le

/--
info: 'Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity

/--
info: 'Cslib.Circuits.Boolean.Smolensky.parity_notMem_AC0Mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.parity_notMem_AC0Mod

/--
info: 'Cslib.Circuits.Boolean.ConstDepth.parity_mem_of_majority_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ConstDepth.parity_mem_of_majority_mem

/--
info: 'Cslib.Circuits.Boolean.parity_mem_TC0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.parity_mem_TC0

/--
info: 'Cslib.Circuits.Boolean.Smolensky.majority_notMem_AC0Mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.majority_notMem_AC0Mod

/--
info: 'Cslib.Circuits.Boolean.Smolensky.TC0_not_subset_AC0Mod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Smolensky.TC0_not_subset_AC0Mod

/--
info: 'Cslib.Circuits.Boolean.exists_formula_depthWith_le_four_mul_clog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_formula_depthWith_le_four_mul_clog

/--
info: 'Cslib.Circuits.Boolean.leafSize_le_two_pow_depthWith_binaryCost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.leafSize_le_two_pow_depthWith_binaryCost

/--
info: 'Cslib.Circuits.Boolean.formulaDepth_le_four_mul_clog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.formulaDepth_le_four_mul_clog

/--
info: 'Cslib.BitString.sum_fourierCoeff_mul_chi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.sum_fourierCoeff_mul_chi

/--
info: 'Cslib.BitString.expect_mul_eq_sum_fourierCoeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_mul_eq_sum_fourierCoeff_mul

/--
info: 'Cslib.BitString.sum_fourierCoeff_sq_signVal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.sum_fourierCoeff_sq_signVal

/--
info: 'Cslib.DecisionTree.fourierCoeff_eq_zero_of_depth_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.fourierCoeff_eq_zero_of_depth_lt

/--
info: 'Cslib.IsGrading.exists_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.IsGrading.exists_sdiff

/--
info: 'Cslib.BitString.expect_sum_fourierCoeff_piecewise_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_sum_fourierCoeff_piecewise_sq

/--
info: 'Cslib.Circuits.Boolean.complexity_existsGuess_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_existsGuess_le

/--
info: 'Cslib.Logic.PL.CNF.derives_nil_iff_not_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.derives_nil_iff_not_satisfiable

/--
info: 'Cslib.Circuits.Boolean.ModelChecking.exists_formula_realize_structure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ModelChecking.exists_formula_realize_structure

/--
info: 'Cslib.Code.card_mul_sum_choose_le_of_two_mul_lt_minDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.card_mul_sum_choose_le_of_two_mul_lt_minDist

/--
info: 'Cslib.Circuits.Boolean.NC_subset_AC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.NC_subset_AC

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_exists_not_shallow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_pow_mul_card_filter_exists_not_shallow_le

/--
info: 'Cslib.Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.sum_fourierCoeff_sq_le_of_computes

/--
info: 'Cslib.Logic.PL.CNF.sum_two_rpow_card_isolated_div_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.sum_two_rpow_card_isolated_div_le

/--
info: 'Cslib.Logic.PL.CNF.sparsification' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.sparsification

/--
info: 'Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose

/--
info: 'Cslib.Logic.PL.CNF.card_isolatedInputs_mul_two_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.card_isolatedInputs_mul_two_rpow_le

/--
info: 'Cslib.Logic.PL.CNF.two_pow_le_length_of_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_pow_le_length_of_eval_eq_parity

/--
info: 'Cslib.Logic.PL.CNF.two_rpow_le_length_of_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_rpow_le_length_of_any_eval_eq_parity

/--
info: 'Cslib.Logic.PL.CNF.exists_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.exists_any_eval_eq_parity

/--
info: 'Cslib.Logic.PL.CNF.sum_two_rpow_sum_inv_critWidth_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.sum_two_rpow_sum_inv_critWidth_le

/--
info: 'Cslib.Logic.PL.CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity

/--
info: 'Cslib.Circuits.Boolean.AltFormula.exists_of_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AltFormula.exists_of_isSymmetric

/--
info: 'Cslib.Circuits.Boolean.Unbounded.exists_circuit_of_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.exists_circuit_of_isSymmetric

/--
info: 'Cslib.Logic.PL.ClauseSet.sparsification' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.ClauseSet.sparsification

/--
info: 'Cslib.Logic.PL.CNF.two_pow_mul_min_le_of_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.two_pow_mul_min_le_of_any_eval_eq_parity

/--
info: 'Cslib.Code.exists_le_minDist_and_prod_le_card_mul_card_filter_hammingDist_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Code.exists_le_minDist_and_prod_le_card_mul_card_filter_hammingDist_lt

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_parity

/--
info: 'Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_parity

/--
info: 'Cslib.Communication.not_solvesKW_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.not_solvesKW_parity

/--
info: 'Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_majority

/--
info: 'Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_majority

/--
info: 'Cslib.Logic.PL.ClauseSet.card_solutions_le_of_not_containsSubcube' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.ClauseSet.card_solutions_le_of_not_containsSubcube

/--
info: 'Cslib.Logic.PL.eventually_two_rpow_le_sigmaThreeSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.eventually_two_rpow_le_sigmaThreeSize

/--
info: 'Cslib.Circuits.Boolean.AltFormula.two_rpow_lt_size_of_eval_eq_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AltFormula.two_rpow_lt_size_of_eval_eq_majority

/--
info: 'Cslib.Circuits.Boolean.AltFormula.exists_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AltFormula.exists_majority

/--
info: 'Cslib.Communication.not_solvesKW_strictMajority' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Communication.not_solvesKW_strictMajority

/--
info: 'Cslib.BitString.exists_mirror_set' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_mirror_set

/--
info: 'Cslib.BitString.influence_eq_sum_fourierCoeff_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.influence_eq_sum_fourierCoeff_sq

/--
info: 'Cslib.BitString.totalInfluence_signVal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.totalInfluence_signVal

/--
info: 'Cslib.BitString.expect_sub_expect_sq_le_totalInfluence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.expect_sub_expect_sq_le_totalInfluence

/--
info: 'Cslib.BitString.fourierCoeff_noiseOp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.fourierCoeff_noiseOp

/--
info: 'Cslib.BitString.noiseStability_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.noiseStability_eq_sum

/--
info: 'Cslib.BitString.noiseSensitivity_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.noiseSensitivity_eq_sum

/--
info: 'Cslib.BitString.fourierCoeff_convolution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.fourierCoeff_convolution

/--
info: 'Cslib.BitString.exists_eq_parityOn_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_eq_parityOn_iff

/--
info: 'Cslib.BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three

/--
info: 'Cslib.BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance

/--
info: 'Cslib.Logic.PL.CNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity

/--
info: 'Cslib.Logic.PL.DNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_all_eval_eq_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.DNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_all_eval_eq_parity

/--
info: 'Cslib.Circuits.Boolean.AC_subset_NC_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.AC_subset_NC_succ

/--
info: 'Cslib.Circuits.Boolean.iUnion_NC_eq_iUnion_AC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.iUnion_NC_eq_iUnion_AC

/--
info: 'Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation

/--
info: 'Cslib.DecisionTree.totalInfluence_le_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.totalInfluence_le_depth

/--
info: 'Cslib.Circuits.Monotone.eformulaDepth_eq_ecomplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.eformulaDepth_eq_ecomplexity

/--
info: 'Cslib.exists_forall_exists_add_mem_of_card_mul_card_compl_pow_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.exists_forall_exists_add_mem_of_card_mul_card_compl_pow_lt

/--
info: 'Cslib.BitString.mem_iff_exists_forall_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.mem_iff_exists_forall_exists

/--
info: 'Cslib.BitString.mem_iff_forall_exists_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.mem_iff_forall_exists_forall

/--
info: 'Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five

/--
info: 'Cslib.Circuits.Boolean.NC_one_eq_polyLength_alternatingGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.NC_one_eq_polyLength_alternatingGroup

/--
info: 'Cslib.Circuits.Boolean.NC_one_eq_polyLength_end' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.NC_one_eq_polyLength_end

/--
info: 'Cslib.Circuits.Boolean.mem_NC_one_iff_formulaDepth_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.mem_NC_one_iff_formulaDepth_le

/--
info: 'Cslib.Circuits.Circuit.size_toFormula_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.size_toFormula_lt

/--
info: 'Cslib.Crypto.PRG.Generator.exists_half_add_div_le_predictionExperiment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.Generator.exists_half_add_div_le_predictionExperiment

/--
info: 'Cslib.Crypto.PRG.Generator.Unpredictable.secure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.Generator.Unpredictable.secure

/--
info: 'Cslib.Crypto.PRG.Generator.Secure.unpredictable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.Generator.Secure.unpredictable

/--
info: 'Cslib.Probability.IsPairwiseIndependentHash.three_quarters_mul_le_dens_filter_mem_image' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Probability in
#print axioms IsPairwiseIndependentHash.three_quarters_mul_le_dens_filter_mem_image

/--
info: 'Cslib.Probability.IsPairwiseIndependentHash.three_sixteenths_le_dens_filter_card_filter_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Probability in
#print axioms IsPairwiseIndependentHash.three_sixteenths_le_dens_filter_card_filter_eq_one

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_affineHash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_affineHash

/--
info: 'Cslib.Probability.ApproximateCounting.three_quarters_le_dens_filter_affineHashEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.ApproximateCounting.three_quarters_le_dens_filter_affineHashEstimate

/--
info: 'Cslib.RotationMap.spectralExpansion_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_le_iff

/--
info: 'Cslib.RotationMap.abs_card_interedges_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.abs_card_interedges_sub_le

/--
info: 'Cslib.RotationMap.abs_card_interedges_sub_le_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.abs_card_interedges_sub_le_mul_sqrt

/--
info: 'Cslib.RotationMap.le_card_interedges_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.le_card_interedges_compl

/--
info: 'Cslib.RotationMap.exists_isSimple_toSimpleGraph_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_isSimple_toSimpleGraph_eq

/--
info: 'Cslib.BitString.abs_expect_signVal_xorMajority_mul_signVal_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.abs_expect_signVal_xorMajority_mul_signVal_le

/--
info: 'Cslib.BitString.two_mul_card_agree_xorMajority_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.two_mul_card_agree_xorMajority_le

/--
info: 'Cslib.BitString.card_filter_selfCorrect_ne_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.card_filter_selfCorrect_ne_le

/--
info: 'Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect

/--
info: 'Cslib.BitString.exists_eq_hadamardCode_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_eq_hadamardCode_iff

/--
info: 'Cslib.BitString.two_mul_hammingDist_hadamardCode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.two_mul_hammingDist_hadamardCode

/--
info: 'Cslib.BitString.eq_of_hammingDist_hadamardCode_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.eq_of_hammingDist_hadamardCode_le

/--
info: 'Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.one_sub_two_mul_le_expect_selfCorrect_eq_apply

/--
info: 'Cslib.BitString.existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.existsUnique_hammingDist_hadamardCode_le_of_le_blrAcceptance

/--
info: 'Cslib.BitString.hadamardCode_tensor_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.hadamardCode_tensor_tensor

/--
info: 'Cslib.BitString.one_div_four_le_expect_hadamardCode_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.one_div_four_le_expect_hadamardCode_tensor

/--
info: 'Cslib.BitString.eq_tensor_of_lt_tensorTestAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.eq_tensor_of_lt_tensorTestAcceptance

/--
info: 'Cslib.BitString.hadamardCode_eq_of_lt_equationTestAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.hadamardCode_eq_of_lt_equationTestAcceptance

/--
info: 'Cslib.BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_predictionExperiment_le_hardwiredExperiment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_predictionExperiment_le_hardwiredExperiment

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_hardwiredExperiment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_hardwiredExperiment

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_card_nextBitGuess_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_half_add_div_le_card_nextBitGuess_eq

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_dependsOn_half_add_div_le_card_nextBitGuess_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_dependsOn_half_add_div_le_card_nextBitGuess_eq

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.exists_complexity_le_half_add_div_le_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.exists_complexity_le_half_add_div_le_card_eq

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.toReal_realExperiment_sub_toReal_idealExperiment_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.toReal_realExperiment_sub_toReal_idealExperiment_lt

/--
info: 'Cslib.Circuits.Boolean.complexity_le_of_dependsOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_le_of_dependsOn

/--
info: 'Cslib.Circuits.Boolean.dist_complexity_le_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.dist_complexity_le_of_cover

/--
info: 'Cslib.Circuits.Boolean.complexityGiven_le_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexityGiven_le_of_cover

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.complexity_indicator_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.complexity_indicator_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.complexityOn_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.complexityOn_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_single_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_single_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.exists_hard_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.exists_hard_indicator

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.not_isLittleO_of_dist_complexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.not_isLittleO_of_dist_complexity_le

/--
info: 'Cslib.Circuits.Boolean.SparseSynthesis.le_vcDim_circuitSets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.SparseSynthesis.le_vcDim_circuitSets

/--
info: 'Cslib.RotationMap.card_mul_one_sub_secondEigenvalue_div_two_le_edgeExpansion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_mul_one_sub_secondEigenvalue_div_two_le_edgeExpansion

/--
info: 'Cslib.RotationMap.expect_mul_walk_le_of_mul_card_le_card_interedges_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.expect_mul_walk_le_of_mul_card_le_card_interedges_compl

/--
info: 'Cslib.RotationMap.secondEigenvalue_le_one_sub_edgeExpansion_sq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.secondEigenvalue_le_one_sub_edgeExpansion_sq_div

/--
info: 'Cslib.RotationMap.edgeExpansion_le_card_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.edgeExpansion_le_card_mul_sqrt

/--
info: 'Cslib.RotationMap.spectralExpansion_eq_secondEigenvalue_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_eq_secondEigenvalue_of_nonneg

/--
info: 'Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_four_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_four_mul_sq

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_of_isPrimePow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_of_isPrimePow

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.card_polynomialBlock_inter_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.card_polynomialBlock_inter_le

/--
info: 'Cslib.Probability.ApproximateCounting.le_nthRoot_and_mul_nthRoot_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.ApproximateCounting.le_nthRoot_and_mul_nthRoot_le

/--
info: 'Cslib.Probability.ApproximateCounting.dens_filter_not_relativeHashEstimate_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.ApproximateCounting.dens_filter_not_relativeHashEstimate_le

/--
info: 'Cslib.Probability.ApproximateCounting.one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Probability.ApproximateCounting in
#print axioms one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate

/--
info: 'Cslib.Probability.ApproximateCounting.one_sub_inv_two_pow_le_dens_filter_affineRelativeHashEstimate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Probability.ApproximateCounting in
#print axioms one_sub_inv_two_pow_le_dens_filter_affineRelativeHashEstimate

/--
info: 'Cslib.RotationMap.walk_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.walk_pow

/--
info: 'Cslib.RotationMap.spectralExpansion_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_pow

/--
info: 'Cslib.RotationMap.spectralExpansion_tensor_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_tensor_le

/--
info: 'Cslib.RotationMap.spectralExpansion_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_tensor

/--
info: 'Cslib.RotationMap.walk_zigzag' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.walk_zigzag

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzag_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzag_le

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzag_le_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzag_le_one_sub

/--
info: 'Cslib.RotationMap.walk_balancedReplacement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.walk_balancedReplacement

/--
info: 'Cslib.RotationMap.spectralExpansion_balancedReplacement_pow_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_balancedReplacement_pow_three_le

/--
info: 'Cslib.RotationMap.spectralExpansion_balancedReplacement_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_balancedReplacement_le

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_add_of_dens_filter_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_add_of_dens_filter_sub_eq

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_add_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_add_of_shift

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_add_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_add_of_surjective

/--
info: 'Cslib.Probability.isPairwiseIndependentHash_toeplitzHash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPairwiseIndependentHash_toeplitzHash

/--
info: 'Cslib.Probability.card_toeplitzHash_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.card_toeplitzHash_seed

/--
info: 'Matrix.toeplitz_mulVec_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.toeplitz_mulVec_surjective

/--
info: 'Cslib.RotationMap.spectralExpansion_union_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_union_le

/--
info: 'Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div

/--
info: 'Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl

/--
info: 'Cslib.RotationMap.card_interedges_compl_ofPerms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_interedges_compl_ofPerms

/--
info: 'Cslib.RotationMap.le_edgeExpansion_ofPerms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.le_edgeExpansion_ofPerms

/--
info: 'Cslib.RotationMap.exists_spectralExpansion_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_spectralExpansion_le

/--
info: 'Cslib.RotationMap.exists_forall_exists_spectralExpansion_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_forall_exists_spectralExpansion_le

/--
info: 'Cslib.exists_perms_card_le_mul_card_filter_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.exists_perms_card_le_mul_card_filter_notMem

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.ecomplexity_le_natCast_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.ecomplexity_le_natCast_iff

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_antitone

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.iInf_etimeBoundedComplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.iInf_etimeBoundedComplexity

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.encard_setOf_ecomplexity_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.encard_setOf_ecomplexity_lt

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_forall_le_etimeBoundedComplexity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_forall_le_etimeBoundedComplexity

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.encard_setOf_length_eq_ecomplexity_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.encard_setOf_length_eq_ecomplexity_lt

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Simulation.ecomplexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Simulation.ecomplexity_le

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Simulation.etimeBoundedComplexity_le_of_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Simulation.etimeBoundedComplexity_le_of_polynomial

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal.invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.IsAdditivelyOptimal.invariance

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.mem_ofMultiTapeTM_runFor_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.mem_ofMultiTapeTM_runFor_iff

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.exists_simulation_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.exists_simulation_literal

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.Composition.ecomplexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.Composition.ecomplexity_le

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.depthBetween_add_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.depthBetween_add_depth

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.isPartrec_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.isPartrec_universal

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.isAdditivelyOptimal_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.isAdditivelyOptimal_universal

/--
info: 'Cslib.Logic.FO.Interpretation.realize_onSentence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Interpretation.realize_onSentence

/--
info: 'Cslib.Logic.FO.Interpretation.compEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Interpretation.compEquiv

/--
info: 'Cslib.Logic.FO.Interpretation.realize_onESOSentence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Interpretation.realize_onESOSentence

/--
info: 'Cslib.Logic.FO.Definable.of_reduces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Definable.of_reduces

/--
info: 'Cslib.Logic.FO.Reduces.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.trans

/--
info: 'Cslib.Logic.FO.Reduces.isoClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Reduces.isoClosed

/--
info: 'Cslib.Logic.ESO.Definable.isoClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.isoClosed

/--
info: 'Cslib.Logic.FO.Definable.simpleGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.FO.Definable.simpleGraph

/--
info: 'Cslib.Logic.ESO.Sentence.realize_iff_of_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.realize_iff_of_equiv

/--
info: 'Cslib.Logic.ESO.Sentence.realize_colorable_structure_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Sentence.realize_colorable_structure_iff

/--
info: 'Cslib.Logic.ESO.Definable.of_fo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.of_fo

/--
info: 'Cslib.Logic.ESO.Definable.of_reduces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.of_reduces

/--
info: 'Cslib.Logic.ESO.Definable.colorable_simpleGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.ESO.Definable.colorable_simpleGraph

/--
info: 'Cslib.RotationMap.expect_splitWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.expect_splitWalk

/--
info: 'Cslib.RotationMap.card_filter_splitWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_filter_splitWalk

/--
info: 'Cslib.RotationMap.sum_walkDart' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.sum_walkDart

/--
info: 'Cslib.RotationMap.expect_walkDart_mul_walkDart' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.expect_walkDart_mul_walkDart

/--
info: 'Cslib.RotationMap.sq_expect_walkDart_mul_walkDart_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.sq_expect_walkDart_mul_walkDart_sub_le

/--
info: 'Cslib.card_filter_killTime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.card_filter_killTime_eq

/--
info: 'Cslib.RotationMap.card_filter_killTime_eq_and_splitWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_filter_killTime_eq_and_splitWalk

/--
info: 'Cslib.PCP.ConstraintGraph.exists_unsatFrac_eq_unsatVal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.exists_unsatFrac_eq_unsatVal

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_eq_zero_iff

/--
info: 'Cslib.PCP.ConstraintGraph.card_mul_unsatVal_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.card_mul_unsatVal_add_le

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_map

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_ofCNF_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_ofCNF_iff

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_ofCNF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_ofCNF

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_degreeReduce' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_degreeReduce

/--
info: 'Cslib.RotationMap.mul_card_filter_ne_le_card_filter_ne_neighbor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.mul_card_filter_ne_le_card_filter_ne_neighbor

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_reindex

/--
info: 'Cslib.PCP.RegularConstraintGraph.unsatVal_addTrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.unsatVal_addTrivial

/--
info: 'Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_le

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_preprocess_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_preprocess_iff

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess

/--
info: 'Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_expanderFamily_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.spectralExpansion_preprocess_expanderFamily_le

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess_expanderFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_preprocess_expanderFamily

/--
info: 'Relation.RelatesWithinSteps.add_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.RelatesWithinSteps.add_iff

/--
info: 'Relation.RelatesWithinSteps.two_pow_succ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.RelatesWithinSteps.two_pow_succ_iff

/--
info: 'Relation.reflTransGen_iff_relatesWithinSteps_two_pow_clog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.reflTransGen_iff_relatesWithinSteps_two_pow_clog

/--
info: 'Relation.reachableWithin_eq_of_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.reachableWithin_eq_of_card_le

/--
info: 'Relation.IsRoundList.mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.IsRoundList.mem_iff

/--
info: 'Relation.exists_isRoundList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.exists_isRoundList

/--
info: 'Relation.not_relatesWithinSteps_succ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.not_relatesWithinSteps_succ_iff

/--
info: 'Relation.not_reflTransGen_iff_exists_isRoundList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Relation.not_reflTransGen_iff_exists_isRoundList

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzagTower_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzagTower_le

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzagTower_le_two_div_five' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzagTower_le_two_div_five

/--
info: 'Cslib.RotationMap.card_zigzagTowerVertex_of_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_zigzagTowerVertex_of_equiv

/--
info: 'Cslib.RotationMap.exists_spectralExpansion_zigzagTower_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.exists_spectralExpansion_zigzagTower_le

/--
info: 'Cslib.RotationMap.walk_affinePlane_twice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.walk_affinePlane_twice

/--
info: 'Cslib.RotationMap.spectralExpansion_affinePlane_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_affinePlane_le

/--
info: 'Cslib.RotationMap.spectralExpansion_affinePlaneTowerBase_le_one_div_five' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_affinePlaneTowerBase_le_one_div_five

/--
info: 'Cslib.RotationMap.spectralExpansion_affinePlaneTower_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_affinePlaneTower_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_tensor

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_zigzag' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_zigzag

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_affinePlane' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_affinePlane

/--
info: 'Cslib.RotationMap.card_interedges_le_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_interedges_le_contract

/--
info: 'Cslib.RotationMap.le_card_interedges_compl_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.le_card_interedges_compl_contract

/--
info: 'Cslib.RotationMap.spectralExpansion_contract_lazy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_contract_lazy_le

/--
info: 'Cslib.RotationMap.isPartialInv_finSlots' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.isPartialInv_finSlots

/--
info: 'Cslib.RotationMap.spectralExpansion_contractFin_lazy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_contractFin_lazy_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionElimWithInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionElimWithInput

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_contract

/--
info: 'Cslib.RotationMap.spectralExpansion_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_reindex

/--
info: 'Cslib.RotationMap.zigzagTower_size_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.zigzagTower_size_bounds

/--
info: 'Cslib.RotationMap.spectralExpansion_zigzagTowerFamily_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_zigzagTowerFamily_le

/--
info: 'Cslib.RotationMap.card_affinePlaneFamilyLabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.card_affinePlaneFamilyLabel

/--
info: 'Cslib.RotationMap.spectralExpansion_affinePlaneFamily_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_affinePlaneFamily_le

/--
info: 'Cslib.RotationMap.spectralExpansion_arithmeticExpander_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_arithmeticExpander_le

/--
info: 'Cslib.RotationMap.spectralExpansion_arithmeticExpander_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.spectralExpansion_arithmeticExpander_lt_one

/--
info: 'Cslib.RotationMap.arithmeticExpanderFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.arithmeticExpanderFamily

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_reindex


/--
info: 'Cslib.RAM.computesInTime_unitCost_repeatedSquaring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.computesInTime_unitCost_repeatedSquaring

/--
info: 'Cslib.RAM.exists_mul_pow_lt_of_computesInTime_logCost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.exists_mul_pow_lt_of_computesInTime_logCost

/--
info: 'Cslib.RAM.haltsWithResult_iff_eval' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.haltsWithResult_iff_eval

/--
info: 'Cslib.RAM.bitLength_read_run_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RAM.bitLength_read_run_le

/--
info: 'Cslib.Circuits.Frontier.RectangleFree.pow_ncard_compl_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.RectangleFree.pow_ncard_compl_lt

/--
info: 'Cslib.Circuits.Frontier.Sweep.ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Sweep.ncard_le

/--
info: 'Cslib.Circuits.Frontier.Multigraph.card_le_card_add_one_of_connected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.card_le_card_add_one_of_connected

/--
info: 'Cslib.Circuits.Frontier.Network.Satisfies.splice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.Satisfies.splice

/--
info: 'Cslib.Circuits.Frontier.Network.ncard_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.ncard_accepted_le

/--
info: 'Cslib.Circuits.Frontier.RectangleBias.abs_signedCount_le_of_dependsOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.RectangleBias.abs_signedCount_le_of_dependsOn

/--
info: 'Cslib.Circuits.Frontier.ReadOnceNBP.ncard_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.ReadOnceNBP.ncard_accepted_le

/--
info: 'Cslib.Circuits.Frontier.ReadOnceNBP.abs_signedCount_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.ReadOnceNBP.abs_signedCount_accepted_le

/--
info: 'Cslib.Circuits.Frontier.Network.accepted_branchingProgram' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.accepted_branchingProgram

/--
info: 'Cslib.Circuits.Frontier.Network.abs_signedCount_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.abs_signedCount_accepted_le

/--
info: 'Cslib.Circuits.Frontier.eventually_add_lt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_add_lt_of_le

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_of_demand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_of_demand

/--
info: 'Set.ncard_le_mul_ncard_image' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Set.ncard_le_mul_ncard_image

/--
info: 'Fintype.expect_sub_div_le_dens_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.expect_sub_div_le_dens_filter

/--
info: 'Fintype.dens_filter_exists_apply_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.dens_filter_exists_apply_mem

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.expect_trialAgreement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.expect_trialAgreement

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_goodTrials' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.div_two_mul_le_dens_goodTrials

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.half_le_dens_exists_mem_goodTrials' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.half_le_dens_exists_mem_goodTrials

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.reconstructionBits_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.reconstructionBits_le

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.one_sub_pow_le_dens_mem_trialCandidates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.one_sub_pow_le_dens_mem_trialCandidates

/--
info: 'Cslib.ListCode.ListDecodes.exists_decodeBits_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ListCode.ListDecodes.exists_decodeBits_eq_some

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder.etimeBoundedComplexity_le_of_random' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open Cslib.Kolmogorov.DescriptionMethod.ReconstructionDecoder in
#print axioms etimeBoundedComplexity_le_of_random

/--
info: 'Cslib.PCP.HadamardTester.exists_inputDist_div_le_one_sub_acceptProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.exists_inputDist_div_le_one_sub_acceptProb

/--
info: 'Cslib.PCP.HadamardTester.one_div_le_one_sub_acceptProb_of_forall_not' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.one_div_le_one_sub_acceptProb_of_forall_not

/--
info: 'Cslib.PCP.HadamardTester.passes_honestProof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.passes_honestProof

/--
info: 'Cslib.PCP.HadamardTester.exists_inputDist_div_le_unsatFrac' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.exists_inputDist_div_le_unsatFrac

/--
info: 'Cslib.PCP.HadamardTester.forall_hadamardCode_tensor_equationCoeff_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.HadamardTester.forall_hadamardCode_tensor_equationCoeff_iff

/--
info: 'Cslib.BitString.eq_of_hammingDist_longCode_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.eq_of_hammingDist_longCode_lt

/--
info: 'Cslib.PCP.LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.LocalTest.one_sub_acceptProb_le_card_mul_unsatFrac

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_compose

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_compose_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_compose_le

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_compose_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_compose_iff

/--
info: 'Cslib.PCP.ConstraintGraph.card_edges_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.card_edges_compose

/--
info: 'Cslib.PCP.RegularConstraintGraph.satisfiable_power_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.satisfiable_power_iff

/--
info: 'Cslib.PCP.RegularConstraintGraph.not_satisfies_of_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.not_satisfies_of_hit

/--
info: 'Cslib.PCP.RegularConstraintGraph.le_expect_numHits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.le_expect_numHits

/--
info: 'Cslib.PCP.RegularConstraintGraph.expect_numHits_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.expect_numHits_sq_le

/--
info: 'Cslib.PCP.RegularConstraintGraph.le_unsatFrac_power' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.le_unsatFrac_power

/--
info: 'Cslib.PCP.RegularConstraintGraph.le_unsatVal_power_min' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.le_unsatVal_power_min

/--
info: 'Cslib.PCP.RegularConstraintGraph.le_unsatVal_power' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.RegularConstraintGraph.le_unsatVal_power

/--
info: 'Cslib.RotationMap.neighbor_pow_take_rot_killedPow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.neighbor_pow_take_rot_killedPow

/--
info: 'Cslib.Circuits.Frontier.Compiler.satisfies_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.satisfies_iff

/--
info: 'Cslib.Circuits.Frontier.Compiler.connected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.connected

/--
info: 'Cslib.Circuits.Frontier.Compiler.maxDegreeLE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.maxDegreeLE

/--
info: 'Cslib.Circuits.Frontier.Compiler.cycleRank_add_ncard_read_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.cycleRank_add_ncard_read_le

/--
info: 'Cslib.Circuits.Frontier.Compiler.card_vertex_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.card_vertex_le

/--
info: 'Cslib.Circuits.Frontier.Network.logb_ncard_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.logb_ncard_accepted_le

/--
info: 'Cslib.Circuits.Frontier.exists_graph_of_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_graph_of_decides

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_innerSize

/--
info: 'Cslib.Circuits.Circuit.innerSize_le_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.innerSize_le_size

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_of_layoutBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_of_layoutBound

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_of_layoutBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_of_layoutBound

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_two

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_two

/--
info: 'Cslib.Circuits.Frontier.layoutBound_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.layoutBound_one

/--
info: 'Cslib.Circuits.Frontier.LayoutBound.of_cubic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.LayoutBound.of_cubic

/--
info: 'Cslib.Circuits.Frontier.Multigraph.exists_width_le_cycleRank_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.exists_width_le_cycleRank_add

/--
info: 'Cslib.Circuits.Frontier.Multigraph.Compression.exists_width_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.Compression.exists_width_le

/--
info: 'Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.card_blocks_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.card_blocks_le

/--
info: 'Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_threshold_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_threshold_le

/--
info: 'Real.sum_arccos_le_card_mul_arccos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Real.sum_arccos_le_card_mul_arccos

/--
info: 'InnerProductGeometry.sum_offDiag_angle_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InnerProductGeometry.sum_offDiag_angle_le

/--
info: 'InnerProductGeometry.angle_eq_two_mul_arctan' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms InnerProductGeometry.angle_eq_two_mul_arctan

/--
info: 'ProbabilityTheory.gaussianReal_Icc_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.gaussianReal_Icc_le

/--
info: 'ProbabilityTheory.stdGaussian_map_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.stdGaussian_map_inner

/--
info: 'ProbabilityTheory.measurePreserving_toLp_pi_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.measurePreserving_toLp_pi_gaussianReal

/--
info: 'ProbabilityTheory.gaussianReal_prod_setOf_abs_le_mul_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.gaussianReal_prod_setOf_abs_le_mul_abs

/--
info: 'ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_angle

/--
info: 'ProbabilityTheory.variance_sum_indicator_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.variance_sum_indicator_le

/--
info: 'ProbabilityTheory.measureReal_pi_le_abs_sum_indicator_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.measureReal_pi_le_abs_sum_indicator_sub_le

/--
info: 'SimpleGraph.card_edist_le_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SimpleGraph.card_edist_le_le

/--
info: 'Cslib.Circuits.Frontier.Gaussian.le_inner_unitKernelRow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.le_inner_unitKernelRow

/--
info: 'Matrix.isTotallyRegular_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isTotallyRegular_cauchy

/--
info: 'Matrix.isTotallyRegular_cauchyNat_zmod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isTotallyRegular_cauchyNat_zmod

/--
info: 'Cslib.Circuits.Circuit.Computes.exists_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.Computes.exists_affine

/--
info: 'Cslib.Circuits.Frontier.exists_graph_of_isTotallyRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_graph_of_isTotallyRegular

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_isTotallyRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_isTotallyRegular

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_arith_cauchyNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_arith_cauchyNat

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_cauchyNat_zmod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_cauchyNat_zmod

/--
info: 'Cslib.Circuits.Frontier.Network.accepted_hide' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Network.accepted_hide

/--
info: 'Cslib.Circuits.Frontier.Compiler.accepted_hiddenNetwork' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.accepted_hiddenNetwork

/--
info: 'Cslib.Circuits.Frontier.exists_graph_of_nondeterministicDecides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_graph_of_nondeterministicDecides

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_nondeterministicDecides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_nondeterministicDecides

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_of_nondeterministicDecides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_of_nondeterministicDecides

/--
info: 'Cslib.Circuits.DecomposableDAG.ncard_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.DecomposableDAG.ncard_accepted_le

/--
info: 'Cslib.Circuits.DecomposableDAG.ncard_accepted_le_size' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.DecomposableDAG.ncard_accepted_le_size

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_amplify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_amplify

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_amplify_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_amplify_iff

/--
info: 'Cslib.PCP.ConstraintGraph.card_edges_amplify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.card_edges_amplify

/--
info: 'Cslib.PCP.ConstraintGraph.card_vertices_amplify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.card_vertices_amplify

/--
info: 'Cslib.PCP.Dinur.min_le_unsatVal_amplify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.min_le_unsatVal_amplify

/--
info: 'Cslib.PCP.Dinur.satisfiable_amplify_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.satisfiable_amplify_iff

/--
info: 'Cslib.PCP.Amplifier.min_le_unsatVal_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.min_le_unsatVal_iter

/--
info: 'Cslib.PCP.Amplifier.gap_le_unsatVal_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.gap_le_unsatVal_iter

/--
info: 'Cslib.PCP.Amplifier.unsatVal_iter_eq_zero_or_gap_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.unsatVal_iter_eq_zero_or_gap_le

/--
info: 'Cslib.PCP.Amplifier.satisfiable_iter_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.satisfiable_iter_iff

/--
info: 'Cslib.PCP.Amplifier.card_edges_iter_clog_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.card_edges_iter_clog_le

/--
info: 'Cslib.PCP.Amplifier.card_vertices_iter_clog_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Amplifier.card_vertices_iter_clog_le

/--
info: 'Cslib.PCP.Dinur.satisfiable_gapGraph_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.satisfiable_gapGraph_iff

/--
info: 'Cslib.PCP.Dinur.gap_le_unsatVal_gapGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.gap_le_unsatVal_gapGraph

/--
info: 'Cslib.PCP.Dinur.unsatVal_gapGraph_eq_zero_or_gap_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.unsatVal_gapGraph_eq_zero_or_gap_le

/--
info: 'Cslib.PCP.Dinur.exists_card_gapGraph_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Dinur.exists_card_gapGraph_le

/--
info: 'Cslib.Circuits.Frontier.LayoutBound.exists_layout_componentwise' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.LayoutBound.exists_layout_componentwise

/--
info: 'Cslib.Circuits.Frontier.Multigraph.connected_induce_component' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.connected_induce_component

/--
info: 'Cslib.Circuits.Frontier.Compiler.cycleRankOn_add_ncard_readIn_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Compiler.cycleRankOn_add_ncard_readIn_le

/--
info: 'Cslib.Circuits.Frontier.Ledger.run_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.run_eq_trace

/--
info: 'Cslib.Circuits.Frontier.Ledger.run_total_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.run_total_trace

/--
info: 'Cslib.Circuits.Frontier.Ledger.ofAggregates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.ofAggregates

/--
info: 'Cslib.Circuits.Frontier.aggregates_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.aggregates_unbounded

/--
info: 'Cslib.Circuits.Frontier.aggregates_countMod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.aggregates_countMod

/--
info: 'Cslib.Circuits.Frontier.Ledger.mem_of_splice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.mem_of_splice

/--
info: 'Cslib.Circuits.Frontier.Ledger.exists_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Ledger.exists_ncard_le

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger

/--
info: 'Cslib.Circuits.Frontier.eventually_lt_mul_card_of_aggregates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_lt_mul_card_of_aggregates

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_ledger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_ledger

/--
info: 'Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_aggregates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_card_of_aggregates

/--
info: 'Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_edgeScore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_edgeScore

/--
info: 'Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_vertexScore' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_vertexScore

/--
info: 'Cslib.Circuits.Frontier.Multigraph.core_density' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.core_density

/--
info: 'Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.mul_card_external_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.mul_card_external_le

/--
info: 'Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le

/--
info: 'Cslib.Circuits.Frontier.Gaussian.exists_good_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.exists_good_sample

/--
info: 'Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.circuitCoefficient_ge_456

/--
info: 'Cslib.Circuits.Frontier.Gaussian.exists_width_le_gaussianCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.exists_width_le_gaussianCoefficient

/--
info: 'Cslib.Circuits.Frontier.Gaussian.cubicLayoutBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.cubicLayoutBound_gaussian

/--
info: 'Cslib.Circuits.Frontier.layoutBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.layoutBound_gaussian

/--
info: 'Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient

/--
info: 'Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_three_le

/--
info: 'Cslib.Circuits.Frontier.layoutBound_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.layoutBound_degree

/--
info: 'Cslib.Circuits.Frontier.layoutBound_one_third' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.layoutBound_one_third

/--
info: 'Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize

/--
info: 'Cslib.Circuits.Frontier.Gaussian.exists_ncard_edgeCut_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.exists_ncard_edgeCut_le

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_gaussian

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_114_div_25' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_114_div_25

/--
info: 'Cslib.Circuits.Frontier.circuitLowerBound_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.circuitLowerBound_four

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_gaussian

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_114_div_25' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_114_div_25

/--
info: 'Cslib.Circuits.Frontier.averageCaseBound_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.averageCaseBound_four

/--
info: 'Cslib.Circuits.Boolean.Threshold.exists_computes_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Threshold.exists_computes_parity

/--
info: 'Cslib.Circuits.Boolean.Threshold.parity_mem_constDepth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.Threshold.parity_mem_constDepth

/--
info: 'Cslib.Circuits.Boolean.TC0_eq_constDepth_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.TC0_eq_constDepth_threshold

/--
info: 'Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_four

/--
info: 'Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_degreeCoefficient_lt_mul_innerSize

/--
info: 'Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_innerSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_seven_div_two_lt_two_mul_innerSize

/--
info: 'Matrix.sq_sum_bilinear_mul_two_pow_rank_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.sq_sum_bilinear_mul_two_pow_rank_le

/--
info: 'Matrix.exists_submatrixRobust' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_submatrixRobust

/--
info: 'Matrix.SubmatrixRobust.le_cutRank_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.SubmatrixRobust.le_cutRank_add

/--
info: 'Matrix.dotProduct_mulVec_self_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.dotProduct_mulVec_self_eq_add

/--
info: 'Cslib.BitString.quadForm_eq_of_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.quadForm_eq_of_submatrix

/--
info: 'Cslib.Circuits.Frontier.correlation_eq_two_mul_agreement_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.correlation_eq_two_mul_agreement_sub_one

/--
info: 'Cslib.Circuits.Frontier.sq_signedCount_quadForm_rectangle_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_signedCount_quadForm_rectangle_mul_le

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_unread' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_unread

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_layout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_layout

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_unread' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_unread

/--
info: 'Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_layout' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.sq_correlation_quadForm_le_of_layout

/--
info: 'Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le

/--
info: 'Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_of_isLittleO' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_of_isLittleO

/--
info: 'Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_gaussian

/--
info: 'Cslib.Circuits.Frontier.half_le_cutRank_hardMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.half_le_cutRank_hardMatrix

/--
info: 'Cslib.Circuits.Frontier.eventually_abs_correlation_hardForm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.eventually_abs_correlation_hardForm_le

/--
info: 'Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_of_lt

/--
info: 'Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le

/--
info: 'Cslib.Complexity.SigmaP_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SigmaP_zero

/--
info: 'Cslib.Complexity.PiP_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PiP_zero

/--
info: 'Cslib.Complexity.SigmaP_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SigmaP_one

/--
info: 'Cslib.Complexity.PiP_one_eq_coNP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PiP_one_eq_coNP

/--
info: 'Cslib.Complexity.PiP_eq_preimage_compl_SigmaP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PiP_eq_preimage_compl_SigmaP

/--
info: 'Cslib.Complexity.PH_eq_iUnion_PiP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PH_eq_iUnion_PiP

/--
info: 'Cslib.Complexity.P_subset_PH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_subset_PH

/--
info: 'Cslib.Complexity.coNP_subset_PH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coNP_subset_PH

/--
info: 'Cslib.Complexity.not_alternation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.not_alternation

/--
info: 'Cslib.Complexity.BPP_subset_PP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BPP_subset_PP

/--
info: 'Cslib.Complexity.mem_NP_iff_exists_SharpP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_iff_exists_SharpP

/--
info: 'Cslib.Complexity.SharpP.exists_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpP.exists_le_two_pow

/--
info: 'Cslib.Complexity.GapP.neg_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.neg_mem

/--
info: 'Cslib.Complexity.PromiseP_eq_PromiseNP_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PromiseP_eq_PromiseNP_iff

/--
info: 'Cslib.Complexity.mem_PromiseSIZE_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PromiseSIZE_iff

/--
info: 'Cslib.Complexity.mem_PromisePPoly_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_PromisePPoly_iff

/--
info: 'Cslib.Complexity.PCP_mono_randomness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCP_mono_randomness

/--
info: 'Cslib.Complexity.PCP_mono_queries' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCP_mono_queries

/--
info: 'Cslib.Complexity.CookLevin.UNSAT_coNPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.UNSAT_coNPComplete

/--
info: 'Cslib.Complexity.NPHard.compl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NPHard.compl

/--
info: 'Cslib.Logic.PL.QBF.eval_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.QBF.eval_congr

/--
info: 'Cslib.Logic.PL.QBF.eval_eq_of_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.QBF.eval_eq_of_closed

/--
info: 'Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le

/--
info: 'Cslib.Circuits.Frontier.exists_rectangleFree_two_pow_le_ncard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_rectangleFree_two_pow_le_ncard

/--
info: 'Cslib.Circuits.Frontier.exists_rectangleFree_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_rectangleFree_family

/--
info: 'Cslib.Circuits.Frontier.exists_rectangleBias' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_rectangleBias

/--
info: 'Cslib.Circuits.Frontier.exists_rectangleBias_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Frontier.exists_rectangleBias_family

/--
info: 'Cslib.MCSP.mem_iff_exists_circuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.mem_iff_exists_circuit

/--
info: 'Cslib.MCSP.ncard_setOf_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.ncard_setOf_mem

/--
info: 'Cslib.GapMCSP.disjoint_yes_no' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.GapMCSP.disjoint_yes_no

/--
info: 'Cslib.MCSP.mem_of_twelve_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.mem_of_twelve_mul_le

/--
info: 'Cslib.MCSP.ncard_setOf_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.ncard_setOf_mem_le

/--
info: 'Cslib.MCSP.eventually_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.eventually_mem

/--
info: 'Cslib.MCSP.eventually_exists_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.eventually_exists_notMem

/--
info: 'Cslib.SuccinctMCSP.eventually_ofFunction_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.SuccinctMCSP.eventually_ofFunction_mem

/--
info: 'Cslib.MCSP.exists_card_le_sixteen_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.exists_card_le_sixteen_mul

/--
info: 'Cslib.MCSP.exists_isAntiChecker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.exists_isAntiChecker

/--
info: 'Cslib.MCSP.exists_lt_complexityOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.MCSP.exists_lt_complexityOn

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.comp

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWith

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.length

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.range

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoding_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoding_length

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_sub

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mul

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_lt

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pair

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_eval

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_parameters' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_parameters

/--
info: 'Turing.MultiTapeTM.Universal.computableTidilyInO_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.computableTidilyInO_universal

/--
info: 'Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_universal_inPlace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.computableTidilyInTimeAndSpace_universal_inPlace

/--
info: 'Turing.MultiTapeTM.Universal.stateSpace_desc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.stateSpace_desc

/--
info: 'Turing.MultiTapeTM.Universal.simSpace_desc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.simSpace_desc

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_logSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_logSpace

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.filter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.filter

/--
info: 'Cslib.Logic.PL.Literal.computableInPolyTime_negate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Literal.computableInPolyTime_negate

/--
info: 'Cslib.Logic.PL.Clause.computableInPolyTime_impLits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Clause.computableInPolyTime_impLits

/--
info: 'Cslib.Logic.PL.Clause.computableInPolyTime_imp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Clause.computableInPolyTime_imp

/--
info: 'Cslib.Logic.PL.Clause.computableInPolyTime_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.Clause.computableInPolyTime_relabel

/--
info: 'Cslib.Logic.PL.CNF.computableInPolyTime_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableInPolyTime_relabel

/--
info: 'Cslib.Logic.PL.CNF.computableInPolyTime_vars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableInPolyTime_vars

/--
info: 'Cslib.Logic.PL.CNF.computableInPolyTime_atLeastOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableInPolyTime_atLeastOne

/--
info: 'Cslib.Logic.PL.CNF.computableInPolyTime_atMostOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableInPolyTime_atMostOne

/--
info: 'Cslib.Logic.PL.CNF.computableInPolyTime_exactlyOne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.computableInPolyTime_exactlyOne

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_enc_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_enc_eq

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapConst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapConst

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapConst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapConst

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_negSucc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_negSucc

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast_sub

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_succ

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pred

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_pos

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_neg

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_toNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_toNat

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natAbs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natAbs

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_equivNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_equivNat

/--
info: 'Turing.computableTidilyInPolyTime_windowList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.computableTidilyInPolyTime_windowList

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_featureIndex' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_featureIndex

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_inPos' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_inPos

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_head' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_head

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_cell' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_cell

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_holds' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_holds

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_cert' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_cert

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_index' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_index

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_relabel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_relabel

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_initClauses' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_initClauses

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_acceptClauses' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_acceptClauses

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_sitClauses' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_sitClauses

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons'

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend'

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWithInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWithInput

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWithInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWithInput

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_spec

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith_spec

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith_of_bounded_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith_of_bounded_growth

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterate_spec

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_spec

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.polyBounded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.polyBounded

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.allConst' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.allConst

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyConst' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyConst

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_oneHotClauses' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_oneHotClauses

/--
info: 'Cslib.Crypto.GGM.computableTidilyInPolyTime_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GGM.computableTidilyInPolyTime_eval

/--
info: 'Cslib.OracleComp.run_interpret_simulation_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.OracleComp.run_interpret_simulation_of_invariant

/--
info: 'Turing.MultiTapeMachine.run_interpret_runConfigFrom_add_of_halted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.run_interpret_runConfigFrom_add_of_halted

/--
info: 'Turing.MultiTapeMachine.toTM_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.toTM_seq

/--
info: 'Turing.MultiTapeMachine.run_interpret_runConfigFrom_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.run_interpret_runConfigFrom_seq

/--
info: 'Turing.MultiTapePTM.run_interpret_runConfigFrom_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.run_interpret_runConfigFrom_seq

/--
info: 'Turing.MultiTapeMachine.run_interpret_runConfigFrom_mul_indexed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.run_interpret_runConfigFrom_mul_indexed

/--
info: 'Turing.MultiTapeMachine.run_interpret_runConfigFrom_withClock_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.run_interpret_runConfigFrom_withClock_add

/--
info: 'Turing.MultiTapeMachine.withClock_halted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.withClock_halted

/--
info: 'Turing.MultiTapePTM.run_interpret_runConfigFrom_withClock_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.run_interpret_runConfigFrom_withClock_add

/--
info: 'Turing.MultiTapeTM.PolynomialClock.exists_prepare' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.PolynomialClock.exists_prepare

/--
info: 'Turing.MultiTapeMachine.runConfigFrom_embed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.runConfigFrom_embed

/--
info: 'Turing.MultiTapeMachine.toTM_extendTapes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.toTM_extendTapes

/--
info: 'Turing.MultiTapePTM.PolynomialClock.run_interpret_compile' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.PolynomialClock.run_interpret_compile

/--
info: 'Turing.MultiTapePTM.exists_polynomialClock' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.exists_polynomialClock

/--
info: 'Cslib.Probability.IsPPTOn.exists_halting_machine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.exists_halting_machine

/--
info: 'Turing.MultiTapeMachine.runConfigFrom_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.runConfigFrom_map

/--
info: 'Turing.MultiTapeMachine.runConfigFrom_inputFromTape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.runConfigFrom_inputFromTape

/--
info: 'Turing.MultiTapeMachine.runConfigFrom_outputToTape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.runConfigFrom_outputToTape

/--
info: 'Turing.MultiTapeTM.runFrom_prepareInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.runFrom_prepareInput

/--
info: 'Turing.MultiTapePTM.eval_runClosedConfigFrom_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.eval_runClosedConfigFrom_comp

/--
info: 'Turing.MultiTapePTM.comp_halted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.comp_halted

/--
info: 'Cslib.Probability.IsPPTOn.bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.bind

/--
info: 'Turing.MultiTapeMachine.runConfigFrom_prependOutput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeMachine.runConfigFrom_prependOutput

/--
info: 'Turing.MultiTapePTM.eval_runClosedConfigFrom_seq_prependOutput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.eval_runClosedConfigFrom_seq_prependOutput

/--
info: 'Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.runFrom_initCfg_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.runFrom_initCfg_eq

/--
info: 'Cslib.Probability.IsPPTOn.prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.prefix

/--
info: 'Cslib.Probability.IsPPTOn.bind_with' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.bind_with

/--
info: 'Cslib.Probability.IsPPTOn.cond' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.cond

/--
info: 'Cslib.BitString.eval_sampleList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.eval_sampleList

/--
info: 'Turing.MultiTapePTM.eval_uniformListMachine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.eval_uniformListMachine

/--
info: 'Turing.MultiTapePTM.uniformListMachine_halted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.uniformListMachine_halted

/--
info: 'Cslib.Probability.isPPTOn_sampleList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.isPPTOn_sampleList

/--
info: 'Turing.MultiTapePTM.run_interpret_runConfigFrom_eq_coins' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.run_interpret_runConfigFrom_eq_coins

/--
info: 'Turing.MultiTapePTM.eval_runClosedConfigFrom_eq_map_coins' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.eval_runClosedConfigFrom_eq_map_coins

/--
info: 'Turing.MultiTapePTM.runClosedCoins_mem_support' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.runClosedCoins_mem_support

/--
info: 'Turing.MultiTapePTM.runFrom_replay' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.runFrom_replay

/--
info: 'Turing.MultiTapeTM.PairEncoding.exists_prepare' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.PairEncoding.exists_prepare

/--
info: 'Turing.MultiTapePTM.computableTidilyInLinearTimeAndSpace_runClosedCoins' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.computableTidilyInLinearTimeAndSpace_runClosedCoins

/--
info: 'Turing.MultiTapePTM.computableTidilyInPolyTime_runClosedCoins' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.computableTidilyInPolyTime_runClosedCoins

/--
info: 'Cslib.Probability.IsPPTOn.exists_polyTime_coin_evaluator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.exists_polyTime_coin_evaluator

/--
info: 'Cslib.Probability.IsPPTOn.exists_total_seeded_evaluator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.exists_total_seeded_evaluator

/--
info: 'Cslib.Probability.IsPPTOn.exists_seeded_evaluator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.exists_seeded_evaluator

/--
info: 'Cslib.Probability.IsPPTOn.exists_padded_bool_coin_evaluator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.exists_padded_bool_coin_evaluator

/--
info: 'Cslib.BitString.uniformList_listRows' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.uniformList_listRows

/--
info: 'Cslib.ProbComp.eval_iterate_of_uniform' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ProbComp.eval_iterate_of_uniform

/--
info: 'Cslib.Probability.IsPPTOn.iterate_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.iterate_spec

/--
info: 'Cslib.Probability.IsPPTOn.iterateWith_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.iterateWith_spec

/--
info: 'Cslib.Probability.IsPPTOn.iterateWith_of_bounded_growth' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.iterateWith_of_bounded_growth

/--
info: 'Cslib.Probability.IsPPTOn.iterate_of_bounded_growth' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.iterate_of_bounded_growth

/--
info: 'Cslib.Crypto.Game.Indistinguishable.of_reduction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Game.Indistinguishable.of_reduction

/--
info: 'Cslib.Crypto.ComputationallyIndistinguishable.bind' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.ComputationallyIndistinguishable.bind

/--
info: 'Cslib.Crypto.PRG.Family.secure_iff_indistinguishable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.Family.secure_iff_indistinguishable

/--
info: 'Cslib.Crypto.isPPT_inversionGame' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.isPPT_inversionGame

/--
info: 'Cslib.Crypto.not_oneWay_of_inverse' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.not_oneWay_of_inverse

/--
info: 'Cslib.Crypto.PRG.wordFamily_secure_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.wordFamily_secure_iff

/--
info: 'Cslib.Crypto.isPPT_hardCorePredictor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.isPPT_hardCorePredictor

/--
info: 'Cslib.Crypto.hardCore_advantage_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.hardCore_advantage_le

/--
info: 'Cslib.Crypto.OneWayPermutation.pseudorandomGenerator_of_hardCore' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.OneWayPermutation.pseudorandomGenerator_of_hardCore

/--
info: 'Cslib.Probability.PMF.uniformOfFintype_map_sum_pair' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.uniformOfFintype_map_sum_pair

/--
info: 'Cslib.Probability.majority_error_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.majority_error_bound

/--
info: 'Cslib.Crypto.GoldreichLevin.decode_failure_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.decode_failure_le

/--
info: 'Cslib.Crypto.GoldreichLevin.decode_failure_le_half' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.decode_failure_le_half

/--
info: 'Cslib.Crypto.GoldreichLevin.card_le_of_mem_support_decode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.card_le_of_mem_support_decode

/--
info: 'Cslib.Crypto.GoldreichLevin.candidate_parity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.candidate_parity

/--
info: 'Cslib.Crypto.GoldreichLevin.checkCandidates_correct' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.checkCandidates_correct

/--
info: 'Cslib.Crypto.GoldreichLevin.invert_success_ge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.invert_success_ge

/--
info: 'Cslib.Crypto.GoldreichLevin.invertSigned_success_ge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.invertSigned_success_ge

/--
info: 'Cslib.Crypto.GoldreichLevin.guessCount_polynomial' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.guessCount_polynomial

/--
info: 'Cslib.Crypto.GoldreichLevin.negligible_prediction_of_negligible_inversion' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GoldreichLevin.negligible_prediction_of_negligible_inversion

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsEnumList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsEnumList

/--
info: 'Cslib.Crypto.GoldreichLevin.polyTime_wordDecode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GoldreichLevin.polyTime_wordDecode

/--
info: 'Cslib.Crypto.GoldreichLevin.uniform_wordDecode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GoldreichLevin.uniform_wordDecode

/--
info: 'Cslib.Crypto.GoldreichLevin.wordDecode_success_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GoldreichLevin.wordDecode_success_ge_half

end ComplexityTests.Axioms

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div_const

/--
info: 'Cslib.Crypto.Negligible.comp_of_polynomial_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Negligible.comp_of_polynomial_bound

/--
info: 'Cslib.Crypto.GoldreichLevin.isPPT_wordInverter' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GoldreichLevin.isPPT_wordInverter

/--
info: 'Cslib.Crypto.GoldreichLevin.negligible_parityPrediction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GoldreichLevin.negligible_parityPrediction

/--
info: 'Cslib.Crypto.GoldreichLevin.padded_hardCore' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GoldreichLevin.padded_hardCore

/--
info: 'Cslib.Crypto.OneWayPermutation.pseudorandomGenerator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.OneWayPermutation.pseudorandomGenerator

/--
info: 'Cslib.BitString.uniformList_binaryValue' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.uniformList_binaryValue

/--
info: 'Cslib.ProbComp.eval_sampleBoundedIndex' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbComp.eval_sampleBoundedIndex

/--
info: 'Cslib.Probability.isPPTOn_sampleBoundedIndex' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.isPPTOn_sampleBoundedIndex

/--
info: 'Cslib.Probability.isPPTOn_sampleDyadicCoin' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.isPPTOn_sampleDyadicCoin

/--
info: 'Cslib.Crypto.PRGStretch.advantage_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.PRGStretch.advantage_eq

/--
info: 'Cslib.Crypto.PRGStretch.indexed_indistinguishable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.PRGStretch.indexed_indistinguishable

/--
info: 'Cslib.Crypto.PseudorandomGenerator.amplify' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.PseudorandomGenerator.amplify

/--
info: 'Cslib.Crypto.PseudorandomGenerator.truncate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.PseudorandomGenerator.truncate

/--
info: 'Cslib.Crypto.PRGStretch.polyTime_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.PRGStretch.polyTime_iterate

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_of_bounded_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_of_bounded_growth

/--
info: 'Cslib.RandomOracle.run_interpret_answer_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.run_interpret_answer_complete

/--
info: 'Cslib.RandomOracle.uniform_interpret_eq_lazy' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.uniform_interpret_eq_lazy

/--
info: 'Cslib.RandomOracle.run_interpret_memoize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.run_interpret_memoize

/--
info: 'Cslib.RandomOracle.memoize_cache_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.memoize_cache_bounds

/--
info: 'Cslib.RandomOracle.eval_run_interpret_memoize_eq_eager' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.eval_run_interpret_memoize_eq_eager

/--
info: 'Cslib.Probability.PMF.pi_bind_update_pair' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.pi_bind_update_pair

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

/--
info: 'Cslib.RandomOracle.run_interpret_answer_complete_prob' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.run_interpret_answer_complete_prob

/--
info: 'Cslib.RandomOracle.uniform_interpret_prob_eq_lazy' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.uniform_interpret_prob_eq_lazy

/--
info: 'Cslib.Probability.IsOraclePPTOn.length_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsOraclePPTOn.length_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.isOraclePPTOn' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.isOraclePPTOn

/--
info: 'Turing.MultiTapePTM.run_interpret_runOracle_ofDeterministic' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapePTM.run_interpret_runOracle_ofDeterministic

/--
info: 'Cslib.Probability.IsOraclePPTOn.query_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsOraclePPTOn.query_bounds

/--
info: 'Turing.MultiTapePTM.query_bounds_runFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapePTM.query_bounds_runFrom

/--
info: 'Turing.MultiTapePTM.query_bounds_runOracle' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapePTM.query_bounds_runOracle

/--
info: 'Cslib.ProbOracleComp.run_interpret_simulation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbOracleComp.run_interpret_simulation

/-- info: 'Cslib.OracleComp.IsCostBounded.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.OracleComp.IsCostBounded.bind

/--
info: 'Cslib.ProbOracleComp.isCostBounded_iff_transcript_cost_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbOracleComp.isCostBounded_iff_transcript_cost_le

/--
info: 'Cslib.Probability.IsPPTOn.memoize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsPPTOn.memoize

/--
info: 'Cslib.Probability.memoize_call_size_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.memoize_call_size_le

/--
info: 'Cslib.Probability.memoize_cache_growth_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.memoize_cache_growth_le

/--
info: 'Cslib.Probability.memoize_cache_size_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.memoize_cache_size_le

/--
info: 'Cslib.RandomOracle.memoize_cache_bounds_prob' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.memoize_cache_bounds_prob

/--
info: 'Cslib.RandomOracle.eval_run_interpret_memoize_prob_eq_eager' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.RandomOracle.eval_run_interpret_memoize_prob_eq_eager

/--
info: 'Cslib.Crypto.GGM.hybridGame_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.hybridGame_zero

/--
info: 'Cslib.Crypto.GGM.hybridGame_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.hybridGame_self

/--
info: 'Cslib.Crypto.GGM.frontierOracle_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.frontierOracle_bounds

/--
info: 'Cslib.Crypto.GGM.isPPTOn_hybridGame' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.isPPTOn_hybridGame

/--
info: 'Cslib.ProbOracleComp.run_interpret_map_state_of_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbOracleComp.run_interpret_map_state_of_invariant

/--
info: 'Cslib.Crypto.GGM.expansionGame_generated' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.expansionGame_generated

/--
info: 'Cslib.Crypto.GGM.expansionGame_uniform' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.expansionGame_uniform

/--
info: 'Cslib.Crypto.GGM.expansionOracle_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.expansionOracle_bounds

/--
info: 'Cslib.Crypto.GGM.isPPTOn_expansionGame' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.isPPTOn_expansionGame

/--
info: 'Cslib.Probability.IsPPTOn.replicate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsPPTOn.replicate

/--
info: 'Cslib.ProbOracleComp.IsQueryBounded.run_interpret_presample' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbOracleComp.IsQueryBounded.run_interpret_presample

/--
info: 'Cslib.ProbOracleComp.IsQueryBounded.eval_presample' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbOracleComp.IsQueryBounded.eval_presample

/--
info: 'Cslib.Probability.IsOraclePPTOn.run_interpret_withSampleList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsOraclePPTOn.run_interpret_withSampleList

/--
info: 'Cslib.Crypto.sequenceTest_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.sequenceTest_gap

/--
info: 'Cslib.Crypto.GGM.sampleGame_replicate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.sampleGame_replicate

/--
info: 'Cslib.Crypto.GGM.isPPT_reduction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.isPPT_reduction

/--
info: 'Cslib.Crypto.GGM.reduction_advantage' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.reduction_advantage

/--
info: 'Cslib.Crypto.GGM.pseudorandomFunction_of_indistinguishable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.GGM.pseudorandomFunction_of_indistinguishable

/--
info: 'Cslib.Crypto.PseudorandomGenerator.exists_pseudorandomFunction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.PseudorandomGenerator.exists_pseudorandomFunction

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_inputClauses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_inputClauses

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_readClauses' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_readClauses

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_stepClauses' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_stepClauses

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_tableau' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_tableau

/--
info: 'Cslib.Complexity.CookLevin.computableInPolyTime_reduce' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.CookLevin.computableInPolyTime_reduce

/--
info: 'Cslib.Complexity.CookLevin.SAT_npHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Complexity.CookLevin.SAT_npHard

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapFilterConst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapFilterConst

/--
info: 'Cslib.Crypto.OneWay.normalize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.OneWay.normalize

/--
info: 'Cslib.Crypto.OneWay.exists_fixedOutputLength' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.OneWay.exists_fixedOutputLength

/--
info: 'Cslib.Crypto.OneWayNormalization.inversion_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.OneWayNormalization.inversion_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsPadWord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsPadWord

/--
info: 'Cslib.Probability.PMF.bind_apply_mono_on_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.bind_apply_mono_on_support

/--
info: 'Cslib.BitString.word_eq_of_padWord_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Cslib.BitString.word_eq_of_padWord_eq

/--
info: 'Cslib.Probability.PMF.bind_conditionalSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.bind_conditionalSnd

/--
info: 'Cslib.Probability.PMF.conditionalSnd_uniform_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.conditionalSnd_uniform_map

/--
info: 'Cslib.Probability.PMF.conditionalSnd_pi_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.conditionalSnd_pi_joint

/--
info: 'Cslib.Probability.PMF.collisionProbability_eq_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.collisionProbability_eq_probability

/--
info: 'Cslib.Probability.PMF.dist_uniform_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.dist_uniform_le

/--
info: 'Cslib.Crypto.output_collision_eq_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.output_collision_eq_inversion

/--
info: 'Cslib.Crypto.OneWay.output_collision_negligible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.OneWay.output_collision_negligible

/--
info: 'Cslib.Probability.PMF.entropy_bind_sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.entropy_bind_sigma

/--
info: 'Cslib.Probability.PMF.conditionalEntropy_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.conditionalEntropy_eq_sum

/--
info: 'Cslib.Probability.PMF.conditionalEntropy_map_fst_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.conditionalEntropy_map_fst_ge

/--
info: 'Cslib.Probability.PMF.conditionalEntropy_map_le_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.conditionalEntropy_map_le_collision

/--
info: 'Cslib.Probability.PMF.entropy_chain_rule_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.entropy_chain_rule_deterministic

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_predictionGame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_predictionGame

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_error_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_error_ge

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_entropy_add_gap_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_entropy_add_gap_le_one

/--
info: 'Cslib.Probability.PMF.pi_sum_le_mean_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.pi_sum_le_mean_sub

/--
info: 'Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge

/--
info: 'Cslib.Probability.PMF.pi_conditional_mass_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.pi_conditional_mass_gt

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.exists_observationBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.exists_observationBound

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.exists_seedRealization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.exists_seedRealization

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.isPPTOn_sampleWithSeed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.isPPTOn_sampleWithSeed

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.eval_sampleWithSeed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.eval_sampleWithSeed

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.entropy_chain_rule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.entropy_chain_rule

/--
info: 'Cslib.Probability.PMF.dist_bind_pair_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.dist_bind_pair_sq_le

/--
info: 'Cslib.Probability.IsTwoUniversal.collision_with_set_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsTwoUniversal.collision_with_set_le

/--
info: 'Cslib.Probability.IsTwoUniversal.leftover_hash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsTwoUniversal.leftover_hash

/--
info: 'Cslib.Probability.IsTwoUniversal.leftover_hash_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsTwoUniversal.leftover_hash_conditional

/--
info: 'Cslib.Probability.IsTwoUniversal.conditionalEntropy_hash_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsTwoUniversal.conditionalEntropy_hash_le

/--
info: 'Cslib.Probability.conditionalEntropy_random_hash_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.conditionalEntropy_random_hash_le

-- Linear hashing, the complete sampler, and its uniform efficiency certificates.

/--
info: 'Cslib.BitString.LinearHash.isTwoUniversal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.LinearHash.isTwoUniversal

/--
info: 'Cslib.BitString.LinearHash.wordHash_eq_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.LinearHash.wordHash_eq_ofFn

/--
info: 'Cslib.BitString.LinearHash.eval_extract_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.LinearHash.eval_extract_bind

/--
info: 'Cslib.BitString.LinearHash.eval_extract_replicate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.LinearHash.eval_extract_replicate

/--
info: 'Cslib.BitString.LinearHash.extract_dist_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.LinearHash.extract_dist_bind_le

/--
info: 'Cslib.BitString.LinearHash.computableTidilyInPolyTime_wordHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.LinearHash.computableTidilyInPolyTime_wordHash

/--
info: 'Cslib.BitString.LinearHash.isPPTOn_extract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.LinearHash.isPPTOn_extract

/--
info: 'Cslib.ProbComp.eval_replicate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbComp.eval_replicate

-- Complete uniform OWF-to-pseudoentropy reduction, including the executable joint laws.

/--
info: 'Cslib.Probability.score_le_uniform_guess' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.score_le_uniform_guess

/--
info: 'Cslib.Crypto.Pseudoentropy.correlation_le_guessInverter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.correlation_le_guessInverter

/--
info: 'Cslib.Crypto.Pseudoentropy.matrixPrediction_entropy_le_of_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.matrixPrediction_entropy_le_of_coins

/--
info: 'Cslib.Crypto.Pseudoentropy.HashPair.eval_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.HashPair.eval_sample

/--
info: 'Cslib.Crypto.Pseudoentropy.HashPair.isPPTOn_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.HashPair.isPPTOn_sample

/--
info: 'Cslib.Crypto.Pseudoentropy.HashPair.wordInverter_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.HashPair.wordInverter_eval

/--
info: 'Cslib.Crypto.Pseudoentropy.HashPair.isPPT_wordInverter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.HashPair.isPPT_wordInverter

/--
info: 'Cslib.Crypto.Pseudoentropy.HashPair.word_prediction_entropy_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.Pseudoentropy.HashPair.word_prediction_entropy_le

/--
info: 'Cslib.Crypto.OneWay.exists_pseudoentropyPair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.OneWay.exists_pseudoentropyPair

-- Independent empirical probability estimates and their complete uniform PPT certificates.

/--
info: 'Cslib.ProbComp.eval_countTrue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbComp.eval_countTrue

/--
info: 'Cslib.ProbComp.countTrue_average_deviation_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbComp.countTrue_average_deviation_pow

/--
info: 'Cslib.ProbComp.replicate_failure_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbComp.replicate_failure_pow

/--
info: 'Cslib.ProbComp.testProbabilityLT_error_pow_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ProbComp.testProbabilityLT_error_pow_of_bounds

/--
info: 'Cslib.Probability.IsPPTOn.countTrue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsPPTOn.countTrue

/--
info: 'Cslib.Probability.IsPPTOn.testProbabilityLT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.IsPPTOn.testProbabilityLT

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_const

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_clog_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_clog_const

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow_clog_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow_clog_const

-- Waring term counts and shared-gate accounting on native sum-of-terms circuits.

/--
info: 'Cslib.Circuits.Waring.centralBinom_le_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Waring.centralBinom_le_card

/--
info: 'Cslib.Circuits.Waring.four_pow_lt_mul_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Waring.four_pow_lt_mul_cost

/--
info: 'Cslib.Circuits.SumOfTerms.rank_trace_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.SumOfTerms.rank_trace_le

-- Source-adjusted Hessians and the all-characteristic bilinear pairing bound.

/--
info: 'Cslib.Circuits.Program.exists_hessian_residual' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.exists_hessian_residual

/--
info: 'Cslib.Circuits.Circuit.exists_helper_hessian_residual' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.exists_helper_hessian_residual

/--
info: 'Cslib.Circuits.Circuit.pairing_le_mulCost' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.pairing_le_mulCost


-- Weighted supplied-source complexity and the minimum-cost Hessian bounds.

/--
info: 'Cslib.Circuits.ecomplexityFrom_le_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_le_iff

/--
info: 'Cslib.Circuits.ecomplexityFrom_comp_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_comp_le

/--
info: 'Cslib.Circuits.ecomplexityFrom_unit_subtype' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_unit_subtype

/--
info: 'Cslib.Circuits.ecomplexityFrom_unit_append' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_unit_append

/--
info: 'Cslib.Circuits.hessianResidualRank_le_two_mul_ecomplexityFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.hessianResidualRank_le_two_mul_ecomplexityFrom

/--
info: 'Cslib.Circuits.hessianResidualRank_le_two_mul_ecomplexityFrom_with_helpers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.hessianResidualRank_le_two_mul_ecomplexityFrom_with_helpers

/--
info: 'Cslib.Circuits.le_ecomplexityFrom_of_hessian_rank' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.le_ecomplexityFrom_of_hessian_rank

/--
info: 'Cslib.Circuits.CyclicCircuit.evalGates_fixed' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.CyclicCircuit.evalGates_fixed

/--
info: 'Cslib.Circuits.CyclicCircuit.evalGates_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.CyclicCircuit.evalGates_le

/--
info: 'Cslib.Circuits.Circuit.eval_toCyclic' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.eval_toCyclic

/--
info: 'Cslib.Circuits.Circuit.cost_toCyclic' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_toCyclic

/--
info: 'Cslib.Circuits.CyclicCircuit.ecomplexityFrom_ne_top_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.CyclicCircuit.ecomplexityFrom_ne_top_iff

/--
info: 'Cslib.Circuits.CyclicCircuit.ecomplexityFrom_le_acyclic' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.CyclicCircuit.ecomplexityFrom_le_acyclic

/--
info: 'Cslib.Circuits.Fusion.Atom.semifilter_of_mem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.Atom.semifilter_of_mem

/--
info: 'Cslib.Circuits.Fusion.PairCover.ofCyclicCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.ofCyclicCircuit

/--
info: 'Cslib.Circuits.Fusion.PairCover.length_ofCyclicCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.length_ofCyclicCircuit

/--
info: 'Cslib.Circuits.Fusion.pairCoverComplexity_le_cyclic_ecomplexityFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.pairCoverComplexity_le_cyclic_ecomplexityFrom

/--
info: 'Cslib.Circuits.Fusion.PairDerivation.le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairDerivation.le

/--
info: 'Cslib.Circuits.Fusion.PairDerivation.mem_of_outside' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairDerivation.mem_of_outside

/--
info: 'Cslib.Circuits.Fusion.PairCover.derives_empty_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.derives_empty_iff

/--
info: 'Cslib.Circuits.Fusion.PairCover.ofDerivesEmpty' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.ofDerivesEmpty

/--
info: 'Cslib.Circuits.Fusion.pairClosure_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.pairClosure_le

/--
info: 'Cslib.Circuits.Fusion.PairCover.pairClosure_empty' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.pairClosure_empty

/--
info: 'Cslib.Circuits.Program.evalGates_feedback' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.evalGates_feedback

/--
info: 'Cslib.Circuits.Program.eval_feedback_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.eval_feedback_le

/--
info: 'Cslib.Circuits.Circuit.eval_feedback_eq_lfp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.eval_feedback_eq_lfp

/--
info: 'Cslib.Circuits.Circuit.cost_feedback' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_feedback

/--
info: 'Cslib.Circuits.Fusion.PairClosureCompiler.readState_pairValues' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairClosureCompiler.readState_pairValues

/--
info: 'Cslib.Circuits.Fusion.PairClosureCompiler.eval_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairClosureCompiler.eval_circuit

/--
info: 'Cslib.Circuits.Fusion.PairCover.cost_toCyclic' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.cost_toCyclic

/--
info: 'Cslib.Circuits.Fusion.PairCover.eval_toCyclic' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.PairCover.eval_toCyclic

/--
info: 'Cslib.Circuits.Fusion.pairCoverComplexity_eq_cyclic_ecomplexityFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Fusion.pairCoverComplexity_eq_cyclic_ecomplexityFrom

/--
info: 'Cslib.BitString.listVoteMargin_cons' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.listVoteMargin_cons

/--
info: 'Cslib.BitString.listStrictMajority_eq_of_pos' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.listStrictMajority_eq_of_pos

/--
info: 'Cslib.BitString.listNonpositiveMargin_eq_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.listNonpositiveMargin_eq_true

/--
info: 'Cslib.BitString.listStrictMajority_error_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.listStrictMajority_error_le

/--
info: 'Cslib.BitString.map_listNonpositiveMargin_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.map_listNonpositiveMargin_true

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsNonpositiveMarginWithInput' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsNonpositiveMarginWithInput

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsStrictMajorityWithInput' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsStrictMajorityWithInput

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.potential_le_quadratic' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.potential_le_quadratic

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.potential_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.potential_lower_bound

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.step_progress' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.step_progress

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.dense_margin_of_iterations' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.dense_margin_of_iterations

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.clock_sufficient' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.clock_sufficient

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.eval_sampleWeight_true' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.eval_sampleWeight_true

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.sampleWeight_density_deviation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.sampleWeight_density_deviation

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.isPolyTime_weightNumerator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.isPolyTime_weightNumerator

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_sampleWeight' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_sampleWeight

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSample_entropy_ge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSample_entropy_ge

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSequence_prediction_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSequence_prediction_gap

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_maskedSequencePredictor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_maskedSequencePredictor

/--
info: 'Cslib.Probability.PMF.toOuterMeasure_bind_failure_toReal_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.toOuterMeasure_bind_failure_toReal_le

/--
info: 'Cslib.ProbComp.iterate_failure_toReal_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ProbComp.iterate_failure_toReal_le_mul

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.testMajority_source_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.testMajority_source_sound

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.testShift_weights_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.testShift_weights_sound

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.run_bounded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.run_bounded

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_round' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_round

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_run

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.State.Invariant.shift_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.State.Invariant.shift_add

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.round_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.round_sound

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.run_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.run_invariant

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.run_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.run_sound

/--
info: 'Cslib.Probability.PMF.exists_lowerTail' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.exists_lowerTail

/--
info: 'Cslib.ProbComp.selectBest_error_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ProbComp.selectBest_error_pow

/--
info: 'Cslib.ProbComp.selectBest_test_error_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ProbComp.selectBest_test_error_le

/--
info: 'Cslib.ProbComp.selectFrom_error_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ProbComp.selectFrom_error_pow

/--
info: 'Cslib.ProbComp.sampleBest_error_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ProbComp.sampleBest_error_pow

/--
info: 'Cslib.ProbComp.sampleBest_support' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ProbComp.sampleBest_support

/--
info: 'Cslib.Probability.IsPPTOn.selectBest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.selectBest

/--
info: 'Cslib.Probability.IsPPTOn.selectFrom' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.selectFrom

/--
info: 'Cslib.Probability.IsPPTOn.sampleBest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsPPTOn.sampleBest

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.eval_clippedPredict_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.eval_clippedPredict_correct

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.exists_dyadic_clippedError_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.exists_dyadic_clippedError_le

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_clippedPredict' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_clippedPredict

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.selectSlope_dense_margin' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.selectSlope_dense_margin

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.State.Successful.selectSlope_advantage' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.State.Successful.selectSlope_advantage

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_train' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_train

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_predict' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_predict

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.train_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.train_sound

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.train_predict_error' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.train_predict_error

/--
info: 'Cslib.Probability.PMF.toOuterMeasure_rate_ge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.toOuterMeasure_rate_ge

/--
info: 'Cslib.Probability.PMF.dist_filter' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.PMF.dist_filter

/--
info: 'Cslib.Crypto.negligible_geometric' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.negligible_geometric

/--
info: 'Cslib.Crypto.Game.advantage_eq_nndist' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Game.advantage_eq_nndist

/--
info: 'Cslib.Probability.IsTwoUniversal.leftover_hash_of_heavy_probability' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsTwoUniversal.leftover_hash_of_heavy_probability

/--
info: 'Cslib.Probability.IsTwoUniversal.leftover_hash_pi_conditional' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Probability.IsTwoUniversal.leftover_hash_pi_conditional

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.randomSign_good_probability' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.randomSign_good_probability

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.learn_goodPredictor_error_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.learn_goodPredictor_error_pow

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.learn_length_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.learn_length_le

/--
info: 'Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_learn' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.Boosting.isPPTOn_learn

/--
info: 'Cslib.Crypto.Pseudoentropy.ExtractionSchedule.error_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ExtractionSchedule.error_le

/--
info: 'Cslib.Crypto.Pseudoentropy.ExtractionSchedule.error_negligible' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ExtractionSchedule.error_negligible

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_extractLabels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_extractLabels

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_extractLabels_list' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_extractLabels_list

/--
info: 'Cslib.Crypto.Pseudoentropy.extractLabels_dist_bind_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.extractLabels_dist_bind_le

/--
info: 'Cslib.Crypto.Pseudoentropy.extractLabels_indistinguishable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.extractLabels_indistinguishable

/--
info: 'Cslib.Crypto.Pseudoentropy.seededHash_replicate_indistinguishable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.seededHash_replicate_indistinguishable

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSequence_validation_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSequence_validation_gap

/--
info: 'Cslib.Crypto.Pseudoentropy.extractedSequence_learn_error_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.extractedSequence_learn_error_pow

/--
info: 'Cslib.Crypto.SavedPrediction.eval_sample' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.SavedPrediction.eval_sample

/--
info: 'Cslib.Crypto.SavedPrediction.exists_evaluator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.SavedPrediction.exists_evaluator

/--
info: 'Cslib.Crypto.SavedPrediction.length_sample_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.SavedPrediction.length_sample_le

/--
info: 'Cslib.Crypto.SavedPrediction.isPPTOn_sample' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.SavedPrediction.isPPTOn_sample

/--
info: 'Cslib.Crypto.SavedPrediction.isPolyTime_evaluate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.SavedPrediction.isPolyTime_evaluate

/--
info: 'Cslib.Crypto.Pseudoentropy.SequenceLearner.isPPTOn_predict' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SequenceLearner.isPPTOn_predict

/--
info: 'Cslib.Crypto.Pseudoentropy.SequenceLearner.exists_evaluator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SequenceLearner.exists_evaluator

/--
info: 'Cslib.Crypto.Pseudoentropy.SequenceLearner.learn_goodPredictor_error' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SequenceLearner.learn_goodPredictor_error

/--
info: 'Cslib.Crypto.Pseudoentropy.SequenceLearner.predict_error' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SequenceLearner.predict_error

/--
info: 'Cslib.Crypto.Pseudoentropy.SequenceLearner.predict_extracted_error' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SequenceLearner.predict_extracted_error

/--
info: 'Cslib.Crypto.Pseudoentropy.SequenceLearner.failureBound_negligible' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SequenceLearner.failureBound_negligible

/--
info: 'Cslib.Crypto.Pseudoentropy.SequenceLearner.failureBound_eventually_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SequenceLearner.failureBound_eventually_le

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.eval_latentSample' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.eval_latentSample

/--
info: 'Cslib.ProbComp.eval_replicate_congr' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.ProbComp.eval_replicate_congr

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSample_map_fst' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSample_map_fst

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSample_mass_ge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSample_mass_ge

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSample_dyadic_mass_ge_eventually' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSample_dyadic_mass_ge_eventually

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSample_weight_mass_ge_eventually' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSample_weight_mass_ge_eventually

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSample_extract_dist_bind_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSample_extract_dist_bind_le

/--
info: 'Cslib.Crypto.Pseudoentropy.maskedSample_weight_extract_dist_bind_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.maskedSample_weight_extract_dist_bind_le

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_selectPredictor' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_selectPredictor

/--
info: 'Cslib.Crypto.Pseudoentropy.selectPredictor_error_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.selectPredictor_error_le

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_indexed_error_ge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_indexed_error_ge

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_exists_indexed_mask' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_exists_indexed_mask

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_exists_mask' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.eventually_exists_mask

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFlatten' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFlatten

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.eval_latentSampleWithSeed' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.eval_latentSampleWithSeed

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_extractMatrixLabels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_extractMatrixLabels

/--
info: 'Cslib.Crypto.Pseudoentropy.eval_extractMatrixLabels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.eval_extractMatrixLabels

/--
info: 'Cslib.Crypto.Pseudoentropy.eval_extractMatrixLabelsIdeal_append' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.eval_extractMatrixLabelsIdeal_append

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.indexed_extracted_advantage_negligible' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.indexed_extracted_advantage_negligible

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_indexed_labels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_indexed_labels

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.observation_extraction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.observation_extraction

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.observation_word_extraction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.observation_word_extraction

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.remainingSeed_extraction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.remainingSeed_extraction

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.remainingSeed_word_extraction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.remainingSeed_word_extraction

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_extractWordLabels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_extractWordLabels

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_extractedWordTest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_extractedWordTest

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_indexed_word_labels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_indexed_word_labels

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_word_labels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_word_labels

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_extractWordObservations' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_extractWordObservations

/--
info: 'Cslib.Crypto.Pseudoentropy.isPPTOn_extractWordSeeds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.isPPTOn_extractWordSeeds

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.extract_word_observations' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.extract_word_observations

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.extract_word_seeds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.extract_word_seeds

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_divMod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_divMod

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_div

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mod

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_size' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_size

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_scale' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_scale

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_observationBits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_observationBits

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_labelBits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_labelBits

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_remainingBits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_remainingBits

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_numerator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_numerator

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.expands' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.expands

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.label_budget' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.label_budget

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_valid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_valid

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.isPPTOn_extract' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.isPPTOn_extract

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.length_extract' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.length_extract

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.isPolyTime_seedLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.isPolyTime_seedLength

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.isPolyTime_outputLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.isPolyTime_outputLength

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.seedLength_lt_outputLength_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.seedLength_lt_outputLength_iff

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.replace_remaining' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.replace_remaining

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.replace_observations' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.replace_observations

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.replace_indexed_labels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.replace_indexed_labels

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_indexed_three' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_indexed_three

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_three' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.extract_three

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.isPolyTime_hashSamples' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.isPolyTime_hashSamples

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.isPolyTime_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.isPolyTime_generate

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.generate_distribution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.generate_distribution

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.eval_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.eval_generate

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.length_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.length_generate

/--
info: 'Cslib.Crypto.Pseudoentropy.ThreeSource.eval_generate_of_realization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.ThreeSource.eval_generate_of_realization

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_finMod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_finMod

/--
info: 'Cslib.RotationMap.TowerTable.polytime_lookup' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.polytime_lookup

/--
info: 'Cslib.RotationMap.TowerTable.polytime_nextRow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.polytime_nextRow

/--
info: 'Cslib.RotationMap.TowerTable.polytime_next' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.polytime_next

/--
info: 'Cslib.RotationMap.TowerTable.length_encoding_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.length_encoding_le

/--
info: 'Cslib.RotationMap.TowerTable.polytime_build' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.polytime_build

/--
info: 'Cslib.RotationMap.TowerTable.valid_initial' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.valid_initial

/--
info: 'Cslib.RotationMap.TowerTable.Valid.lookup_lt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.Valid.lookup_lt

/--
info: 'Cslib.RotationMap.TowerTable.Valid.next' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.Valid.next

/--
info: 'Cslib.RotationMap.TowerTable.length_iterate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.length_iterate

/--
info: 'Cslib.RotationMap.TowerTable.valid_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.valid_iterate

/--
info: 'Cslib.RotationMap.TowerTable.lookup_iterate_numbered' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.lookup_iterate_numbered

/--
info: 'Cslib.RotationMap.TowerTable.length_build' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.length_build

/--
info: 'Cslib.RotationMap.TowerTable.lookup_build' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.lookup_build

/--
info: 'Cslib.RotationMap.TowerTable.contract_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.contract_eq

/--
info: 'Cslib.RotationMap.TowerTable.rotateFamily_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.rotateFamily_eq

/--
info: 'Cslib.RotationMap.TowerTable.polytime_contract' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.polytime_contract

/--
info: 'Cslib.RotationMap.TowerTable.polytime_rotateFamily' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.TowerTable.polytime_rotateFamily

/--
info: 'Cslib.RotationMap.arithmeticExpanderRotate_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.arithmeticExpanderRotate_eq

/--
info: 'Cslib.RotationMap.polytime_arithmeticExpanderRotate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.polytime_arithmeticExpanderRotate

/--
info: 'Cslib.PCP.Encoded.Graph.isWellFormed_eq_true' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isWellFormed_eq_true

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_isWellFormed' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_isWellFormed

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_edgeAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_edgeAt

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_checkEdge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_checkEdge

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
info: 'Cslib.PCP.Encoded.Graph.satisfiable_toFiniteGraph_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_toFiniteGraph_iff

/--
info: 'Cslib.PCP.Encoded.Graph.unsatVal_toFiniteGraph' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_toFiniteGraph

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_addTrivial' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_addTrivial

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_addLoops' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_addLoops

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
info: 'Cslib.PCP.Encoded.Graph.toGraph_append' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_append

/--
info: 'Cslib.PCP.Encoded.Graph.toGraph_eq_comap' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_eq_comap

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_addTrivial_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_addTrivial_iff

/--
info: 'Cslib.PCP.Encoded.Graph.unsatVal_addTrivial' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_addTrivial

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_addLoops_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_addLoops_iff

/--
info: 'Cslib.PCP.Encoded.Graph.unsatVal_addLoops' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_addLoops

/--
info: 'Cslib.PCP.Encoded.Graph.mem_cloud_iff' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.mem_cloud_iff

/--
info: 'Cslib.PCP.Encoded.Graph.nodup_cloud' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.nodup_cloud

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_cloud' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_cloud

/--
info: 'Cslib.PCP.Encoded.Graph.cloudEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.cloudEquiv

/--
info: 'Cslib.PCP.Encoded.Graph.cloudEquiv_symm_apply' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.cloudEquiv_symm_apply

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_cloudRotation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_cloudRotation

/--
info: 'Cslib.PCP.Encoded.Graph.cloudRotation_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.cloudRotation_eq

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.indexed_polynomial_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.indexed_polynomial_bound

/--
info: 'Cslib.Crypto.GeneratorPadding.isPolyTime_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorPadding.isPolyTime_generate

/--
info: 'Cslib.Crypto.GeneratorPadding.length_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorPadding.length_generate

/--
info: 'Cslib.Crypto.GeneratorPadding.generate_distribution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorPadding.generate_distribution

/--
info: 'Cslib.Crypto.GeneratorPadding.ideal_distribution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorPadding.ideal_distribution

/--
info: 'Cslib.Crypto.GeneratorPadding.isPPTOn_test' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorPadding.isPPTOn_test

/--
info: 'Cslib.Crypto.GeneratorPadding.advantage_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorPadding.advantage_eq

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_seedLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_seedLength

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_outputLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_outputLength

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_generate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_generate_of_realization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_generate_of_realization

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.seedLength_lt_outputLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.seedLength_lt_outputLength

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.length_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.length_generate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_valid_choice' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_valid_choice

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_secure_choice' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_secure_choice

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.four_steps_le_owf_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.four_steps_le_owf_gap

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_common_seedLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_common_seedLength

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_paddedGenerate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_paddedGenerate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.length_paddedGenerate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.length_paddedGenerate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_secure_padded_choice' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_secure_padded_choice

/--
info: 'Cslib.PCP.ConstraintGraph.PreprocessExpanders.ofFamily' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.PreprocessExpanders.ofFamily

/--
info: 'Cslib.PCP.ConstraintGraph.preprocessWith_ofFamily' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.preprocessWith_ofFamily

/--
info: 'Cslib.PCP.ConstraintGraph.spectralExpansion_preprocessWith_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.spectralExpansion_preprocessWith_le

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_preprocessWith' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_preprocessWith

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_preprocessWith_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_preprocessWith_iff

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_preprocessWith' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_preprocessWith

/--
info: 'Cslib.PCP.ConstraintGraph.unsatVal_preprocessWith_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.unsatVal_preprocessWith_le

/--
info: 'Cslib.PCP.ConstraintGraph.satisfiable_amplifyWith_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.satisfiable_amplifyWith_iff

/--
info: 'Cslib.PCP.ConstraintGraph.le_unsatVal_amplifyWith' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.le_unsatVal_amplifyWith

/--
info: 'Cslib.PCP.ConstraintGraph.min_le_unsatVal_amplifyWith' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.min_le_unsatVal_amplifyWith

/--
info: 'Cslib.PCP.ConstraintGraph.Amplification.exists_killRate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.Amplification.exists_killRate

/--
info: 'Cslib.PCP.ConstraintGraph.Amplification.card_vertices' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.Amplification.card_vertices

/--
info: 'Cslib.PCP.ConstraintGraph.Amplification.card_edges' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.Amplification.card_edges

/--
info: 'Cslib.PCP.ConstraintGraph.Amplification.amplifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.Amplification.amplifier

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_degreeReduce' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_degreeReduce

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_degreeReduceEval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_degreeReduceEval

/--
info: 'Cslib.PCP.Encoded.Graph.toGraph_degreeReduce' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_degreeReduce

/--
info: 'Cslib.PCP.Encoded.Graph.wellFormed_degreeReduce' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.wellFormed_degreeReduce

/--
info: 'Cslib.PCP.Encoded.Graph.le_unsatVal_degreeReduce' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.le_unsatVal_degreeReduce

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_preprocess' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_preprocess

/--
info: 'Cslib.PCP.Encoded.Graph.toGraph_preprocess' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_preprocess

/--
info: 'Cslib.PCP.Encoded.Graph.wellFormed_preprocess' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.wellFormed_preprocess

/--
info: 'Cslib.PCP.Encoded.Graph.unsatVal_preprocess_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_preprocess_eq

/--
info: 'Cslib.PCP.Encoded.Graph.le_unsatVal_preprocess' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.le_unsatVal_preprocess

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_preprocess_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_preprocess_iff

/--
info: 'Cslib.PCP.Encoded.Graph.spectralExpansion_regularPreprocess_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.spectralExpansion_regularPreprocess_le

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_constraintTable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_constraintTable

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_tabulateConstraints' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_tabulateConstraints

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_constraintTableEval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_constraintTableEval

/--
info: 'Cslib.PCP.Encoded.Graph.toGraph_mapConstraints' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_mapConstraints

/--
info: 'Cslib.PCP.Encoded.Graph.unsatVal_mapConstraints' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_mapConstraints

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_mapConstraints_iff' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_mapConstraints_iff

/--
info: 'Cslib.PCP.Encoded.Graph.length_encoding_tabulateConstraints_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.length_encoding_tabulateConstraints_le

/--
info: 'Cslib.BitString.length_listXor' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.length_listXor

/--
info: 'Cslib.BitString.listXor_eq_ofFn_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.listXor_eq_ofFn_sum

/--
info: 'Turing.MultiTapeTM.length_encList_reverse' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.length_encList_reverse

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsXorWithInput' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsXorWithInput

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.listReverse' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.listReverse

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.listReverseWithInput' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.listReverseWithInput

/--
info: 'Cslib.Crypto.GeneratorXor.length_generate' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.length_generate

/--
info: 'Cslib.Crypto.GeneratorXor.isPolyTime_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.isPolyTime_generate

/--
info: 'Cslib.Crypto.GeneratorXor.generate_eq_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.generate_eq_sum

/--
info: 'Cslib.Crypto.GeneratorXor.generate_distribution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.generate_distribution

/--
info: 'Cslib.Crypto.GeneratorXor.real_distribution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.real_distribution

/--
info: 'Cslib.Crypto.GeneratorXor.ideal_distribution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.ideal_distribution

/--
info: 'Cslib.Crypto.GeneratorXor.isPPTOn_test' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.isPPTOn_test

/--
info: 'Cslib.Crypto.GeneratorXor.advantage_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.advantage_eq

/--
info: 'Cslib.Crypto.GeneratorXor.indistinguishable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorXor.indistinguishable

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_amplifiedGenerate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_amplifiedGenerate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.length_amplifiedGenerate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.length_amplifiedGenerate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_secure_amplified_choice' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.exists_secure_amplified_choice

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_combinedGenerate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.isPolyTime_combinedGenerate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.length_combinedGenerate' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.length_combinedGenerate

/--
info: 'Cslib.Crypto.Pseudoentropy.EntropyGrid.combinedGenerate_indistinguishable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.EntropyGrid.combinedGenerate_indistinguishable

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.findGreatest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.findGreatest

/--
info: 'Cslib.Crypto.Negligible.sqrt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Negligible.sqrt

/--
info: 'Cslib.Crypto.probability_calibratedTest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.probability_calibratedTest

/--
info: 'Cslib.Crypto.calibratedTest_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.calibratedTest_gap

/--
info: 'Cslib.Crypto.isPPTOn_calibratedTest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.isPPTOn_calibratedTest

/--
info: 'Cslib.Crypto.UniformChoice.isPPTOn_test' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.UniformChoice.isPPTOn_test

/--
info: 'Cslib.Crypto.UniformChoice.eval_bind_test' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.UniformChoice.eval_bind_test

/--
info: 'Cslib.Crypto.UniformChoice.advantage_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.UniformChoice.advantage_eq

/--
info: 'Cslib.Crypto.UniformChoice.advantage_sq_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.UniformChoice.advantage_sq_le

/--
info: 'Cslib.Crypto.ComputationallyIndistinguishable.uniform_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.ComputationallyIndistinguishable.uniform_bound

/--
info: 'Cslib.Crypto.GeneratorReindex.isPolyTime_parameter' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorReindex.isPolyTime_parameter

/--
info: 'Cslib.Crypto.GeneratorReindex.isPolyTime_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorReindex.isPolyTime_generate

/--
info: 'Cslib.Crypto.GeneratorReindex.length_generate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorReindex.length_generate

/--
info: 'Cslib.Crypto.GeneratorReindex.indistinguishable' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorReindex.indistinguishable

/--
info: 'Cslib.Crypto.GeneratorReindex.pseudorandomGenerator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.GeneratorReindex.pseudorandomGenerator

/--
info: 'Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.exists_pseudorandomGenerator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.exists_pseudorandomGenerator

/--
info: 'Cslib.Crypto.OneWay.exists_pseudorandomGenerator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.OneWay.exists_pseudorandomGenerator

/--
info: 'Cslib.Crypto.OneWay.exists_pseudorandomFunction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.OneWay.exists_pseudorandomFunction

/-! ### Executable PCP powering, composition, and one amplification round -/

/-- info: 'Cslib.RotationMap.walkAtWithInput_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.RotationMap.walkAtWithInput_eq

/-- info: 'Cslib.RotationMap.powRotWithInput_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.RotationMap.powRotWithInput_eq

/-- info: 'Cslib.RotationMap.killedPowRotWithInput_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.RotationMap.killedPowRotWithInput_eq

/-- info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_walkAtWithInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_walkAtWithInput

/-- info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_powRotWithInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_powRotWithInput

/-- info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_killedPowRotWithInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_killedPowRotWithInput

/-- info: 'Cslib.PCP.Encoded.Graph.halfEdgeOfNumber_halfEdgeNumber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.halfEdgeOfNumber_halfEdgeNumber

/-- info: 'Cslib.PCP.Encoded.Graph.isPolyTime_halfEdgeOfNumber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_halfEdgeOfNumber

/-- info: 'Cslib.PCP.Encoded.Graph.preprocessRotation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.preprocessRotation_eq

/-- info: 'Cslib.PCP.Encoded.Graph.preprocessRelation_eq_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.preprocessRelation_eq_true

/-- info: 'Cslib.PCP.Encoded.Graph.isPolyTime_preprocessRotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_preprocessRotation

/-- info: 'Cslib.PCP.Encoded.Graph.isPolyTime_preprocessRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_preprocessRelation

/-- info: 'Cslib.PCP.RegularConstraintGraph.powerRelationWithInput_eq_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.RegularConstraintGraph.powerRelationWithInput_eq_true

/-- info: 'Cslib.PCP.RegularConstraintGraph.isPolyTime_powerRelationWithInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.RegularConstraintGraph.isPolyTime_powerRelationWithInput

/-- info: 'Cslib.PCP.Encoded.Graph.length_edges_powerPreprocess' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.length_edges_powerPreprocess

/-- info: 'Cslib.PCP.Encoded.Graph.toGraph_powerPreprocess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_powerPreprocess

/-- info: 'Cslib.PCP.Encoded.Graph.wellFormed_powerPreprocess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.wellFormed_powerPreprocess

/-- info: 'Cslib.PCP.Encoded.Graph.unsatVal_powerPreprocess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_powerPreprocess

/-- info: 'Cslib.PCP.Encoded.Graph.satisfiable_powerPreprocess_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_powerPreprocess_iff

/-- info: 'Cslib.PCP.Encoded.Graph.isPolyTime_powerPreprocess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_powerPreprocess

/-- info: 'Cslib.PCP.ConstraintGraph.le_div_unsatVal_power_preprocessWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.ConstraintGraph.le_div_unsatVal_power_preprocessWith

/-- info: 'Cslib.PCP.Encoded.Graph.isPolyTime_amplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_amplify

/-- info: 'Cslib.PCP.Encoded.Graph.vertices_amplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.vertices_amplify

/-- info: 'Cslib.PCP.Encoded.Graph.length_edges_amplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.length_edges_amplify

/-- info: 'Cslib.PCP.Encoded.Graph.wellFormed_amplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.wellFormed_amplify

/-- info: 'Cslib.PCP.Encoded.Graph.div_le_unsatVal_amplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.div_le_unsatVal_amplify

/-- info: 'Cslib.PCP.Encoded.Graph.le_unsatVal_amplify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.le_unsatVal_amplify

/-- info: 'Cslib.PCP.Encoded.Graph.satisfiable_amplify_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_amplify_iff
/--
info: 'Cslib.PCP.Encoded.HadamardTester.localTest_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.HadamardTester.localTest_eq

/--
info: 'Cslib.PCP.Encoded.HadamardTester.isPolyTime_query' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.HadamardTester.isPolyTime_query

/--
info: 'Cslib.PCP.Encoded.HadamardTester.isPolyTime_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.HadamardTester.isPolyTime_accepts

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_compose' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_compose

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_composeTabulated' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_composeTabulated

/--
info: 'Cslib.PCP.Encoded.Graph.WellFormed.compose' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.WellFormed.compose

/--
info: 'Cslib.PCP.Encoded.Graph.toGraph_compose' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_compose

/--
info: 'Cslib.PCP.Encoded.Graph.le_unsatVal_compose' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.le_unsatVal_compose

/--
info: 'Cslib.PCP.Encoded.Graph.unsatVal_composeTabulated_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_composeTabulated_eq

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_composeTabulated_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_composeTabulated_iff
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
info: 'Cslib.PCP.Encoded.Graph.WellFormed.length_encoding_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.WellFormed.length_encoding_le

/--
info: 'Cslib.Logic.PL.CNF.satisfiable_compact' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.satisfiable_compact

/--
info: 'Cslib.Logic.PL.CNF.mem_vars_compact_lt' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.mem_vars_compact_lt

/--
info: 'Cslib.Logic.PL.CNF.isPolyTime_compact' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.isPolyTime_compact

/--
info: 'Cslib.PCP.Encoded.Graph.cnfVertexNumber_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.cnfVertexNumber_injective

/--
info: 'Cslib.PCP.Encoded.Graph.toGraph_ofCNF' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.toGraph_ofCNF

/--
info: 'Cslib.PCP.Encoded.Graph.unsatVal_ofCNF' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_ofCNF

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_ofCompactCNF' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_ofCompactCNF

/--
info: 'Cslib.PCP.Encoded.Graph.wellFormed_ofCompactCNF' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.wellFormed_ofCompactCNF

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_ofCompactCNF_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_ofCompactCNF_iff

/--
info: 'Cslib.PCP.Encoded.Graph.inv_edges_le_unsatVal_ofCompactCNF' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.inv_edges_le_unsatVal_ofCompactCNF

/--
info: 'Cslib.PCP.ConstraintGraph.min_le_div_unsatVal_power_preprocessWith' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.min_le_div_unsatVal_power_preprocessWith

/--
info: 'Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplify' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplify

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_amplifyIter_clog' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_amplifyIter_clog

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_amplifyIter_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_amplifyIter_iff

/--
info: 'Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplifyIter' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplifyIter

/--
info: 'Cslib.PCP.Encoded.Graph.gap_le_unsatVal_amplifyIter' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.gap_le_unsatVal_amplifyIter

/--
info: 'Cslib.PCP.Encoded.Graph.gap_le_unsatVal_amplifyIter_clog' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.gap_le_unsatVal_amplifyIter_clog

/--
info: 'Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.walkLength_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.walkLength_eq

/--
info: 'Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.gain' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.ConstraintGraph.Amplification.Arithmetic.gain


/--
info: 'Cslib.PCP.Encoded.Graph.polyBounded_iterationSize_clog' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.polyBounded_iterationSize_clog

/--
info: 'Cslib.PCP.Encoded.Graph.iterate_length_encoding_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.iterate_length_encoding_le

/-- info: 'Cslib.PCP.min_two_pow_mul_le_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.min_two_pow_mul_le_iterate

/-- info: 'Cslib.PCP.ConstraintGraph.one_le_card_mul_unsatVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.ConstraintGraph.one_le_card_mul_unsatVal

/-- info: 'Cslib.PCP.Amplifier.min_le_unsatVal_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Amplifier.min_le_unsatVal_iter

/-- info: 'Cslib.PCP.Amplifier.gap_le_unsatVal_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Amplifier.gap_le_unsatVal_iter

/-- info: 'Cslib.PCP.HadamardTester.Rand.finEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.HadamardTester.Rand.finEnum

/-- info: 'Cslib.PCP.Encoded.Graph.ComposeSlot.finEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.ComposeSlot.finEnum

/-- info: 'Cslib.PCP.Encoded.Graph.isPolyTime_composeEnumerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_composeEnumerated

/-- info: 'Cslib.PCP.Encoded.Graph.WellFormed.composeEnumerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.WellFormed.composeEnumerated

/-- info: 'Cslib.PCP.Encoded.Graph.unsatVal_composeEnumerated_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_composeEnumerated_eq

/-- info: 'Cslib.PCP.Encoded.Graph.satisfiable_composeEnumerated_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_composeEnumerated_iff

/-- info: 'Cslib.PCP.Encoded.Graph.le_unsatVal_composeEnumerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.le_unsatVal_composeEnumerated

/-- info: 'Cslib.PCP.Encoded.Graph.isPolyTime_amplifyEnumerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_amplifyEnumerated

/-- info: 'Cslib.PCP.Encoded.Graph.wellFormed_amplifyEnumerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.wellFormed_amplifyEnumerated

/-- info: 'Cslib.PCP.Encoded.Graph.satisfiable_amplifyEnumerated_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_amplifyEnumerated_iff

/-- info: 'Cslib.PCP.Encoded.Graph.le_unsatVal_amplifyEnumerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.le_unsatVal_amplifyEnumerated

/-- info: 'Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplifyEnumerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplifyEnumerated

/--
info: 'Cslib.PCP.Encoded.Graph.arithmeticAmplify' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.arithmeticAmplify

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_arithmeticAmplify' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_arithmeticAmplify

/--
info: 'Cslib.PCP.Encoded.Graph.wellFormed_arithmeticAmplify' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.wellFormed_arithmeticAmplify

/--
info: 'Cslib.PCP.Encoded.Graph.satisfiable_arithmeticAmplify_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.satisfiable_arithmeticAmplify_iff

/--
info: 'Cslib.PCP.Encoded.Graph.gap_le_unsatVal_arithmeticAmplify' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.gap_le_unsatVal_arithmeticAmplify

/-- info: 'Turing.MultiTapeTM.encSum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.encSum

/-- info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.sumInl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.sumInl

/-- info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.sumInr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.sumInr

/-- info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.zipIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.zipIdx

/-- info: 'Cslib.Logic.PL.Clause.isPolyTime_splitAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.PL.Clause.isPolyTime_splitAux

/-- info: 'Cslib.Logic.PL.Clause.isPolyTime_split3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.PL.Clause.isPolyTime_split3

/-- info: 'Cslib.Logic.PL.CNF.isPolyTime_to3CNF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Logic.PL.CNF.isPolyTime_to3CNF

/-- info: 'Cslib.PCP.Encoded.isPolyTime_gapGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.isPolyTime_gapGraph

/-- info: 'Cslib.PCP.Encoded.wellFormed_gapGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.wellFormed_gapGraph

/-- info: 'Cslib.PCP.Encoded.satisfiable_gapGraph_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.satisfiable_gapGraph_iff

/-- info: 'Cslib.PCP.Encoded.gap_le_unsatVal_gapGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.gap_le_unsatVal_gapGraph

/--
info: 'Cslib.PCP.Encoded.Edge.proofVerdict_answers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Edge.proofVerdict_answers

/--
info: 'Cslib.PCP.Encoded.Edge.isPolyTime_proofQueries' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Edge.isPolyTime_proofQueries

/--
info: 'Cslib.PCP.Encoded.Edge.isPolyTime_proofVerdict' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Edge.isPolyTime_proofVerdict

/--
info: 'Cslib.PCP.Encoded.Graph.isPolyTime_sampleEdge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.isPolyTime_sampleEdge

/--
info: 'Cslib.PCP.Encoded.Graph.proofLabels_proofOfLabels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.proofLabels_proofOfLabels

/--
info: 'Cslib.PCP.Encoded.Graph.edgeVerifier_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.edgeVerifier_accepts

/--
info: 'Cslib.PCP.Encoded.Graph.polyTime_edgeVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.polyTime_edgeVerifier

/--
info: 'Cslib.PCP.Encoded.Graph.accepts_proofOfLabels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.accepts_proofOfLabels

/--
info: 'Cslib.PCP.Encoded.Graph.rejectProb_edgeVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.rejectProb_edgeVerifier

/--
info: 'Cslib.PCP.Encoded.Graph.unsatVal_div_two_le_rejectProb' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.unsatVal_div_two_le_rejectProb

/--
info: 'Cslib.PCP.Encoded.Graph.length_queries_repeatedEdgeVerifier' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.length_queries_repeatedEdgeVerifier

/--
info: 'Cslib.PCP.Encoded.Graph.repeatedEdgeVerifier_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.repeatedEdgeVerifier_accepts

/--
info: 'Cslib.PCP.Encoded.Graph.polyTime_repeatedEdgeVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.polyTime_repeatedEdgeVerifier

/--
info: 'Cslib.PCP.Encoded.Graph.repeated_accepts_proofOfLabels' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.repeated_accepts_proofOfLabels

/--
info: 'Cslib.PCP.Encoded.Graph.acceptProb_repeatedEdgeVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.acceptProb_repeatedEdgeVerifier

/--
info: 'Cslib.PCP.Encoded.Graph.polyTime_reductionVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.polyTime_reductionVerifier

/--
info: 'Cslib.PCP.Encoded.Graph.mem_PCP_of_gapReduction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.PCP.Encoded.Graph.mem_PCP_of_gapReduction

/-- info: 'Cslib.BitString.uniformList_all_listRow_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.BitString.uniformList_all_listRow_true

/-- info: 'Cslib.Complexity.uniformList_acceptCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.uniformList_acceptCount

/-- info: 'Cslib.Complexity.uniformList_acceptCount_toReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.uniformList_acceptCount_toReal

/-- info: 'Cslib.Complexity.acceptCount_le_half_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.acceptCount_le_half_iff

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
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_to_unary_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_to_unary_bounded

/--
info: 'Cslib.Complexity.PCPVerifier.isPolyTime_queryTable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCPVerifier.isPolyTime_queryTable

/--
info: 'Cslib.Complexity.PCPVerifier.isPolyTime_tableVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCPVerifier.isPolyTime_tableVerifier

/--
info: 'Cslib.Complexity.PCPVerifier.tableVerifier_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCPVerifier.tableVerifier_complete

/--
info: 'Cslib.Complexity.PCPVerifier.tableVerifier_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCPVerifier.tableVerifier_sound

/--
info: 'Cslib.Complexity.PCP_log_subset_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PCP_log_subset_NP

/--
info: 'Cslib.Complexity.NP_subset_PCP_log' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_subset_PCP_log

/--
info: 'Cslib.Complexity.NP_eq_PCP_log' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.NP_eq_PCP_log

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_spec

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInO.foldl_bits_finite' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInO.foldl_bits_finite

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.map_bits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.map_bits

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInDegree.comp_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInDegree.comp_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInDegree.prod_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInDegree.prod_le

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInDegree.id'' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInDegree.id'

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_sum

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum_spec

/--
info: 'Cslib.Circuits.Circuit.eval_replicate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.eval_replicate

/--
info: 'Cslib.Circuits.Circuit.cost_program_replicate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_program_replicate

/--
info: 'Cslib.Circuits.Circuit.Computes.takeDirectProductPrefix' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.Computes.takeDirectProductPrefix

/--
info: 'Cslib.Circuits.ecomplexityFrom_directProduct_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_directProduct_zero

/--
info: 'Cslib.Circuits.ecomplexityFrom_directProduct_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_directProduct_le

/--
info: 'Cslib.Circuits.ecomplexityFrom_directProduct_mono' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_directProduct_mono

/--
info: 'Cslib.Circuits.ecomplexityFrom_directProduct_comp_wiring_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFrom_directProduct_comp_wiring_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.massComplexity_le_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.massComplexity_le_iff

/--
info: 'Cslib.Circuits.Boolean.MassProduction.exists_computes_cost_eq_massComplexity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.exists_computes_cost_eq_massComplexity

/--
info: 'Cslib.Circuits.Boolean.MassProduction.massComplexity_comp_castLE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.massComplexity_comp_castLE

/--
info: 'Cslib.Circuits.Boolean.MassProduction.shannonScale_le_of_le_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.shannonScale_le_of_le_add

/--
info: 'Cslib.Circuits.Boolean.MassProduction.MassProducesAt.allLengths' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.MassProducesAt.allLengths

/--
info: 'Cslib.Circuits.Boolean.MassProduction.Uhlig.complexity_directProduct_two_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.Uhlig.complexity_directProduct_two_mul_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.mul_complexity_directProduct_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.mul_complexity_directProduct_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.eventually_mul_complexity_directProduct_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.eventually_mul_complexity_directProduct_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.eventually_mul_massComplexity_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.eventually_mul_massComplexity_le

/--
info: 'Cslib.Circuits.Boolean.MassProduction.fineMassProducesThrough' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.fineMassProducesThrough

/--
info: 'Cslib.Circuits.Boolean.MassProduction.fineMassProducesAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.fineMassProducesAt

/--
info: 'Cslib.Circuits.Boolean.MassProduction.exponentialMassProduction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.exponentialMassProduction

/--
info: 'Cslib.Circuits.Boolean.MassProduction.realFineMassProduction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.realFineMassProduction

/--
info: 'Cslib.Circuits.Boolean.MassProduction.exists_isScheduler' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.exists_isScheduler

/--
info: 'Cslib.Circuits.Boolean.MassProduction.complexity_directProduct_le_of_isScheduler' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.complexity_directProduct_le_of_isScheduler

/--
info: 'Cslib.LineCode.HighRate.exists_lineCode' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.LineCode.HighRate.exists_lineCode

/--
info: 'Cslib.LineCode.exists_isUniversalMenu' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.LineCode.exists_isUniversalMenu

/--
info: 'Cslib.Circuits.Boolean.eval_mintermCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_mintermCircuit

/--
info: 'Cslib.Circuits.Boolean.size_mintermCircuit_add_three_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_mintermCircuit_add_three_le

/--
info: 'Cslib.Circuits.Boolean.ShannonSynthesis.eval_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ShannonSynthesis.eval_circuit

/--
info: 'Cslib.Circuits.Boolean.ShannonSynthesis.size_circuit_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ShannonSynthesis.size_circuit_le

/--
info: 'Cslib.Circuits.Boolean.ShannonSynthesis.bound_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ShannonSynthesis.bound_le

/--
info: 'Cslib.Circuits.Boolean.ShannonSynthesis.computes_synthesize' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ShannonSynthesis.computes_synthesize

/--
info: 'Cslib.Circuits.Boolean.ShannonSynthesis.exists_circuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.ShannonSynthesis.exists_circuit

/--
info: 'Cslib.Circuits.Boolean.MassProduction.massComplexity_le_shannon' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.MassProduction.massComplexity_le_shannon

/--
info: 'Cslib.Circuits.Program.get_evalVector' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.get_evalVector

/--
info: 'Cslib.Circuits.Program.eval_eq_evalImpl' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.eval_eq_evalImpl

/--
info: 'Cslib.Circuits.Program.trace_eq_traceImpl' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Program.trace_eq_traceImpl

/--
info: 'Cslib.Circuits.Circuit.get_evalVector' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.get_evalVector

/--
info: 'Cslib.Circuits.Circuit.eval_eq_evalImpl' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.eval_eq_evalImpl

/--
info: 'Cslib.Circuits.Formula.size_lexLt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.size_lexLt

/--
info: 'Cslib.Circuits.Formula.eval_lexLt_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.eval_lexLt_iff

/--
info: 'Cslib.Circuits.Boolean.eval_compareSwapCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_compareSwapCircuit

/--
info: 'Cslib.Circuits.Boolean.size_compareSwapCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_compareSwapCircuit

/--
info: 'Cslib.Circuits.Boolean.compareSwapCircuit_keys_ordered' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.compareSwapCircuit_keys_ordered

/--
info: 'Cslib.Circuits.Boolean.eval_compareSwapCircuit_of_key_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_compareSwapCircuit_of_key_eq

/--
info: 'Cslib.BitonicSort.sort_perm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.sort_perm

/--
info: 'Cslib.BitonicSort.monotone_sort' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.monotone_sort

/--
info: 'Cslib.BitonicSort.antitone_sort' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.antitone_sort

/--
info: 'Cslib.Circuits.Circuit.cost_program_parallel' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_program_parallel

/--
info: 'Cslib.Circuits.Boolean.eval_bitonicSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_bitonicSortCircuit

/--
info: 'Cslib.Circuits.Boolean.monotone_bitonicSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.monotone_bitonicSortCircuit

/--
info: 'Cslib.Circuits.Boolean.antitone_bitonicSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.antitone_bitonicSortCircuit

/--
info: 'Cslib.Circuits.Boolean.bitonicSortCircuit_perm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.bitonicSortCircuit_perm

/--
info: 'Cslib.Circuits.Boolean.four_mul_cost_program_bitonicSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.four_mul_cost_program_bitonicSortCircuit

/--
info: 'Cslib.Circuits.Boolean.four_mul_size_bitonicSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.four_mul_size_bitonicSortCircuit

/--
info: 'Cslib.Circuits.Boolean.eval_keyedSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_keyedSortCircuit

/--
info: 'Cslib.Circuits.Boolean.keyedSortCircuit_perm' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.keyedSortCircuit_perm

/--
info: 'Cslib.Circuits.Boolean.monotone_keyedSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.monotone_keyedSortCircuit

/--
info: 'Cslib.Circuits.Boolean.antitone_keyedSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.antitone_keyedSortCircuit

/--
info: 'Cslib.Circuits.Boolean.four_mul_cost_program_keyedSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.four_mul_cost_program_keyedSortCircuit

/--
info: 'Cslib.Circuits.Boolean.four_mul_size_keyedSortCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.four_mul_size_keyedSortCircuit

/--
info: 'Cslib.BitString.propagate_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.propagate_eq_true_iff

/--
info: 'Cslib.BitString.propagate_sorted_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.propagate_sorted_eq_true_iff

/--
info: 'Cslib.Circuits.Boolean.eval_propagateCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_propagateCircuit

/--
info: 'Cslib.Circuits.Boolean.eval_propagateCircuit_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_propagateCircuit_eq_true_iff

/--
info: 'Cslib.Circuits.Boolean.cost_program_propagateCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_propagateCircuit

/--
info: 'Cslib.Circuits.Boolean.size_propagateCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_propagateCircuit

/--
info: 'Cslib.Circuits.Formula.eval_equalBits_iff' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.eval_equalBits_iff

/--
info: 'Cslib.Circuits.Formula.cost_equalBits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.cost_equalBits

/--
info: 'Cslib.Circuits.Formula.size_equalBits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Formula.size_equalBits

/--
info: 'Cslib.BitString.propagate_congr' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.propagate_congr

/--
info: 'Cslib.BitString.propagate_sorted_tagged_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.propagate_sorted_tagged_eq_true_iff

/--
info: 'Cslib.Circuits.Boolean.broadcastCircuit.eval_values_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.broadcastCircuit.eval_values_eq_true_iff

/--
info: 'Cslib.Circuits.Boolean.eval_broadcastCircuit_header' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_broadcastCircuit_header

/--
info: 'Cslib.Circuits.Boolean.eval_broadcastCircuit_value' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_broadcastCircuit_value

/--
info: 'Cslib.Circuits.Boolean.eval_broadcastCircuit_value_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_broadcastCircuit_value_eq_true_iff

/--
info: 'Cslib.Circuits.Boolean.eval_broadcastCircuit_value_of_unique_source' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_broadcastCircuit_value_of_unique_source

/--
info: 'Cslib.Circuits.Boolean.cost_program_broadcastCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_broadcastCircuit

/--
info: 'Cslib.Circuits.Boolean.size_broadcastCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_broadcastCircuit

/--
info: 'List.Perm.exists_ofFn_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms List.Perm.exists_ofFn_iff

/--
info: 'List.countP_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms List.countP_ofFn

/--
info: 'List.Perm.card_filter_ofFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms List.Perm.card_filter_ofFn_eq

/--
info: 'List.Perm.existsUnique_ofFn_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms List.Perm.existsUnique_ofFn_iff

/--
info: 'Fin.card_lt_of_monotone_of_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fin.card_lt_of_monotone_of_unique

/--
info: 'List.Perm.key_ofFn_eq_of_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms List.Perm.key_ofFn_eq_of_rank

/--
info: 'List.Perm.apply_ofFn_eq_of_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms List.Perm.apply_ofFn_eq_of_rank

/--
info: 'Cslib.Circuits.Boolean.routeCircuit.headers_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.routeCircuit.headers_perm

/--
info: 'Cslib.Circuits.Boolean.routeCircuit.value_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.routeCircuit.value_eq_true_iff

/--
info: 'Cslib.Circuits.Boolean.routeCircuit_headers_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.routeCircuit_headers_perm

/--
info: 'Cslib.Circuits.Boolean.monotone_routeCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.monotone_routeCircuit

/--
info: 'Cslib.Circuits.Boolean.eval_routeCircuit_value_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_routeCircuit_value_eq_true_iff

/--
info: 'Cslib.Circuits.Boolean.eval_routeCircuit_header_of_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_routeCircuit_header_of_rank

/--
info: 'Cslib.Circuits.Boolean.eval_routeCircuit_value_eq_true_iff_of_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_routeCircuit_value_eq_true_iff_of_rank

/--
info: 'Cslib.Circuits.Boolean.eval_routeCircuit_value_of_unique_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_routeCircuit_value_of_unique_source

/--
info: 'Cslib.Circuits.Boolean.cost_program_routeCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_routeCircuit

/--
info: 'Cslib.Circuits.Boolean.four_mul_cost_program_routeCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.four_mul_cost_program_routeCircuit

/--
info: 'Cslib.Circuits.Boolean.four_mul_size_routeCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.four_mul_size_routeCircuit

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
info: 'Cslib.Circuits.Boolean.eval_bitonicSortTraceCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_bitonicSortTraceCircuit

/--
info: 'Cslib.Circuits.Boolean.eval_bitonicUnsortCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_bitonicUnsortCircuit

/--
info: 'Cslib.Circuits.Boolean.eval_bitonicUnsortCircuit_sort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_bitonicUnsortCircuit_sort

/--
info: 'Cslib.Circuits.Boolean.cost_program_bitonicSortTraceCircuit_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_bitonicSortTraceCircuit_eq

/--
info: 'Cslib.Circuits.Boolean.size_bitonicUnsortCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_bitonicUnsortCircuit

/--
info: 'Cslib.Circuits.Boolean.cost_program_bitonicSortTraceCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_bitonicSortTraceCircuit

/--
info: 'Cslib.Circuits.Boolean.cost_program_bitonicUnsortCircuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_bitonicUnsortCircuit

/--
info: 'Cslib.BitonicSort.unrouteSort_rel_sort' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitonicSort.unrouteSort_rel_sort

/--
info: 'Cslib.Circuits.Boolean.eval_substituteCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_substituteCircuit

/--
info: 'Cslib.Circuits.Boolean.cost_program_substituteCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_substituteCircuit

/--
info: 'Cslib.Circuits.Boolean.eval_routeValuesCircuit_value_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_routeValuesCircuit_value_eq_true_iff

/--
info: 'Cslib.Circuits.Boolean.eval_routeValuesCircuit_of_unique_source' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_routeValuesCircuit_of_unique_source

/--
info: 'Cslib.Circuits.Boolean.cost_program_routeValuesCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_routeValuesCircuit

/--
info: 'Cslib.Circuits.Boolean.size_routeValuesCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_routeValuesCircuit

/--
info: 'Cslib.Circuits.Boolean.batchLookupCircuit.eval_withPadding' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.batchLookupCircuit.eval_withPadding

/--
info: 'Cslib.Circuits.Boolean.batchLookupCircuit.size_withPadding' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.batchLookupCircuit.size_withPadding

/--
info: 'Cslib.Circuits.Boolean.size_batchLookupCircuit_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_batchLookupCircuit_le

/--
info: 'Cslib.Circuits.Boolean.complexity_blockMap_le_lookup' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.complexity_blockMap_le_lookup

/--
info: 'Cslib.Circuits.Boolean.eval_batchLookupCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_batchLookupCircuit

/--
info: 'Cslib.Circuits.Boolean.batchLookupCircuit.cost_program_withPadding' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.batchLookupCircuit.cost_program_withPadding

/--
info: 'Cslib.Circuits.Boolean.eval_batchOrCircuit_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_batchOrCircuit_iff

/--
info: 'Cslib.Circuits.Boolean.batchOrCircuit.cost_program_withPadding' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.batchOrCircuit.cost_program_withPadding

/--
info: 'Cslib.Circuits.Boolean.batchOrCircuit.size_withPadding' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.batchOrCircuit.size_withPadding

/--
info: 'Cslib.Circuits.Boolean.size_batchOrCircuit_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_batchOrCircuit_le

/--
info: 'Cslib.Circuits.Boolean.eval_adjacentDuplicateCircuit_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_adjacentDuplicateCircuit_iff

/--
info: 'Cslib.Circuits.Boolean.eval_duplicateFlagsCircuit_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.eval_duplicateFlagsCircuit_iff

/--
info: 'Cslib.Circuits.Boolean.cost_program_duplicateFlagsCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.cost_program_duplicateFlagsCircuit

/--
info: 'Cslib.Circuits.Boolean.size_duplicateFlagsCircuit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.size_duplicateFlagsCircuit

/--
info: 'Fin.exists_ne_apply_eq_iff_adjacent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fin.exists_ne_apply_eq_iff_adjacent

/--
info: 'Cslib.BitString.LinearHash.expect_card_collisions_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.LinearHash.expect_card_collisions_le

/--
info: 'Cslib.BitString.LinearHash.exists_card_collisions_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.LinearHash.exists_card_collisions_le

/--
info: 'Cslib.BitString.LinearHash.exists_card_collisions_le_choose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.LinearHash.exists_card_collisions_le_choose

/--
info: 'Cslib.BitString.LinearHash.exists_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.LinearHash.exists_injOn

/--
info: 'Cslib.PCP.AssignmentTester.Implementation.toGraph_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.PCP.AssignmentTester.Implementation.toGraph_compose

/--
info: 'Cslib.PCP.AssignmentTester.Implementation.isPolyTime_composeTabulated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.PCP.AssignmentTester.Implementation.isPolyTime_composeTabulated

/--
info: 'Cslib.PCP.AssignmentTester.Implementation.unsatVal_composeEnumerated_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.PCP.AssignmentTester.Implementation.unsatVal_composeEnumerated_eq

/--
info: 'Cslib.PCP.ConstraintGraph.card_vertices_composeSelected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.PCP.ConstraintGraph.card_vertices_composeSelected

/--
info: 'Cslib.PCP.Encoded.Graph.le_unsatVal_composeSelectedEnumerated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.PCP.Encoded.Graph.le_unsatVal_composeSelectedEnumerated

/--
info: 'Finset.exists_quantile' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Finset.exists_quantile

/--
info: 'Cslib.SeparableComparison.exists_rectangle' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.SeparableComparison.exists_rectangle

/--
info: 'Cslib.DecisionTree.exists_leaf_rectangle' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.DecisionTree.exists_leaf_rectangle

/--
info: 'Cslib.DecisionTree.card_mul_le_mul_leafCount_sq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.DecisionTree.card_mul_le_mul_leafCount_sq

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.preserves_ofThreshold' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.preserves_ofThreshold

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.eval_gate_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.eval_gate_eq

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.gateWeight_eq_zero_of_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.gateWeight_eq_zero_of_le

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_transcript_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_transcript_eq

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_eval_eq_of_transcript_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.circuit_eval_eq_of_transcript_eq

/--
info: 'Cslib.BitString.card_mul_le_two_pow_of_dotProduct_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.BitString.card_mul_le_two_pow_of_dotProduct_eq

/--
info: 'Cslib.DecisionTree.two_pow_le_leafCount_sq_of_dotProduct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.DecisionTree.two_pow_le_leafCount_sq_of_dotProduct

/--
info: 'Cslib.DecisionTree.exists_of_observations'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.exists_of_observations

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_forall_mem_inputGates_lt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_forall_mem_inputGates_lt

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.gateComparison_eval_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.gateComparison_eval_eq

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.exists_transcript_tree'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.exists_transcript_tree

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.exists_gate_readout_tree'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.exists_gate_readout_tree

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.exists_circuit_tree'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.exists_circuit_tree

/--
info: 'Cslib.BitString.card_filter_weight_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.card_filter_weight_le

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_le_card' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_le_card

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose

/--
info: 'Cslib.ChangesAtMost.exists_sorted_group' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ChangesAtMost.exists_sorted_group

/--
info: 'Cslib.ChangesAtMost.comp_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.ChangesAtMost.comp_monotone

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.BlockDecomposition.two_pow_lt_mul_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.BlockDecomposition.two_pow_lt_mul_cost

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_card_attainableTranscripts_sq_of_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_card_attainableTranscripts_sq_of_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_sq_of_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_sq_of_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_sq_of_circuit_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_sq_of_circuit_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.cost_blockDecomposition' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.cost_blockDecomposition

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_four_pow_inputGates'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_four_pow_inputGates

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_mul_four_pow_inputGates'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_mul_four_pow_inputGates

/--
info: 'Cslib.BitString.card_image_le_sum_choose'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.BitString.card_image_le_sum_choose

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_le_gateActivity'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_le_gateActivity

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose_gateActivity'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose_gateActivity

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_gateActivity_sq_of_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_gateActivity_sq_of_dotProduct

open Cslib.Circuits.Boolean.WeightedThreshold in
/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.two_pow_le_sum_choose_gateActivity_sq_of_circuit_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_le_sum_choose_gateActivity_sq_of_circuit_dotProduct

/-- info: 'Cslib.DecisionTree.eval_mapQueries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.DecisionTree.eval_mapQueries

/-- info: 'Cslib.DecisionTree.depth_mapQueries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.DecisionTree.depth_mapQueries

/-- info: 'Cslib.DecisionTree.leafCount_mapQueries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.DecisionTree.leafCount_mapQueries

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.gateQuery_eval_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.gateQuery_eval_eq

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.lineComparison_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.lineComparison_eval

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.exists_linear_transcript_tree'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.exists_linear_transcript_tree

/--
info: 'Cslib.sum_choose_le_exp_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.sum_choose_le_exp_mul_pow

/--
info: 'Cslib.sum_choose_le_exp_one_mul_div_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.sum_choose_le_exp_one_mul_div_pow

/--
info: 'Cslib.le_mul_logb_of_two_pow_le_sum_choose_sq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.le_mul_logb_of_two_pow_le_sum_choose_sq

/--
info: 'Cslib.mul_rpow_le_of_two_pow_le_sum_choose_sq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.mul_rpow_le_of_two_pow_le_sum_choose_sq

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_pos_of_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_pos_of_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.le_inputActivity_mul_logb_of_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.WeightedThreshold.le_inputActivity_mul_logb_of_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_mul_rpow_le_card_of_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_mul_rpow_le_card_of_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.le_inputActivity_mul_logb_of_circuit_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.le_inputActivity_mul_logb_of_circuit_dotProduct

/--
info:
'Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_mul_rpow_le_card_of_circuit_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.inputActivity_mul_rpow_le_card_of_circuit_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.le_gateActivity_mul_logb_of_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.le_gateActivity_mul_logb_of_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.gateActivity_mul_rpow_le_of_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.gateActivity_mul_rpow_le_of_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.le_gateActivity_mul_logb_of_circuit_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.le_gateActivity_mul_logb_of_circuit_dotProduct

/--
info: 'Cslib.Circuits.Boolean.WeightedThreshold.gateActivity_mul_rpow_le_of_circuit_dotProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Cslib.Circuits.Boolean.WeightedThreshold.gateActivity_mul_rpow_le_of_circuit_dotProduct

/--
info: 'Cslib.FunctionalGraph.exists_checkpoints' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.FunctionalGraph.exists_checkpoints

/--
info: 'Cslib.FunctionalGraph.card_range_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.FunctionalGraph.card_range_iterate

/-- info: 'Cslib.Circuits.Circuit.cost_program_iterate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Circuit.cost_program_iterate

/--
info: 'Cslib.Circuits.Synthesis.orbit' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Synthesis.orbit

/--
info: 'Cslib.BitString.totalInfluence_le_sqrt_card_of_monotone' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.totalInfluence_le_sqrt_card_of_monotone

/--
info: 'Cslib.BitString.totalInfluence_signVal_le_of_degree' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.totalInfluence_signVal_le_of_degree

/--
info: 'Cslib.BitString.two_pow_card_le_two_pow_mul_card_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.two_pow_card_le_two_pow_mul_card_ne_zero

/--
info: 'Cslib.BitString.card_filter_influence_ne_zero_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.BitString.card_filter_influence_ne_zero_le

/--
info: 'Cslib.DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one

/--
info: 'Cslib.DecisionTree.sum_abs_fourierCoeff_le_leafCount' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.DecisionTree.sum_abs_fourierCoeff_le_leafCount

/--
info: 'Cslib.Circuits.Boolean.exists_formula_parity_two_pow_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.exists_formula_parity_two_pow_add

/--
info: 'Cslib.Circuits.Boolean.formulaDepth_parity_two_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.formulaDepth_parity_two_pow

/--
info: 'Cslib.Circuits.Boolean.sq_div_four_le_leafSize_of_computes_majority' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.sq_div_four_le_leafSize_of_computes_majority

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.not_computable_complexity_universal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.not_computable_complexity_universal

/--
info: 'Cslib.Kolmogorov.DescriptionMethod.tendsto_complexity_universal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Kolmogorov.DescriptionMethod.tendsto_complexity_universal

/--
info: 'Cslib.Crypto.PseudorandomGenerator.oneWay' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PseudorandomGenerator.oneWay

/--
info: 'Cslib.Crypto.exists_oneWay_iff_exists_pseudorandomGenerator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.exists_oneWay_iff_exists_pseudorandomGenerator

/--
info: 'Cslib.RotationMap.sqrt_le_spectralExpansion' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.RotationMap.sqrt_le_spectralExpansion

/--
info: 'Cslib.exists_card_eq_pow_not_containsSunflower' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.exists_card_eq_pow_not_containsSunflower

/--
info: 'Cslib.Finset.card_pow_le_prod_card_image_restrict_erase' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Finset.card_pow_le_prod_card_image_restrict_erase
