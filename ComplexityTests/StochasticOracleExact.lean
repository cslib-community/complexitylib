/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.TwoBatchHardness
import Complexity.Probability.StochasticOracle.TwoBatchIntegralRuntime
import ComplexityTests.StochasticOracleApproximation
import Mathlib.Tactic

/-!
# Exact two-turn selection clients

Binary hardness includes zero-weight source inputs, repeated indexed calls and
both answers. Exact selection checks heterogeneous cutoffs/probabilities, the
actual emitted batches, exact cost/success, infeasible deadlines and empty input.
-/

open Cslib.Probability.StochasticOracle Cslib.Complexity
namespace ComplexityTests.StochasticOracleExact
open TwoBatchHardness

example : (reduction ([],0)).calls = [(1/4,1,1),(1/4,1,1)] := by decide +kernel
example : (reduction ([0,0],0)).calls = (reduction ([],0)).calls := by decide +kernel
example : (reduction ([],0)).threshold = 15/8 := by decide +kernel

/-- A yes-instance reaches the actual real-randomized-policy decision language. -/
example : reduction ([0,2,2],2) ∈ Decision := by
  rw [reduction_mem_iff,mem_SubsetSum_iff_sublist]
  exact ⟨[2],by decide +kernel,rfl⟩

/-- Equal positive source weights are distinct indexed opportunities. -/
example : (reduction ([2,2],2)).calls.length = 4 := by decide +kernel

/-- A no-instance cannot beat the threshold using real private randomization. -/
example : reduction ([2],1) ∉ Decision := by
  rw [reduction_mem_iff,mem_SubsetSum_iff_sublist]
  rintro ⟨s,hs,he⟩
  have hm := List.mem_sublists.mpr hs
  simp only [List.sublists,List.foldr_cons,List.foldr_nil,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,
    List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl <;> simp at he

open TwoBatchIntegral

/-- The previously checked heterogeneous source instance has integer costs. -/
def costs (i : Fin 2) : ℕ := if i = 0 then 1 else 5

private theorem cost_eq : StochasticOracleApproximation.input.cost = fun i => (costs i : ℚ) := by
  funext i
  fin_cases i <;> norm_num [StochasticOracleApproximation.input,costs]

example : totalCost (Input.ofInstance StochasticOracleApproximation.input costs 3) = 6 := by
  decide +kernel

example : run (Input.ofInstance StochasticOracleApproximation.input costs 3) =
    (true,([0],[1])) := by decide +kernel

example : run (Input.ofInstance StochasticOracleApproximation.input costs 2) =
    (true,([0,1],[])) := by decide +kernel

example : admissible (Input.ofInstance StochasticOracleApproximation.input costs 1) = false := by
  decide +kernel

example : Plan.expectedCost StochasticOracleApproximation.input
    (selectedPlan StochasticOracleApproximation.input costs 3) = 2 := by decide +kernel

example : Plan.success StochasticOracleApproximation.input
    (selectedPlan StochasticOracleApproximation.input costs 3) = 9/10 := by decide +kernel

/-- The returned exact cost is a lower bound against every real-randomized competitor. -/
example (π : Policy (Fin 2) ℝ 2) (hπ : π.Feasible StochasticOracleApproximation.input.realify 3)
    (hp : (π.execution StochasticOracleApproximation.input.realify).mean executionSuccess =
      1 - StochasticOracleApproximation.input.realify.batchFailure Finset.univ) :
    2 ≤ (π.execution StochasticOracleApproximation.input.realify).mean
      (executionCost StochasticOracleApproximation.input.realify) := by
  have h := (optimizer StochasticOracleApproximation.input costs cost_eq 3
    (by decide +kernel)).2.2 π hπ hp
  have hc : Plan.expectedCost StochasticOracleApproximation.input
      (selectedPlan StochasticOracleApproximation.input costs 3) = 2 := by decide +kernel
  rw [hc] at h
  exact_mod_cast h

example : run (⟨[],0⟩ : TwoBatchIntegral.Input) = (true,([],[])) := by decide +kernel
example : run (⟨[],-1⟩ : TwoBatchIntegral.Input) = (false,([],[])) := by decide +kernel
example : budget (⟨[],0⟩ : TwoBatchIntegral.Input) = 2 := by decide +kernel

/-- Empty input also satisfies the exact optimizer theorem, with zero cost. -/
def empty : FullCoverInstance (Fin 0) ℚ where
  success := fun i => Fin.elim0 i
  success_pos := fun i => Fin.elim0 i
  success_lt_one := fun i => Fin.elim0 i
  cost := fun i => Fin.elim0 i
  cost_pos := fun i => Fin.elim0 i
  cutoff := fun i => Fin.elim0 i
  cutoff_pos := fun i => Fin.elim0 i

example : Plan.Feasible empty (selectedPlan empty (fun i => Fin.elim0 i) 0) 0 ∧
    Plan.expectedCost empty (selectedPlan empty (fun i => Fin.elim0 i) 0) = 0 := by
  refine ⟨(optimizer empty (fun i => Fin.elim0 i) (by funext i; exact Fin.elim0 i)
    0 (by decide +kernel)).1,?_⟩
  decide +kernel

example : ¬ ∃ π : Policy (Fin 2) ℝ 2, π.Feasible StochasticOracleApproximation.input.realify 1 ∧
    (π.execution StochasticOracleApproximation.input.realify).mean executionSuccess =
      1 - StochasticOracleApproximation.input.realify.batchFailure Finset.univ := by
  simpa only [Rat.cast_one] using
    infeasible StochasticOracleApproximation.input costs 1 (by decide +kernel)

/-- A single call has zero achievable saving and an empty second batch. -/
example : run (⟨[(1/2,3,1)],1⟩ : TwoBatchIntegral.Input) = (true,([0],[])) := by decide +kernel

end ComplexityTests.StochasticOracleExact
