/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.TwoBatchApproximation
import Complexity.Algorithms.Lean.DynamicProgramming.MinProduct
import Complexity.Algorithms.Lean.DynamicProgramming.RoundedProduct
import Complexity.Probability.StochasticOracle.FullCover
import Mathlib.Tactic

/-!
# Executable two-batch approximation clients

These clients exercise the actual algorithm, including zero-rounded-cost collisions,
mandatory selections, heterogeneous deadlines, and zero-saving fallback. They do
not turn the outstanding global approximation/bit-cost proof into an assumption.
-/

open Cslib.Probability.StochasticOracle
open Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
namespace ComplexityTests.StochasticOracleApproximation

/-- The heterogeneous two-oracle example from [Wang2027], PDF p. 8. -/
def input : FullCoverInstance (Fin 2) ℚ where
  success i := if i = 0 then 4 / 5 else 1 / 2
  success_pos i := by split_ifs <;> norm_num
  success_lt_one i := by split_ifs <;> norm_num
  cost i := if i = 0 then 1 else 5
  cost_pos i := by split_ifs <;> norm_num
  cutoff i := if i = 0 then 2 else 1
  cutoff_pos i := by split_ifs <;> norm_num

example : TwoBatchApproximation.choose input (1 / 2) 3 = {0} := by decide +kernel

example : TwoBatchApproximation.gain input
    (TwoBatchApproximation.choose input (1 / 2) 3) = 4 := by decide +kernel

example : TwoBatchApproximation.choose input (1 / 2) 2 = Finset.univ := by decide +kernel

example : TwoBatchApproximation.gain input
    (TwoBatchApproximation.choose input (1 / 2) 2) = 0 := by decide +kernel

example : input.TwoBatchFeasible 3 (TwoBatchApproximation.choose input (1 / 2) 3) := by
  apply TwoBatchApproximation.choose_feasible input (by decide +kernel)
  norm_num [FullCoverInstance.batchDuration, input, Finset.univ_fin2]

example : Plan.success input (n := 2)
    (TwoBatchApproximation.choose input (1 / 2) 3,
      ((TwoBatchApproximation.choose input (1 / 2) 3)ᶜ,())) = 9 / 10 := by
  rw [TwoBatchApproximation.choose_success]
  norm_num [FullCoverInstance.batchFailure, input, Finset.univ_fin2]

/-- The source example's optimum is a lower bound against arbitrary randomized
policies, using the newly packaged nonempty-first-batch reduction. -/
example (π : Policy (Fin 2) ℚ 2) (hπ : π.Feasible input 3)
    (hp : (π.execution input).mean executionSuccess = 1 - input.batchFailure Finset.univ) :
    2 ≤ (π.execution input).mean (executionCost input) := by
  obtain ⟨A,hA,hc⟩ := two_batch_reduction input 3 π hπ hp
  have hmin : ∀ A : Finset (Fin 2), A.Nonempty → 2 ≤ input.twoBatchCost A := by
    intro A hA
    let : DecidableEq (Fin 2) := Classical.decEq _
    have hs : input.batchCost Aᶜ = input.batchCost Finset.univ - input.batchCost A := by
      have ht : input.batchCost A + input.batchCost Aᶜ = input.batchCost Finset.univ :=
        Finset.sum_add_sum_compl A input.cost
      linarith
    rw [FullCoverInstance.twoBatchCost, hs]
    fin_cases A <;>
      norm_num [FullCoverInstance.batchCost, FullCoverInstance.batchFailure,
        input, Finset.univ_fin2] at *
  exact (hmin A hA.1).trans hc

/-- Both items round to zero: minimum product still retains the correct witness. -/
example : run (fun _ : Bool => 0) (fun _ => 1 / 2) ⟨0,1,[]⟩ [true,false] =
    [⟨0,1 / 4,[]⟩] := by decide +kernel

/-- The mandatory initial member survives every choice and compression. -/
example : ∀ e ∈ branch (fun _ : Bool => (1 : ℚ)) (fun _ => 1 / 2)
    (1 / 2) true 1 [false], true ∈ e.selected := by decide +kernel

/-- A concrete nonzero branch obtains the checked multiplicative guarantee. -/
example : ∃ d ∈ branch (fun _ : Bool => (1 : ℚ)) (fun _ => 1 / 2)
    (1 / 2) true 1 [false],
    1 / 2 ≤ d.gain (fun _ => 1) 0 (1 / 2) := by decide +kernel

end ComplexityTests.StochasticOracleApproximation
