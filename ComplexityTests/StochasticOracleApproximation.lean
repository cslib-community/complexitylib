/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.TwoBatchBinary
import Complexity.Probability.StochasticOracle.TwoBatchGuarantees
import Complexity.Probability.StochasticOracle.TwoBatchResources
import Complexity.Algorithms.Lean.DynamicProgramming.Native
import Complexity.Algorithms.Lean.DynamicProgramming.MinProduct
import Complexity.Algorithms.Lean.DynamicProgramming.RoundedProduct
import Complexity.Probability.StochasticOracle.FullCover
import Mathlib.Tactic

/-!
# Executable two-batch approximation clients

These clients exercise the actual algorithm, including zero-rounded-cost collisions,
mandatory selections, heterogeneous deadlines, and zero-saving fallback. They do
exercise the global approximation, native arithmetic/table APIs and complete
binary-input selector, including its derived precision budget and invalid inputs.
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

/-- The savings guarantee covers arbitrary real private randomization. -/
example (π : Policy (Fin 2) ℝ 2) (hπ : π.Feasible input.realify 3)
    (hp : (π.execution input.realify).mean executionSuccess =
      1 - input.realify.batchFailure Finset.univ) :
    (Plan.expectedCost input (n := 2)
      (TwoBatchApproximation.choose input (1 / 2) 3,
        ((TwoBatchApproximation.choose input (1 / 2) 3)ᶜ,())) : ℚ) ≤
      ((π.execution input.realify).mean (executionCost input.realify) + 6) / 2 := by
  have h := (TwoBatchApproximation.choose_real_policy_approximation input
    (by decide) (by norm_num : (0 : ℚ) < 1 / 2) (by norm_num : (1 / 2 : ℚ) < 1)
    π hπ hp).2
  have hc : input.batchCost Finset.univ = 6 := by
    norm_num [FullCoverInstance.batchCost, input, Finset.univ_fin2]
  rw [hc] at h
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  linarith

/-- A collision with tiny optional costs must retain a nonempty first batch. -/
def collisionInput : FullCoverInstance (Fin 3) ℚ where
  success _ := 1 / 2
  success_pos _ := by norm_num
  success_lt_one _ := by norm_num
  cost i := if i = 0 then 100 else 1
  cost_pos _ := by split_ifs <;> norm_num
  cutoff _ := 1
  cutoff_pos _ := by norm_num

example : TwoBatchApproximation.choose collisionInput (3 / 4) 2 = {1,2} := by
  decide +kernel

example : TwoBatchApproximation.gain collisionInput
    (TwoBatchApproximation.choose collisionInput (3 / 4) 2) = 75 := by decide +kernel

example : (3 / 4 : ℚ) * TwoBatchApproximation.gain input {0} ≤
    TwoBatchApproximation.gain input (TwoBatchApproximation.choose input (1 / 4) 3) := by
  let : DecidableEq (Fin 2) := Classical.decEq _
  have hf : input.TwoBatchFeasible 3 {0} := by
    constructor
    · simp
    · have hcomp : ({0} : Finset (Fin 2))ᶜ = {1} := by
        ext i
        fin_cases i <;> simp
      change input.batchDuration {0} + input.batchDuration ({0} : Finset (Fin 2))ᶜ ≤ 3
      rw [hcomp]
      norm_num [FullCoverInstance.batchDuration, input]
  convert TwoBatchApproximation.choose_approximation input
    (ε := 1 / 4) (by norm_num) hf using 1; norm_num

example : (TwoBatchApproximation.candidates input (1 / 2) 3).length ≤ 234 := by
  exact TwoBatchApproximation.candidates_length_le input (by norm_num) 2 (by norm_num) 3

example : (Turing.MultiTapeTM.encRatBin (1 / 3)).length = 7 := by decide +kernel
example : Turing.MultiTapeTM.encRatBin (2 / 6) =
    Turing.MultiTapeTM.encRatBin (1 / 3) := by decide +kernel
example : Turing.MultiTapeTM.encRatBin (-1 / 3) ≠
    Turing.MultiTapeTM.encRatBin (1 / 3) := by decide +kernel

/-- Actual native binary normalization, not a unit rational-operation premise. -/
example : Turing.MultiTapeTM.ComputableInPolyTime (fun p : ℤ × ℕ => mkRat p.1 p.2)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encIntBin Turing.MultiTapeTM.encNat)
    Turing.MultiTapeTM.encRatBin := Turing.MultiTapeTM.ComputableInPolyTime.ratBin_mkRat

example : mkRat (-6) 8 = -3 / 4 := by decide +kernel
example : mkRat 7 0 = 0 := by decide +kernel
example : (⌊(-7 / 3 : ℚ)⌋₊ : ℕ) = 0 := by decide +kernel
example : (⌊(7 / 3 : ℚ)⌋₊ : ℕ) = 2 := by decide +kernel

/-- Insertion/pruning reuse their original exact list implementation and tie rule. -/
example : prune Entry.rounded Entry.product
    ([⟨0,3 / 4,[0]⟩,⟨0,1 / 2,[1]⟩,⟨1,1 / 3,[2]⟩] : List (Entry ℕ)) =
    [⟨1,1 / 3,[2]⟩,⟨0,1 / 2,[1]⟩] := by decide +kernel

example : Turing.MultiTapeTM.ComputableInPolyTime
    (prune (Entry.rounded (ι := ℕ)) Entry.product)
    (Turing.MultiTapeTM.encList (encEntry Turing.MultiTapeTM.encNat))
    (Turing.MultiTapeTM.encList (encEntry Turing.MultiTapeTM.encNat)) :=
  computable_prune Turing.MultiTapeTM.encNat

/-- The complete external algorithm derives its precision budget and executes
all cutoff, DP, reconstruction and comparison stages on the source example. -/
example : TwoBatchNative.run (TwoBatchNative.BinaryInput.ofInstance input (1 / 2) 3) = [0] := by
  decide +kernel

example : TwoBatchNative.precision
    (TwoBatchNative.BinaryInput.ofInstance input (1 / 2) 3) = 3 := by decide +kernel

example : TwoBatchNative.run (TwoBatchNative.BinaryInput.ofInstance input (1 / 2) 2) = [0,1] := by
  decide +kernel

example : TwoBatchNative.run
    (TwoBatchNative.BinaryInput.ofInstance collisionInput (3 / 4) 2) = [1,2] := by
  decide +kernel

example : TwoBatchNative.runSchedule
    (TwoBatchNative.BinaryInput.ofInstance input (1 / 2) 3) = ([0],[1]) := by decide +kernel

/-- There is one total algorithm even for empty, negative-tolerance or zero-cost data. -/
example : TwoBatchNative.run ⟨0,0,[]⟩ = [] := by decide +kernel
example : TwoBatchNative.run ⟨-1,2,[(1 / 2,0,1)]⟩ = [0] := by decide +kernel

/-- The complete selector retains the source example's exact success probability. -/
example : Plan.success input (TwoBatchNative.selectedPlan input (1 / 2) 3) = 9 / 10 := by
  rw [TwoBatchNative.selectedPlan_eq input (by norm_num)]
  rw [TwoBatchApproximation.choose_success]
  norm_num [FullCoverInstance.batchFailure, input, Finset.univ_fin2]

example : TwoBatchNative.runtimeSize (TwoBatchNative.BinaryInput.ofInstance input (1 / 2) 3) =
    TwoBatchApproximation.inputSize input (1 / 2) 3 + 3 := by decide +kernel

example : TwoBatchNative.runSchedule
    (TwoBatchNative.BinaryInput.ofInstance input (1 / 2) 2) = ([0,1],[]) := by decide +kernel

end ComplexityTests.StochasticOracleApproximation
