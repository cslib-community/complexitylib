/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualRealChoice
import CslibFrontierTests.StochasticOracleResidualCover
import Mathlib.Tactic

/-!
# Actual fractional expected costs for the same compiled price-aware selector

The near call has mean one quarter; each specialist has mean one half. Natural
reports are sampled freshly at each batch and can be correlated within a batch.
The program sees only the rational table, original WSC input and actual replies.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleNativeResidualRealChoice
open Cslib.Probability StochasticOracle NativeRetention ResidualCover ConcurrentBatch
open NativeResidualCostChoice NativeOpenExecution Turing
open Cslib.Optimization.OneConstraint
open scoped ENNReal

private abbrev blocks := StochasticOracleResidualCover.blocks
private def points : Fin (Fintype.card (Point blocks)) ≃ Point blocks :=
  (Fintype.equivFin _).symm
private def candidates : Fin (Fintype.card (Candidate blocks)) ≃ Candidate blocks :=
  (Fintype.equivFin _).symm
private def prices : Prices :=
  ⟨1 / 4, List.ofFn (fun _ : Fin 5 => ⟨1 / 5, 1 / 2⟩)⟩
private def parameters : Parameters 5 where
  missing := StochasticOracleResidualCover.parameters.missing
  full_support := StochasticOracleResidualCover.parameters.full_support
  nearCost := 1 / 4
  near_pos := by norm_num
  specialistCost _ := 1 / 2
  specialist_pos _ := by norm_num

private def reflects : Reflects prices parameters where
  rows _ := ⟨1 / 5, 1 / 2⟩
  entries := rfl
  near := by norm_num [prices, parameters]
  probability j := by norm_num [parameters, StochasticOracleResidualCover.parameters]
  price j := by norm_num [parameters]

example : adaptive prices = true := by
  norm_num [adaptive, adaptiveCost, specialistCost, prices, List.sum_ofFn, Fin.sum_univ_succ]

-- This price is not any constant natural invoice.
example (invoice : ℕ) : (invoice : ℝ) ≠ parameters.nearCost := by
  simp only [parameters]
  have h : (invoice : ℝ) = 0 ∨ 1 ≤ (invoice : ℝ) := by
    by_cases hi : invoice = 0
    · simp [hi]
    · right; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
  rcases h with h | h <;> linarith

-- Actual whole-trace expected bill of the one compiled cost-aware program.
example : NativeBatch.Quantitative.expected NativeResidualAttainment.limits
    (NativeResidualRealCost.sample blocks points candidates parameters)
    controller.program NativeBatch.Trace.charge 3
    ⟨controller.program.initialConfig
      (encoding ⟨NativeResidualAttainment.input blocks points candidates, prices⟩),
      NativeResidualAttainment.initialMemory⟩ = ENNReal.ofReal (3 / 4) := by
  rw [NativeResidualRealChoice.native_expected_cost blocks points candidates parameters
    (by norm_num) prices reflects]
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean,
    Fin.sum_univ_succ]

example : ((NativeUnboundedExecution.terminal controller.program
    (environment NativeResidualAttainment.limits
      (NativeResidualRealCost.sample blocks points candidates parameters))
    ⟨controller.program.initialConfig
      (encoding ⟨NativeResidualAttainment.input blocks points candidates, prices⟩),
      NativeResidualAttainment.initialMemory⟩).map
    (BatchOutput.certified NativeResidualAttainment.limits
      (NativeResidualAttainment.input blocks points candidates).startup.system
      (NativeResidualAttainment.valid blocks points candidates (by norm_num)))) true = 1 :=
  NativeResidualRealChoice.native_certified blocks points candidates parameters (by norm_num) prices

example : ENNReal.ofReal (3 / 4) ∈ BatchOptimum.costs NativeResidualAttainment.limits
    (NativeResidualRealCost.sample blocks points candidates parameters)
    (packed ⟨NativeResidualAttainment.input blocks points candidates, prices⟩) ()
    (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1 := by
  have h := NativeResidualRealChoice.native_cost_mem blocks points candidates parameters
    (by norm_num) prices reflects
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean,
    Fin.sum_univ_succ] at h ⊢
  exact h

end CslibFrontierTests.StochasticOracleNativeResidualRealChoice
