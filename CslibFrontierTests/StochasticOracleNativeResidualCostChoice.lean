/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualCostChoice
import CslibFrontierTests.StochasticOracleResidualCover
import Mathlib.Tactic

/-!
# One actual cost-aware program on both source alternatives

Only the original encoded rational price table changes. The fixed native code
selects adaptation for near price two and all specialists for near price twenty,
with the same five nontrivial X3C blocks and uniform missing-block law.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleNativeResidualCostChoice
open Cslib.Probability StochasticOracle NativeRetention ResidualCover ConcurrentBatch
open NativeResidualCostChoice NativeOpenExecution Turing
open Cslib.Optimization.OneConstraint
open scoped ENNReal

private abbrev blocks := StochasticOracleResidualCover.blocks
private def points : Fin (Fintype.card (Point blocks)) ≃ Point blocks :=
  (Fintype.equivFin _).symm
private def candidates : Fin (Fintype.card (Candidate blocks)) ≃ Candidate blocks :=
  (Fintype.equivFin _).symm
private def prices (near : ℕ) : Prices :=
  ⟨near, List.ofFn (fun j : Fin 5 => ⟨1 / 5, j.val + 1⟩)⟩
private def invoice (near : ℕ) (i : Fin 6) : ℕ := if i = 0 then near else i.val
private def parameters (near : ℕ) (hn : 0 < near) : Parameters 5 where
  missing := StochasticOracleResidualCover.parameters.missing
  full_support := StochasticOracleResidualCover.parameters.full_support
  nearCost := near
  near_pos := by exact_mod_cast hn
  specialistCost j := j.val + 1
  specialist_pos j := by positivity

private def reflects (near : ℕ) (hn : 0 < near) :
    Reflects (prices near) (parameters near hn) where
  rows j := ⟨1 / 5, j.val + 1⟩
  entries := rfl
  near := by simp [prices, parameters]
  probability j := by norm_num [parameters, StochasticOracleResidualCover.parameters]
  price j := by simp [parameters]

private theorem wire_prices (near : ℕ) (hn : 0 < near) (i : Fin 6) :
    (invoice near i : ℝ) =
      (finSuccEquiv 5 i).elim (parameters near hn).nearCost
        (parameters near hn).specialistCost := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [invoice, parameters]
  · rw [finSuccEquiv_succ]
    simp only [invoice, parameters, Fin.succ_ne_zero, ite_false, Fin.val_succ,
      Option.elim_some, Nat.cast_add, Nat.cast_one]

example : adaptive (prices 2) = true := by
  norm_num [adaptive, adaptiveCost, specialistCost, prices, List.sum_ofFn, Fin.sum_univ_succ]

example : adaptive (prices 20) = false := by
  norm_num [adaptive, adaptiveCost, specialistCost, prices, List.sum_ofFn, Fin.sum_univ_succ]

-- An exact tie chooses adaptation; this is an actual runtime arithmetic branch.
example : adaptive (prices 12) = true := by
  norm_num [adaptive, adaptiveCost, specialistCost, prices, List.sum_ofFn, Fin.sum_univ_succ]

-- Both instances below execute this same controller.program, not a host-selected program.
example : NativeBatch.Quantitative.expected NativeResidualAttainment.limits
    (NativeResidualOracle.sample blocks points candidates (parameters 2 (by norm_num)) (invoice 2))
    controller.program NativeBatch.Trace.charge 3
    ⟨controller.program.initialConfig
      (encoding ⟨NativeResidualAttainment.input blocks points candidates, prices 2⟩),
      NativeResidualAttainment.initialMemory⟩ = 5 := by
  rw [native_expected_cost blocks points candidates (parameters 2 (by norm_num)) (invoice 2)
    (by norm_num) (prices 2) (reflects 2 (by norm_num)) (wire_prices 2 (by norm_num))]
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean,
    Fin.sum_univ_succ]

example : NativeBatch.Quantitative.expected NativeResidualAttainment.limits
    (NativeResidualOracle.sample blocks points candidates
      (parameters 20 (by norm_num)) (invoice 20))
    controller.program NativeBatch.Trace.charge 3
    ⟨controller.program.initialConfig
      (encoding ⟨NativeResidualAttainment.input blocks points candidates, prices 20⟩),
      NativeResidualAttainment.initialMemory⟩ = 15 := by
  rw [native_expected_cost blocks points candidates (parameters 20 (by norm_num)) (invoice 20)
    (by norm_num) (prices 20) (reflects 20 (by norm_num)) (wire_prices 20 (by norm_num))]
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean,
    Fin.sum_univ_succ]

example (near : ℕ) (hn : 0 < near) :
    ((NativeUnboundedExecution.terminal controller.program
      (environment NativeResidualAttainment.limits
        (NativeResidualOracle.sample blocks points candidates (parameters near hn) (invoice near)))
      ⟨controller.program.initialConfig
        (encoding ⟨NativeResidualAttainment.input blocks points candidates, prices near⟩),
        NativeResidualAttainment.initialMemory⟩).map
      (BatchOutput.certified NativeResidualAttainment.limits
        (NativeResidualAttainment.input blocks points candidates).startup.system
        (NativeResidualAttainment.valid blocks points candidates (by norm_num)))) true = 1 :=
  native_certified blocks points candidates (parameters near hn) (invoice near)
    (by norm_num) (prices near)

-- The priced input uses the existing GuardedStartup ABI and the same native OPT.
example (near : ℕ) (hn : 0 < near) :
    BatchOptimum.optimum NativeResidualAttainment.limits
      (NativeResidualOracle.sample blocks points candidates (parameters near hn) (invoice near))
      (packed ⟨NativeResidualAttainment.input blocks points candidates, prices near⟩) ()
      (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1 =
        ENNReal.ofReal (min 15 ((near : ℝ) + 3)) := by
  rw [native_optimum blocks points candidates (parameters near hn) (invoice near)
    (by norm_num) (prices near) (reflects near hn) (wire_prices near hn)]
  congr 1
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean,
    Fin.sum_univ_succ]

end CslibFrontierTests.StochasticOracleNativeResidualCostChoice
