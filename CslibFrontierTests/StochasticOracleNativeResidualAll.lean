/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualMinima
import CslibFrontierTests.StochasticOracleResidualCover
import Mathlib.Tactic

/-!
# Attained all-specialist native minimum

Five nontrivial overlapping-triple blocks have specialist invoices one through
five. The near invoice is twenty, so all specialists cost fifteen while the
adaptive controller costs twenty-three. The same original-input all-specialist
program succeeds with one or two permitted source turns, without seeing a hidden
cover in its original input. All conclusions concern actual compiled execution.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleNativeResidualAll
open Cslib.Probability StochasticOracle NativeRetention ResidualCover ConcurrentBatch
open NativeResidualAttainment NativeOpenExecution Turing
open Cslib.Optimization.OneConstraint
open scoped ENNReal NNReal

private abbrev blocks := StochasticOracleResidualCover.blocks
private def points : Fin (Fintype.card (Point blocks)) ≃ Point blocks :=
  (Fintype.equivFin _).symm
private def candidates : Fin (Fintype.card (Candidate blocks)) ≃ Candidate blocks :=
  (Fintype.equivFin _).symm
private def invoice (i : Fin 6) : ℕ := if i = 0 then 20 else i.val
private def parameters : Parameters 5 where
  missing := StochasticOracleResidualCover.parameters.missing
  full_support := StochasticOracleResidualCover.parameters.full_support
  nearCost := 20
  near_pos := by norm_num
  specialistCost j := j.val + 1
  specialist_pos j := by positivity

private theorem invoice_succ (j : Fin 5) : invoice j.succ = j.val + 1 := by
  simp only [invoice, Fin.succ_ne_zero, ite_false, Fin.val_succ]

private theorem prices (i : Fin 6) : (invoice i : ℝ) =
    (finSuccEquiv 5 i).elim parameters.nearCost parameters.specialistCost := by
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num [invoice, parameters]
  · rw [finSuccEquiv_succ]
    simp only [parameters, invoice_succ, Option.elim_some, Nat.cast_add, Nat.cast_one]

private theorem source_minimum : min (∑ j, parameters.specialistCost j)
    (parameters.nearCost + parameters.missing.mean parameters.specialistCost) = 15 := by
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean,
    Fin.sum_univ_succ]

-- The actual native optimum, over every admitted finite-control competitor.
example : BatchOptimum.optimum limits
    (NativeResidualOracle.sample blocks points candidates parameters invoice)
    (input blocks points candidates) () (valid blocks points candidates (by norm_num)) 1 = 15 := by
  rw [NativeResidualMinima.native_optimum blocks points candidates parameters invoice
    (by norm_num) prices, source_minimum]
  norm_num

-- The witness is the fixed all-specialist program, not a supplied resource law.
example (budget : ℕ) (hb : 0 < budget) :
    NativeBatch.Quantitative.expected (NativeResidualAll.config budget)
      (NativeResidualOracle.sample blocks points candidates parameters invoice)
      (NativeResidualRouting.controller false).program NativeBatch.Trace.charge (budget + 1)
      ⟨(NativeResidualRouting.controller false).program.initialConfig
        (GuardedStartup.encoding (input blocks points candidates)), initialMemory⟩ = 15 := by
  rw [NativeResidualAll.native_expected_cost blocks points candidates parameters invoice
    (by norm_num) budget hb prices]
  norm_num [parameters, Fin.sum_univ_succ]

-- In particular the same program has one-turn certified tape success one.
example : ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
    (environment (NativeResidualAll.config 1)
      (NativeResidualOracle.sample blocks points candidates parameters invoice))
    ⟨(NativeResidualRouting.controller false).program.initialConfig
      (GuardedStartup.encoding (input blocks points candidates)), initialMemory⟩).map
      (BatchOutput.certified (NativeResidualAll.config 1)
        (input blocks points candidates).startup.system
        (valid blocks points candidates (by norm_num)))) true = 1 :=
  NativeResidualAll.native_certified blocks points candidates parameters invoice
    (by norm_num) 1 (by norm_num)

-- The all-specialist upper bound also applies to the original one-turn OPT.
example : BatchOptimum.optimum (NativeResidualAll.config 1)
    (NativeResidualOracle.sample blocks points candidates parameters invoice)
    (input blocks points candidates) () (valid blocks points candidates (by norm_num)) 1 ≤ 15 := by
  have h := NativeResidualAll.native_upper blocks points candidates parameters invoice
    (by norm_num) 1 (by norm_num) prices
  norm_num [parameters, Fin.sum_univ_succ] at h ⊢
  exact h

-- All calls are concurrent: the joint resource law has bill fifteen and duration one.
example : (NativeUnboundedExecution.terminal (NativeResidualRouting.controller false).program
    (environment (NativeResidualAll.config 2)
      (NativeResidualOracle.sample blocks points candidates parameters invoice))
    ⟨(NativeResidualRouting.controller false).program.initialConfig
      (GuardedStartup.encoding (input blocks points candidates)), initialMemory⟩).map
      (Option.map fun world => (tokenBill world.memory.events, elapsed world.memory.events)) =
        PMF.pure (some (15, 1)) := by
  rw [NativeResidualAll.native_resources blocks points candidates parameters invoice
    (by norm_num) 2 (by norm_num)]
  norm_num [invoice_succ, Fin.sum_univ_succ]

end CslibFrontierTests.StochasticOracleNativeResidualAll
