/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualAttainment
import CslibFrontierTests.StochasticOracleResidualCover
import Mathlib.Tactic

/-!
# Attained native residual cost on overlapping X3C blocks

The original point enumeration is arbitrary. Five six-point blocks include
unused overlapping triples. Every near residual has positive probability;
its identity controls the actual second query and its invoice. The same compiled
program has certified tape success one and expected accrued bill five, and
attains the existing native OPT. No successful execution or bill is a premise.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleNativeResidualAttainment
open Cslib.Probability StochasticOracle NativeRetention ResidualCover ConcurrentBatch
open NativeResidualAttainment NativeOpenExecution Turing
open Cslib.Optimization.OneConstraint
open scoped ENNReal NNReal

private abbrev blocks := StochasticOracleResidualCover.blocks
private def points : Fin (Fintype.card (Point blocks)) ≃ Point blocks :=
  (Fintype.equivFin _).symm
private def candidates : Fin (Fintype.card (Candidate blocks)) ≃ Candidate blocks :=
  (Fintype.equivFin _).symm
private def invoice (i : Fin 6) : ℕ := if i = 0 then 2 else i.val
private def parameters : Parameters 5 where
  missing := StochasticOracleResidualCover.parameters.missing
  full_support := StochasticOracleResidualCover.parameters.full_support
  nearCost := 2
  near_pos := by norm_num
  specialistCost j := j.val + 1
  specialist_pos j := by positivity

private theorem invoice_zero : invoice 0 = 2 := rfl
private theorem invoice_succ (j : Fin 5) : invoice j.succ = j.val + 1 := by
  simp only [invoice, Fin.succ_ne_zero, ite_false, Fin.val_succ]

private theorem prices (i : Fin 6) : (invoice i : ℝ) =
    (finSuccEquiv 5 i).elim parameters.nearCost parameters.specialistCost := by
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num [invoice, parameters]
  · rw [finSuccEquiv_succ]
    simp only [parameters, invoice_succ, Option.elim_some, Nat.cast_add, Nat.cast_one]

private theorem source_cost : parameters.nearCost + parameters.missing.mean
    parameters.specialistCost = 5 := by
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean,
    Fin.sum_univ_succ]

private theorem cheaper : parameters.nearCost + parameters.missing.mean
    parameters.specialistCost ≤ ∑ j, parameters.specialistCost j := by
  rw [source_cost]
  norm_num [parameters, Fin.sum_univ_succ]

-- This is the original Theorem 5 native infimum over all admitted finite-control
-- competitors on the same input, source oracle and seed. It is finite and attained.
example : BatchOptimum.optimum limits
    (NativeResidualOracle.sample blocks points candidates parameters invoice)
    (input blocks points candidates) () (valid blocks points candidates (by norm_num)) 1 = 5 := by
  rw [native_optimum_of_adaptive_le blocks points candidates parameters invoice
    (by norm_num) prices cheaper, source_cost]
  norm_num

-- The witness is the concrete uniform runtime-routing native controller, with
-- actual accrued bill (not a behavioral cost score or a supplied resource bound).
example : NativeBatch.Quantitative.expected limits
    (NativeResidualOracle.sample blocks points candidates parameters invoice)
    (NativeResidualRouting.controller true).program NativeBatch.Trace.charge 3
    ⟨(NativeResidualRouting.controller true).program.initialConfig
      (GuardedStartup.encoding (input blocks points candidates)), initialMemory⟩ = 5 := by
  rw [native_expected_cost blocks points candidates parameters invoice (by norm_num) prices,
    source_cost]
  norm_num

example : ((NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
    (environment limits (NativeResidualOracle.sample blocks points candidates parameters invoice))
    ⟨(NativeResidualRouting.controller true).program.initialConfig
      (GuardedStartup.encoding (input blocks points candidates)), initialMemory⟩).map
      (BatchOutput.certified limits (input blocks points candidates).startup.system
        (valid blocks points candidates (by norm_num)))) true = 1 :=
  native_certified blocks points candidates parameters invoice (by norm_num)

-- Joint billing still reveals the hidden missing block: different second query
-- labels have different positive invoices, while the concurrent deadline is two.
example : (NativeUnboundedExecution.terminal (NativeResidualRouting.controller true).program
    (environment limits (NativeResidualOracle.sample blocks points candidates parameters invoice))
    ⟨(NativeResidualRouting.controller true).program.initialConfig
      (GuardedStartup.encoding (input blocks points candidates)), initialMemory⟩).map
      (Option.map fun world => (tokenBill world.memory.events, elapsed world.memory.events)) =
    parameters.missing.toPMF.map (fun j => some
      (((2 + (j.val + 1) : ℕ) : ℝ≥0), (2 : ℝ≥0))) := by
  rw [native_resources blocks points candidates parameters invoice (by norm_num)]
  apply congrArg (fun f => parameters.missing.toPMF.map f)
  funext j
  simp only [invoice_zero, invoice_succ]

example (j : Fin 5) :
    NativeResidualRouting.slots (afterNear blocks points candidates j (invoice 0)) =
      (fun i : Fin 6 => if i = j.succ then
        some (NativeResidualOracle.query blocks points candidates i) else none) :=
  second_slots blocks points candidates (by norm_num) j (invoice 0)

-- Metadata is physically decoded from the first private frame and survives even
-- an empty reply and a long arbitrary reply suffix; it contains no hidden cover.
example (word : List Bool) :
    NativeResidualRouting.roles (RuntimeControl.afterReply
      (NativeResidualRouting.initial true (input blocks points candidates)) word) =
      universes blocks points := NativeResidualRouting.roles_afterReply _ _ rfl word

example : NativeResidualRouting.sameUniverse [3, 1, 3] [1, 3] = true := rfl
example : NativeResidualRouting.sameUniverse [3, 1] [1, 2] = false := rfl

end CslibFrontierTests.StochasticOracleNativeResidualAttainment
