/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch
public import CslibFrontier.Probability.StochasticOracle.PartialCover
import Mathlib.Tactic

/-!
# Shared singleton-cover source for actual native clients

The successful deterministic native program and its randomized retention sibling
use the same actual one-opportunity sampler, complete receipt and covering instance.
The fixture is an ordinary module, independent of either machine implementation.
-/

public section
noncomputable section
namespace CslibFrontierTests.NativeBatchSingleton
open Cslib.Probability Cslib.Probability.StochasticOracle
open ConcurrentBatch PartialCover
open scoped ENNReal NNReal

/-- A satisfiable nonempty ground with a feasible positive dual. -/
@[expose] def coverInstance : Instance Unit (Fin 1) where
  ground := {()}
  sets _ := {()}
  sets_subset := by intro _; exact Finset.Subset.rfl
  weight _ := 1
  weight_nonneg := by intro _; norm_num
  dual _ := 1
  dual_nonneg := by intro _; norm_num
  dual_feasible := by intro _; norm_num

/-- One issued turn, unit cutoff and two units of external time. -/
@[expose] def limits : Limits 1 := ⟨fun _ => 1, by intro _; norm_num, 2, 1⟩

/-- The single opportunity is a nonempty batch with its empty word preformed. -/
@[expose] def batch : Batch 1 := ⟨fun _ => some [], ⟨0, by simp [active]⟩⟩

/-- The oracle returns the unique original set and charges two tokens. -/
@[expose] def path : CallTrace := ⟨some (1, encodeFamily ({0} : Finset (Fin 1))),
  fun _ => 2, by intro _ _ _; exact le_rfl⟩

/-- One deterministic oracle shared across all histories. -/
@[expose] def sample : Sampler 1 Unit := fun _ _ => PMF.pure (fun _ => path, ())

/-- The actual accepted source receipt, including its concrete report. -/
@[expose] def receipt : Exchange 1 := ConcurrentBatch.observe limits 2 batch (fun _ => path)

/-- The actual one-opportunity receipt proposes the unique original candidate. -/
theorem receipt_proposals : proposals 1 receipt.report = [{0}] := by
  norm_num [proposals, receipt, ConcurrentBatch.observe, path, limits, batch,
    CallTrace.report, CallTrace.response, CallTrace.stop, encodeFamily, decodeFamily,
    List.ofFn_succ, Finset.mem_filter, List.filterMap_cons, List.filterMap_nil]

end CslibFrontierTests.NativeBatchSingleton
