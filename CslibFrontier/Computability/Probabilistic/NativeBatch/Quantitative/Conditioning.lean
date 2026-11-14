/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Quantitative
import CslibFrontier.Probability.PMF.Disintegration.Map
import Mathlib.Tactic

/-!
# Native conditional dispatch depends only on the selected checkpoint and receipts

The previous hidden configuration is unnecessary after the actual next source
boundary has been selected. Keeping the selected checkpoint and earlier receipts
preserves both the observed signal and the entire conditional response law.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Quantitative
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- Actual selected checkpoint paired with the retained earlier accepted receipts. -/
@[expose] def Selected.checkpointState (picked : Selected n k Private Control input) :
    Trace.State n k Private Control input :=
  ⟨picked.checkpoint, picked.before.records⟩

/-- Conditional dispatch is unchanged when the old hidden configuration is
forgotten after selecting its replacement. The actual checkpoint and ledger remain. -/
theorem conditional_checkpointState (limits : Limits n) (sample : Sampler n Private)
    (machine : MultiTapePTM k Bool Control Unit)
    (prior : PMF (Trace.State n k Private Control input)) (o : Observation n) :
    conditional limits sample machine prior o =
      (PMF.posterior ((select limits sample machine prior).map Selected.checkpointState)
        (fun state : Trace.State n k Private Control input =>
          (⟨state.records, sourceSignal limits state.hidden⟩ : Observation n)) o).bind
        (fun state => Trace.respond limits sample machine state state.hidden) := by
  rw [← PMF.posterior_map, PMF.bind_map]
  simp only [conditional, Selected.checkpointState, Function.comp_def, Trace.respond]
  rfl

end Cslib.Probability.NativeBatch.Quantitative
