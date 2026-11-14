/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.History
public import CslibFrontier.Probability.PMF.RecordedProcess

/-!
# Actual native receipt and output observations

The actual trace-state law constructs a posterior response kernel on complete
receipt histories, then a conditional final observation of native state. The
resulting sequential receipt/output law is derived from execution, preserving
hidden work tapes and private-coin correlations. Accrued receipts survive silent
divergence; terminal `none` is never used as a replacement for an earlier receipt.
Records start empty at the supplied world: scores account for these epochs, not
charges already present in that world's protocol memory.

These kernels depend on the native machine. A common response kernel across
competitors requires an additional source-state filtering argument. The extra
finalization epoch in `Trace.law_terminal` is kept separate from the issued-call budget.

## Main results

* `records_law`, `joint_law`: exact receipt and private-output observations.
* `expected_accrued`: actual extended receipt-score accounting, including divergence.
* `terminal_law`: original native terminal-world observation at the finalization horizon.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.RecordedObservation
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing Trace
open scoped ENNReal
variable {n k : ℕ} {Private Control O : Type} {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)
  (machine : MultiTapePTM k Bool Control Unit)
  (world : World k Control Unit (ServerState n Private) input)

/-- Native next-receipt distribution from its actual full-history state posterior. -/
@[expose] def response (history : List (Record n)) : PMF (Record n) :=
  RecordedProcess.response (Trace.step limits sample machine) State.records
    (initial world) none history

/-- Actual conditional native observation, rather than fresh independent hidden state. -/
@[expose] def output (observe : State n k Private Control input → O)
    (turns : ℕ) (history : List (Record n)) : PMF O :=
  RecordedProcess.output (Trace.step limits sample machine) State.records (initial world)
    observe turns history

/-- The constructed sequential histories have exactly the actual native receipt law. -/
theorem records_law (turns : ℕ) :
    (PMF.seqProcess (fun _ h => response limits sample machine world (PMF.seqHistory h)) turns).map
      PMF.seqHistory = (Trace.law limits sample machine turns world).map State.records :=
  RecordedProcess.history_law (Trace.step limits sample machine) State.records (initial world) none
    rfl (History.step_records limits sample machine) turns

/-- The complete receipt/private-output joint law, with no supplied abstraction identity. -/
theorem joint_law (observe : State n k Private Control input → O) (turns : ℕ) :
    ((PMF.seqProcess (fun _ h => response limits sample machine world (PMF.seqHistory h)) turns).map
      PMF.seqHistory).bind (fun history =>
        (output limits sample machine world observe turns history).map
        (fun result => (history, result))) =
      (Trace.law limits sample machine turns world).map
        fun state => (state.records, observe state) :=
  RecordedProcess.joint_law (Trace.step limits sample machine) State.records (initial world) none
    rfl (History.step_records limits sample machine) observe turns

/-- Every extended receipt-score mean agrees with the actual native trace accounting.
Receipts collected since this initial world persist when the hidden machine silently
diverges. Pre-existing charges in the supplied world are not part of this new recorder. -/
theorem expected_accrued (score : Record n → ℝ≥0∞) (turns : ℕ) :
    (∑' h, PMF.seqProcess
        (fun _ h => response limits sample machine world (PMF.seqHistory h)) turns h *
      ((PMF.seqHistory h).map score).sum) =
      ∑' state, Trace.law limits sample machine turns world state * Trace.accrued score state :=
  RecordedProcess.expected_sum (Trace.step limits sample machine) State.records (initial world)
    none rfl (History.step_records limits sample machine) score turns

/-- At `limits.turns + 1` epochs, conditional extraction recovers the original
native terminal-world law. This includes divergence and arbitrary silent local work. -/
theorem terminal_law (hi : Invariant limits world.memory) :
    ((PMF.seqProcess (fun _ h => response limits sample machine world (PMF.seqHistory h))
      (limits.turns + 1)).map PMF.seqHistory).bind
        (output limits sample machine world (fun state => state.hidden.map worldOf)
          (limits.turns + 1)) =
      NativeUnboundedExecution.terminal machine (environment limits sample) world := by
  have he := RecordedProcess.output_law (Trace.step limits sample machine) State.records
    (initial world) none rfl (History.step_records limits sample machine)
    (fun state => state.hidden.map worldOf) (limits.turns + 1)
  exact he.trans (Trace.law_native_terminal limits sample machine world hi)

end Cslib.Probability.NativeBatch.RecordedObservation
