/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction
public import CslibFrontier.Computability.Probabilistic.NativeBatch.History
import CslibFrontier.Probability.PMF.Expect

/-!
# Actual response rewards from the fixed enriched source

History-dependent invoice and progress scores can be averaged under the same
actual source response law. The complete receipt and latent successor remain
joint in `response_trace`; averaging a receipt score forgets only the subsequent
native checkpoint. Rewards take values in the nonnegative extended reals, so no
integrability or bounded-invoice premise is needed. Halt and divergence retain
the source's explicit no-call record and all earlier receipts.

## Main results

* `response_reward`: the actual native newest-reward mean equals the fixed source mean.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Interaction
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing
open scoped ENNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- Any history-dependent receipt reward has the actual fixed source mean at a
selected source boundary, including no-call outcomes. The normalized native
continuation cannot alter a reward of the receipt it has just received. -/
theorem response_reward (limits : Limits n) (sample : Sampler n Private)
    (initial : PMF Private) (machine : MultiTapePTM k Bool Control Unit)
    (state : State n k Private Control input)
    (hit : Option (Phase k Control Unit (ServerState n Unit) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase)
    (reward : List (Trace.Record n) → Trace.Record n → ℝ≥0∞) :
    Quantitative.mean (Trace.respond limits sample machine (trace state)
      (hit.map (Phase.mapMemory (Memory.mapPrivate
        (ServerState.mapPrivate fun _ => state.sourceState))))) (History.newest reward) =
      ∑' pair, ((StochasticOracle.ConcurrentBatch.Interaction.source limits sample initial).step
        state.history state.sourceState (request limits hit)) pair *
          reward (state.history.map Prod.snd) pair.1 := by
  unfold Quantitative.mean
  rw [← response_trace limits sample initial machine state hit hb, PMF.tsum_bind_mul]
  apply tsum_congr
  intro pair
  rw [PMF.tsum_map_mul]
  simp only [History.newest, List.tail_cons, List.headD_cons,
    ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Cslib.Probability.NativeBatch.Interaction
