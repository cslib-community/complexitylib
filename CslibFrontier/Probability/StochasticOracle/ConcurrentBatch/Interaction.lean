/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Memory
public import CslibFrontier.Probability.PMF.Interaction.Process

/-!
# Fixed source for enriched accepted-batch interactions

One actual sampler draw determines the complete concurrent receipt and the next
source-private state. The analytical observation is the entire `Exchange`, including
its per-call time vector; native continuations consume only `replyOf` that receipt.
This enriched observation need not be recoverable from the native reply bytes.

A request carries an accepted-ledger snapshot and the preformed batch, without
native tapes or raw event logs. An arbitrary generic policy can forge that snapshot;
feasibility must be proved for the generated native class. `draw_serve` identifies
the actual guarded handler only when the supplied request is admitted. No response
kernel identity or posterior factorization is assumed.

## Main definitions

* `Request`, `Request.restore`: an erased-private snapshot and its actual private state.
* `draw`: the joint receipt and successor from one actual source sample.
* `source`: the same fixed source for every private policy, with a no-call branch.

## Main results

* `draw_serve`: the joint draw gives the actual admitted native reply and server update.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch.Interaction
open NativeOpenExecution
variable {n : ℕ} {Private : Type}

/-- An analytical source request retains the accepted ledger but no source-private state. -/
structure Request (n : ℕ) where
  /-- Accepted history, used opportunities and elapsed time with private state erased. -/
  server : ServerState n Unit
  /-- The whole batch is selected before the response draw. -/
  batch : Batch n

/-- Restore only the actual private state, retaining the request's entire accepted ledger. -/
@[expose, simps! privateState used elapsed history] def Request.restore (request : Request n)
    (privateState : Private) : ServerState n Private :=
  request.server.mapPrivate (fun _ => privateState)

/-- The receipt and successor are obtained from the same actual joint trajectory sample. -/
@[expose] def draw (limits : Limits n) (sample : Sampler n Private)
    (privateState : Private) (request : Request n) : PMF (Exchange n × Private) :=
  (sample (request.restore privateState) request.batch).map fun (paths, nextPrivate) =>
    (observe limits (limits.deadline - request.server.elapsed) request.batch paths, nextPrivate)

/-- A fixed source, independent of policy-private state; `none` issues no source call. -/
@[expose] def source (limits : Limits n) (sample : Sampler n Private) (initial : PMF Private) :
    InteractionProcess.Source (Option (Request n)) (Option (Exchange n)) Private where
  initial := initial
  step _ privateState request := match request with
    | none => PMF.pure (none, privateState)
    | some request => (draw limits sample privateState request).map fun (receipt, nextPrivate) =>
        (some receipt, nextPrivate)

/-- An admitted enriched draw has exactly the actual handler's joint reply and
server law, retaining all correlations between the receipt and successor state. -/
theorem draw_serve (limits : Limits n) (sample : Sampler n Private)
    (privateState : Private) (request : Request n)
    (hadmit : admit limits (request.restore privateState) (encodeBatch request.batch) =
      some request.batch) :
    (draw limits sample privateState request).map (fun (receipt, nextPrivate) =>
      (replyOf receipt, commit (request.restore privateState) receipt nextPrivate)) =
        serve limits sample (encodeBatch request.batch) (request.restore privateState) := by
  rw [serve_accepted limits sample _ _ _ hadmit]
  simp only [draw, PMF.map_comp, Function.comp_def, Request.restore_elapsed]

end Cslib.Probability.StochasticOracle.ConcurrentBatch.Interaction
