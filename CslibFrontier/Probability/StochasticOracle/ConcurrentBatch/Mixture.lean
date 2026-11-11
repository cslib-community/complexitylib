/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Protocol
import CslibFrontier.Probability.PMF.Bind

/-!
# Fresh mixtures of actual source batch samplers

## Main results

* `environment_mixture`: the guarded handler samples the mixture only after batch admission.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch
open NativeOpenExecution
variable {n : ℕ} {Private I : Type}

/-- A fresh mixture at each selected batch, rather than one latent choice reused
for the whole policy. Rejected requests do not sample it. -/
@[expose] def mixture (μ : PMF I) (samples : I → Sampler n Private) : Sampler n Private :=
  fun s b => μ.bind fun i => samples i s b

/-- Actual response words, resources and private state have the mixed kernel law.
This one-query identity does not assert a global mixture for an adaptive policy. -/
theorem environment_mixture (limits : Limits n) (μ : PMF I) (samples : I → Sampler n Private)
    (q : Unit × Word) (memory : Memory Unit (ServerState n Private)) :
    environment limits (mixture μ samples) q memory =
      μ.bind fun i => environment limits (samples i) q memory := by
  unfold environment serve
  cases he : admit limits memory.privateState q.2 with
  | none => simp
  | some batch => simp only [mixture, PMF.map_bind]

end Cslib.Probability.StochasticOracle.ConcurrentBatch
