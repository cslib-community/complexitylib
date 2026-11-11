/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOutput
import CslibFrontier.Probability.PMF.Bind

/-!
# Certified native tape output as an output/memory observation

## Main results

* `BatchOutput.terminal_certified`: stopped native certification depends only on
  actual output bytes and oracle memory, since every supported terminal world is halted.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchOutput
open Turing NativeOpenExecution ConcurrentBatch
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- Raw output/memory certification, including actual oracle elapsed time. -/
@[expose] def certifiedObservation (limits : Limits n) (x : Input) (hx : Valid x)
    (result : Option (List Bool × Memory Unit (ServerState n Private))) : Bool :=
  result.any fun pair => (decodeFamily x.rows.length pair.1).any fun C =>
    accept x hx C && decide (pair.2.privateState.elapsed ≤ limits.deadline)

/-- On the actual terminal law, certification is an observable of output and
memory. No almost-sure halting, output or resource conclusion is assumed. -/
theorem terminal_certified (limits : Limits n) (sample : Sampler n Private)
    (machine : MultiTapePTM k Bool Control Unit)
    (world : World k Control Unit (ServerState n Private) input)
    (x : Input) (hx : Valid x) :
    (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
      (certified limits x hx) =
    ((NativeUnboundedExecution.terminal machine (environment limits sample) world).map
      (Option.map fun w => (w.config.tapes.output, w.memory))).map
        (certifiedObservation limits x hx) := by
  rw [PMF.map_comp]
  apply PMF.bind_congr_on_support
  intro result hs
  cases result with
  | none => rfl
  | some next =>
    have hh := ((NativeUnboundedExecution.terminal_support machine
      (environment limits sample) world next).mp hs).1
    have hh' : next.config.tapes.state = none := hh
    simp only [certified, certifiedObservation, Option.any_some, Function.comp_def,
      Option.map_some, NativeOpenSelection.result,
      hh', Option.isNone_none, ite_true]

end Cslib.Probability.StochasticOracle.NativeRetention.BatchOutput
