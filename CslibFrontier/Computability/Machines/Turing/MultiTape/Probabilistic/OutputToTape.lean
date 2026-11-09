/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.OutputToTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Buffering probabilistic machine output

The common output compiler applies directly to Boolean-indexed choices, preserving the whole
typed program, including stateful coin and query effects. The buffer starts blank.

## Main definitions

* `Turing.MultiTapePTM.outputToTape`: redirect output to a fresh work tape.

## Main results

* `Turing.MultiTapePTM.runConfigFrom_outputToTape`: preserve the source configuration program.

## References

Specializes `MultiTape.Machine.OutputToTape`, adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` and upstream's deterministic output redirection.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {spec : OracleSpec.{0, 0} Query}
  {input : List Symbol}

/-- The common output compiler specialized to Boolean-indexed transitions. -/
abbrev outputToTape (machine : MultiTapePTM k Symbol State Oracle) :
    MultiTapePTM (k + 1) Symbol State Oracle := MultiTapeMachine.outputToTape machine

/-- Buffer output while retaining the complete clocked program and every oracle channel. -/
theorem runConfigFrom_outputToTape [DecidableEq Oracle]
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    machine.outputToTape.runConfigFrom coin query fuel (OutputToTape.config cfg) =
      OutputToTape.config <$> machine.runConfigFrom coin query fuel cfg :=
  MultiTapeMachine.runConfigFrom_outputToTape machine (fun choices => choices <$> coin)
    (fun _ _ => by rw [Functor.map_map]; rfl) query fuel cfg

end Turing.MultiTapePTM
