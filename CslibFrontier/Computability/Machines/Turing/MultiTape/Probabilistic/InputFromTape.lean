/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Probabilistic machines reading a buffered input

The common virtual-input compiler applies directly to Boolean-indexed choices, preserving the
whole typed program, including stateful coin and query effects. Preparing the buffer is separate.

## Main definitions

* `Turing.MultiTapePTM.inputFromTape`: read the input from a word and a boundary-marker tape.

## Main results

* `Turing.MultiTapePTM.runConfigFrom_inputFromTape`: preserve the source configuration program.

## References

Specializes `MultiTape.Machine.InputFromTape`, adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` and upstream's deterministic input redirection.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {spec : OracleSpec.{0, 0} Query}
  {input : List Symbol}

/-- The common virtual-input compiler specialized to Boolean-indexed transitions. -/
abbrev inputFromTape (machine : MultiTapePTM k Symbol State Oracle) :
    MultiTapePTM (k + 2) Symbol State Oracle := MultiTapeMachine.inputFromTape machine

/-- Read a prepared virtual input, preserving the complete clocked program and oracle channels. -/
theorem runConfigFrom_inputFromTape [DecidableEq Oracle]
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (mark : Symbol) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) (outerInput : List Symbol)
    (outerPosition : Fin (outerInput.length + 2)) :
    machine.inputFromTape.runConfigFrom coin query fuel
        (InputFromTape.config mark cfg outerInput outerPosition) =
      (fun final => InputFromTape.config mark final outerInput outerPosition) <$>
        machine.runConfigFrom coin query fuel cfg :=
  MultiTapeMachine.runConfigFrom_inputFromTape machine (fun choices => choices <$> coin)
    (fun _ _ => by rw [Functor.map_map]; rfl) query mark fuel cfg outerInput outerPosition

end Turing.MultiTapePTM
