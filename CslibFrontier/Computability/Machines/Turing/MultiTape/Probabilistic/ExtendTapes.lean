/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Reserving work tapes for probabilistic machines

The common tape compiler applies to Boolean-indexed choices by naturality of mapping a coin
program. It preserves the program itself, allowing stateful coin and query interpreters.

## Main definitions

* `Turing.MultiTapePTM.extendTapes`: reindex the source tapes, retaining unused tapes.

## Main results

* `Turing.MultiTapePTM.runConfigFrom_embed`: preserve the clocked configuration program.
* `Turing.MultiTapePTM.runClosed_extendTapes`: preserve the closed fair-coin program.

## References

The common proof in `MultiTape.Machine.ExtendTapes` adapts the cslib `crypto` branch's
MultiTape/Oracle/ExtendTapes.lean at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k k' : ℕ} {Symbol State Oracle Query : Type} {spec : OracleSpec.{0, 0} Query}
  {input : List Symbol}

/-- The common tape compiler specialized to Boolean-indexed transitions. -/
abbrev extendTapes (machine : MultiTapePTM k Symbol State Oracle) (e : Fin k ↪ Fin k') :
    MultiTapePTM k' Symbol State Oracle := MultiTapeMachine.extendTapes machine e

/-- Reindexing preserves the entire program and all contents on additional tapes. -/
theorem runConfigFrom_embed [DecidableEq Oracle] (machine : MultiTapePTM k Symbol State Oracle)
    (e : Fin k ↪ Fin k') (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (cfg : Config k Symbol State Oracle input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (fuel : ℕ) :
    (machine.extendTapes e).runConfigFrom coin query fuel (cfg.embed e extraTapes extraPos) =
      (fun final => final.embed e extraTapes extraPos) <$>
        machine.runConfigFrom coin query fuel cfg :=
  MultiTapeMachine.runConfigFrom_embed machine e (fun choices => choices <$> coin)
    (fun _ _ => by rw [Functor.map_map]; rfl) query cfg extraTapes extraPos fuel

/-- Reserving blank scratch tapes preserves the closed program, before interpretation. -/
theorem runClosed_extendTapes (machine : MultiTapePTM k Symbol State)
    (e : Fin k ↪ Fin k') (fuel : ℕ) (input : List Symbol) :
    (machine.extendTapes e).runClosed fuel input = machine.runClosed fuel input :=
  MultiTapeMachine.run_extendTapes machine e
    (fun choices => choices <$> ProbComp.uniform Bool)
    (fun _ _ => by rw [Functor.map_map]; rfl) Empty.elim fuel input

end Turing.MultiTapePTM
