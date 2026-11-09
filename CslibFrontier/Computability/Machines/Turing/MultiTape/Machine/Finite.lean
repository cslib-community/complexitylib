/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.FiniteConfiguration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Program
public import CslibFrontier.Languages.Probabilistic.Iteration

/-!
# Running the common machine with finite data

The finite interpreter executes the unchanged transition table using cslib's existing tapes.
Its choice and query handlers are the same typed programs as the native interpreter's handlers.
The bounded loop is an ordinary `OracleComp.iterate` program.

Equality of the resulting programs preserves every sampling and external interaction, including
the complete private state of any later interpreter. The representation theorem is independent
of efficient handlers or finite control. Efficient encoded realization remains subsequent work.

## Main definitions

* `Turing.MultiTapeMachine.finiteStep`: one native instruction on finite storage.
* `Turing.MultiTapeMachine.finiteRunFrom`: a bounded loop followed by output projection.

## Main results

* `Turing.MultiTapeMachine.finiteRunFrom_eq`: exact agreement with the native output program.
* `Turing.MultiTapeMachine.finiteRunFrom_init`: agreement from blank initial storage.

## References

Generalizes Computability/Machines/Turing/MultiTape/Probabilistic/Finite.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common choice mechanism.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query} [DecidableEq Oracle]

/-- One native transition on finite storage, using the original choice and external handlers.
A halted configuration remains unchanged without either effect. -/
def finiteStep (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Action k Symbol State Oracle) →
      OracleComp spec (Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (cfg : FiniteConfig k Symbol State Oracle) :
    OracleComp spec (FiniteConfig k Symbol State Oracle) :=
  match cfg.tapes.state with
  | none => pure cfg
  | some state => do
    let action ← choose (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
      cfg.answerSymbols)
    match action with
    | .step action symbol move => pure (cfg.step action symbol move)
    | .query oracle next => do
      let answer ← query oracle (cfg.channels oracle).1
      pure (cfg.receive oracle next answer)

/-- Execute a bounded functional loop and observe its accumulated output. -/
def finiteRunFrom (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Action k Symbol State Oracle) →
      OracleComp spec (Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (fuel : ℕ) (cfg : FiniteConfig k Symbol State Oracle) : OracleComp spec (List Symbol) :=
  (fun final => final.tapes.output) <$>
    OracleComp.iterate fuel (machine.finiteStep choose query) cfg

/-- The finite and native interpreters return the very same typed program. In particular,
they preserve private state for every later interpretation of choices and oracle calls. -/
theorem finiteRunFrom_eq (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Action k Symbol State Oracle) →
      OracleComp spec (Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (finite : FiniteConfig k Symbol State Oracle)
    (cfg : Config k Symbol State Oracle finite.tapes.input) (h : finite.Represents cfg) :
    machine.finiteRunFrom choose query fuel finite = machine.runFrom choose query fuel cfg := by
  induction fuel generalizing finite with
  | zero => simp [finiteRunFrom, h.tapes.output]
  | succ fuel ih =>
    rw [finiteRunFrom, OracleComp.iterate_succ_bind, map_bind]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [finiteStep, h.tapes.state, hs, pure_bind]
      change machine.finiteRunFrom choose query fuel finite = _
      rw [ih finite cfg h]
      simp [runFrom, hs]
    | some state =>
      simp only [finiteStep, h.tapes.state, h.tapes.inputSymbol,
        h.tapes.workTapeSymbols, h.answerSymbols, bind_assoc, runFrom, runConfigFrom, hs, map_bind]
      congr 1
      funext action
      cases action with
      | step action symbol move =>
        simp only [pure_bind]
        exact ih _ _ (h.step action symbol move)
      | query oracle next =>
        simp only [h.queries, bind_assoc, pure_bind, map_bind]
        congr 1
        funext answer
        exact ih _ _ (h.receive oracle next answer)

/-- Finite blank storage realizes the standard native run, with identical choice and query
programs and no assumptions on their distributions. -/
theorem finiteRunFrom_init (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Action k Symbol State Oracle) →
      OracleComp spec (Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (input : List Symbol) :
    machine.finiteRunFrom choose query fuel (FiniteConfig.init machine.initial input) =
      machine.run choose query fuel input :=
  finiteRunFrom_eq machine choose query fuel _ _ (FiniteConfig.represents_init _ _)

end Turing.MultiTapeMachine
