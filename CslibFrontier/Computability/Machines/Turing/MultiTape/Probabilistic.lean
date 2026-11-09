/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Program

/-!
# Fair-coin multi-tape machines

`MultiTapePTM` specializes the common table to one action per Boolean coin value. Its run is
the common interpreter with a handler that samples a bit and selects the corresponding action.
Even equal branches consume a bit; halted configurations consume no more bits.

The open run accepts a typed program supplying coins and a program answering each named oracle
call. This separates the syntax from the interpretation: fair-coin semantics requires interpreting
the coin program as an independent uniform bit. `runClosed` fixes this interpretation through
`ProbComp.uniform Bool` for machines without oracle channels. No efficiency assertion about an
arbitrary coin program or oracle handler is made here.

Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.

## Main definitions

* `Turing.MultiTapePTM`: the Boolean-indexed specialization of the common machine.
* `Turing.MultiTapePTM.runConfigFrom`: the run program with explicit coin and query programs.
* `Turing.MultiTapePTM.runClosed`: a closed fair-coin run using the finite-uniform interface.
-/

@[expose] public section

namespace Turing

open Cslib

/-- A machine with one transition per Boolean coin; by default it has no oracle channels. -/
abbrev MultiTapePTM (k : ℕ) (Symbol State : Type) (Oracle : Type := Empty) :=
  MultiTapeMachine k Symbol State Oracle (ReaderT Bool Id)

namespace MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {spec : OracleSpec.{0, 0} Query}
  {input : List Symbol} [DecidableEq Oracle]

/-- Run with the supplied coin program, retaining the whole configuration at clock exhaustion. -/
def runConfigFrom (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    OracleComp spec (Config k Symbol State Oracle input) :=
  MultiTapeMachine.runConfigFrom machine (fun choices => choices <$> coin) query fuel cfg

/-- Observe the output word of an open run. -/
def runFrom (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) : OracleComp spec (List Symbol) :=
  (fun final => final.tapes.output) <$> machine.runConfigFrom coin query fuel cfg

/-- Run from the initial configuration with explicit coin and oracle programs. -/
def run (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (input : List Symbol) : OracleComp spec (List Symbol) :=
  machine.runFrom coin query fuel (machine.initialConfig input)

/-- A zero clock observes the current output without drawing a coin or making a query. -/
@[simp] theorem runFrom_zero (machine : MultiTapePTM k Symbol State Oracle)
    (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (cfg : Config k Symbol State Oracle input) :
    machine.runFrom coin query 0 cfg = pure cfg.tapes.output := by
  simp [runFrom, runConfigFrom]

/-- A live instruction draws one coin, then performs one ordinary step or one external request.
This equation is left out of the simp set to avoid expanding a symbolic clock. -/
theorem runFrom_succ (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    machine.runFrom coin query (fuel + 1) cfg =
      (match cfg.tapes.state with
      | none => pure cfg.tapes.output
      | some state => do
        let bit ← coin
        match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols bit with
        | .step action symbol move => machine.runFrom coin query fuel (cfg.step action symbol move)
        | .query op next => do
          let answer ← query op (cfg.channels op).queryBuffer
          machine.runFrom coin query fuel (cfg.receive op next answer)) := by
  cases hs : cfg.tapes.state with
  | none => simp [runFrom, runConfigFrom, MultiTapeMachine.runConfigFrom, hs]
  | some state =>
    simp only [runFrom, runConfigFrom, MultiTapeMachine.runConfigFrom, hs, bind_map_left, map_bind]
    congr 1
    funext bit
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit <;>
      simp only [map_bind]

/-- The closed fair-coin run, with fresh uniform Boolean choices at each live transition. -/
noncomputable def runClosed (machine : MultiTapePTM k Symbol State) (fuel : ℕ)
    (input : List Symbol) : ProbComp (List Symbol) :=
  machine.run (ProbComp.uniform Bool) (fun oracle => oracle.elim) fuel input

/-- Every supported closed output has length at most the machine's clock. -/
theorem length_output_eval_runClosed_le (machine : MultiTapePTM k Symbol State) (fuel : ℕ)
    (input output : List Symbol)
    (h : output ∈ (ProbComp.eval (machine.runClosed fuel input)).support) :
    output.length ≤ fuel := by
  have hstate : (output, ()) ∈
      ((OracleComp.interpret (m := StateT Unit PMF)
        (fun q (s : Unit) => (fun a => (a, s)) <$> ProbComp.unifOracle q)
        (machine.runClosed fuel input)).run ()).support := by
    rw [OracleComp.run_interpret_stateless, PMF.monad_map_eq_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨output, h, rfl⟩
  have hbound := MultiTapeMachine.length_output_runFrom_le machine
    (fun choices => choices <$> ProbComp.uniform Bool) Empty.elim _ fuel
    (machine.initialConfig input) () () output hstate
  simpa only [MultiTapeMachine.initialConfig, Cfg.init, List.length_nil, Nat.zero_add] using hbound

/-- Forget probabilities, retaining exactly the actions selected by some coin value. -/
def toNondeterministic (machine : MultiTapePTM k Symbol State Oracle) :
    MultiTapeMachine k Symbol State Oracle Set where
  initial := machine.initial
  tr state symbol work answer := Set.range (machine.tr state symbol work answer)

end MultiTapePTM

end Turing
