/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Simulation
public import Complexity.Languages.Probabilistic.Oracle

/-!
# Fair-coin machines with external oracle calls

`runOracle` fixes the coin program of the common machine interpreter and exposes its word-based
external channels. The two effects use disjoint query types: external handlers cannot choose
the machine's private coins. Every live instruction draws one fresh fair bit; query writing and
reply reading still use ordinary machine instructions.

## Main definitions

* `Turing.MultiTapePTM.runOracle`: the clocked run as a `ProbOracleComp` program.
* `Turing.MultiTapePTM.ofClosed`: a closed machine with unused external channels.

## Main results

* `Turing.MultiTapePTM.length_output_runOracle_le`: the clock bounds supported output lengths.
* `Turing.MultiTapePTM.run_interpret_runOracle_ofDeterministic`: deterministic embedding preserves
  the output and external oracle state.
* `Turing.MultiTapePTM.runOracle_ofClosed`: a closed machine's oracle run is its sampled closed run.
* `Turing.MultiTapePTM.runOracle_eq_sample_runClosed`: without external channels, the oracle run is
  the sampled closed run.

## References

Adapts the oracle run from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common machine and typed sum interface.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine

variable {k : ℕ} {Symbol State Operation OracleState : Type} [DecidableEq Operation]

/-- Use private fair coins and submit each channel's accumulated word to the external oracle. -/
noncomputable def runOracle (machine : MultiTapePTM k Symbol State Operation)
    (fuel : ℕ) (input : List Symbol) :
    ProbOracleComp (fun _ : Operation × List Symbol => List Symbol) (List Symbol) :=
  machine.run (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query (op, word)) fuel input

/-- Arbitrarily long oracle replies cannot bypass the cost of writing the output. -/
theorem length_output_runOracle_le (machine : MultiTapePTM k Symbol State Operation)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (input output : List Symbol) (s s' : OracleState)
    (h : (output, s') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        (machine.runOracle fuel input)).run s).support) : output.length ≤ fuel := by
  have hbound := MultiTapeMachine.length_output_runFrom_le machine
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query
      (spec := fun _ : Operation × List Symbol => List Symbol) (op, word))
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) fuel
    (machine.initialConfig input) s s' output h
  simpa only [initialConfig, Cfg.init, List.length_nil, Nat.zero_add] using hbound

/-- A deterministic run ignores the external oracle and preserves its full private state. -/
theorem run_interpret_runOracle_ofDeterministic (machine : MultiTapeTM k Symbol State)
    (oracle : Operation × List Symbol → StateT OracleState PMF (List Symbol))
    (fuel : ℕ) (input : List Symbol) (s : OracleState) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((ofDeterministic machine).runOracle fuel input)).run s =
      PMF.pure ((machine.runFrom (machine.initCfg input) fuel).output, s) := by
  apply run_interpret_ofDeterministic machine (ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun op word => ProbOracleComp.query
      (spec := fun _ : Operation × List Symbol => List Symbol) (op, word))
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
    (PMF.uniformOfFintype Bool)
  intro state
  simp only [ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform]

/-- A closed fair-coin machine with external channels that it never reads or writes. -/
def ofClosed (machine : MultiTapePTM k Symbol State) : MultiTapePTM k Symbol State Operation where
  initial := machine.initial
  tr state symbol work _ bit := match machine.tr state symbol work Empty.elim bit with
    | .step action _ _ => .step action (fun _ => none) (fun _ => 0)
    | .query oracle _ => oracle.elim

/-- Running a closed machine with external channels samples its closed run: the program makes no
external call, so it preserves every external oracle state. -/
theorem runOracle_ofClosed (machine : MultiTapePTM k Symbol State) (fuel : ℕ)
    (input : List Symbol) :
    (ofClosed (Operation := Operation) machine).runOracle fuel input =
      ProbOracleComp.sample (machine.runClosed fuel input) := by
  let embed (cfg : Config k Symbol State Empty input) : Config k Symbol State Operation input :=
    { tapes := cfg.tapes }
  have hsim := MultiTapeMachine.runConfigFrom_map machine
    (ofClosed (Operation := Operation) machine)
    (fun choices => choices <$> ProbOracleComp.sample
      (spec := fun _ : Operation × List Symbol => List Symbol) (ProbComp.uniform Bool))
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun oracle _ => oracle.elim) (fun op word => ProbOracleComp.query (op, word)) embed
    (fun cfg => by
      cases hs : cfg.tapes.state with
      | none => simp [MultiTapeMachine.runConfigFrom, embed, hs]
      | some state =>
        have hanswer : cfg.answerSymbols = Empty.elim := funext fun oracle => oracle.elim
        dsimp only [embed]
        simp only [MultiTapeMachine.runConfigFrom, hs, hanswer, bind_map_left, map_bind]
        congr 1
        funext bit
        cases htr : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols Empty.elim
            bit with
        | step action symbol move =>
          simp only [ofClosed, htr, map_pure]
          rfl
        | query oracle next => exact oracle.elim)
  calc (ofClosed (Operation := Operation) machine).runOracle fuel input
      = (fun final => final.tapes.output) <$> MultiTapeMachine.runConfigFrom
          (ofClosed (Operation := Operation) machine)
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) fuel
          (embed (machine.initialConfig input)) := rfl
    _ = (fun final => final.tapes.output) <$> MultiTapeMachine.runConfigFrom machine
          (fun choices => choices <$> ProbOracleComp.sample
            (spec := fun _ : Operation × List Symbol => List Symbol) (ProbComp.uniform Bool))
          (fun oracle _ => oracle.elim) fuel (machine.initialConfig input) := by
      rw [hsim, Functor.map_map]
    _ = ProbOracleComp.sample (machine.runClosed fuel input) := by
      simp only [runClosed, run, runFrom, runConfigFrom, ProbOracleComp.sample,
        OracleComp.interpret_map, MultiTapeMachine.interpret_runConfigFrom]
      congr 2
      funext oracle
      exact oracle.elim

/-- A machine without external channels never calls the external oracle: its oracle run is its
sampled closed run. -/
theorem runOracle_eq_sample_runClosed (machine : MultiTapePTM k Symbol State) (fuel : ℕ)
    (input : List Symbol) :
    machine.runOracle fuel input = ProbOracleComp.sample (machine.runClosed fuel input) := by
  simp only [runOracle, runClosed, run, runFrom, runConfigFrom, ProbOracleComp.sample,
    OracleComp.interpret_map, MultiTapeMachine.interpret_runConfigFrom]
  congr 2
  funext oracle
  exact oracle.elim

/-- A closed machine's oracle run preserves every external oracle state and has the closed
output distribution. -/
theorem run_interpret_runOracle_ofClosed (machine : MultiTapePTM k Bool State)
    (oracle : Operation × List Bool → StateT OracleState PMF (List Bool))
    (fuel : ℕ) (input : List Bool) (s : OracleState) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        ((ofClosed machine).runOracle fuel input)).run s =
      (ProbComp.eval (machine.runClosed fuel input)).map (·, s) := by
  rw [runOracle_ofClosed, ProbOracleComp.run_interpret_sample]

end Turing.MultiTapePTM
