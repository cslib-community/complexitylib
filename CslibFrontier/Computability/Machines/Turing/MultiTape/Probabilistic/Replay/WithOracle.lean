/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.AuxiliaryTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Simulation

/-!
# Saved-coin replay with external oracle channels

The controller reads a saved coin into its finite control before executing the source instruction.
This separates consuming the coin from a possible oracle call: a query cannot consume a second coin
or reset the external handler's state. Communication channels retain their original meaning.

The controller uses a last work tape for the supplied bits. Preparing that tape and the ordinary
input is a separate obligation in a full-input complexity certificate.

## Main definitions

* `Turing.MultiTapePTM.replayWithOracle`: a two-phase saved-coin controller with oracle channels.

## Main results

* `Turing.MultiTapePTM.ReplayWithOracle.run_coins`: exact replay in two steps per supplied bit.
* `Turing.MultiTapePTM.ReplayWithOracle.run_interpret_coin_independent`: discard the controller's
  own stateless private randomness without changing external state.

## References

An original oracle-preserving controller for the existing `MultiTapePTM.runConfigFromCoins`.
It reuses the clock's auxiliary-tape operations and the common machine simulation rule.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeMachine.AuxiliaryTape

variable {k : ℕ} {State Oracle : Type} {input : List Bool}

namespace ReplayWithOracle

/-- An optional saved coin and the source state. `none` means the next phase reads the coin tape. -/
abbrev Control (State : Type) := Option Bool × Option State

/-- Change replay control and move only the saved-coin head, leaving all channels untouched. -/
@[expose] def advance (next : Option (Control State)) (move : SignType) :
    MultiTapeMachine.Action (k + 1) Bool (Control State) Oracle :=
  .step (AuxiliaryTape.move next move) (fun _ => none) (fun _ => 0)

/-- Extend a source instruction to the saved-coin tape and return to the read phase.
The instruction's query buffers and answer-head moves are retained verbatim. -/
@[expose] def execute : MultiTapeMachine.Action k Bool State Oracle →
    MultiTapeMachine.Action (k + 1) Bool (Control State) Oracle
  | .step action symbol move => .step (liftAction none action) symbol move
  | .query oracle next => .query oracle (none, some next)

end ReplayWithOracle

/-- Replay each supplied bit in two phases: read and advance the coin tape, then execute one
source instruction. The controller ignores its own private random bits. -/
@[expose] def replayWithOracle (machine : MultiTapePTM k Bool State Oracle) :
    MultiTapePTM (k + 1) Bool (ReplayWithOracle.Control State) Oracle where
  initial := (none, some machine.initial)
  tr state symbol work answer _ := match state with
    | (none, source) => match work (Fin.last k) with
      | none => ReplayWithOracle.advance none 0
      | some bit => ReplayWithOracle.advance (some (some bit, source)) 1
    | (some _, none) => ReplayWithOracle.advance (some (none, none)) 0
    | (some bit, some source) => ReplayWithOracle.execute
        (machine.tr source symbol (fun i => work i.castSucc) answer bit)

namespace ReplayWithOracle

/-- Two controller instructions consume one saved bit and perform exactly its source instruction,
including any adaptive oracle query and reply. This is equality of programs, not just marginals. -/
theorem run_two [DecidableEq Oracle] {Query : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool State Oracle)
    (query : Oracle → List Bool → OracleComp spec (List Bool))
    (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (bit : Bool) (hcell : tape position = some bit) :
    machine.replayWithOracle.runConfigFrom (pure false) query 2 (config cfg tape position none) =
      (fun final => config final tape (position + 1) none) <$>
        machine.runConfigFrom (pure bit) query 1 cfg := by
  simp only [runConfigFrom, MultiTapeMachine.runConfigFrom, config_state,
    config_inputSymbol, config_workTapeSymbols_last, config_workTapeSymbols_castSucc,
    config_answerSymbols, replayWithOracle, hcell, advance, map_pure, pure_bind, step_move]
  cases hs : cfg.tapes.state with
  | none =>
    simp only [map_pure]
    congr 1
    simpa [hs] using
      step_move cfg tape (position + 1) (some bit) none 0
  | some state =>
    dsimp only
    cases ht : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols bit with
    | step action symbol move => simp [execute, step_liftAction]
    | query oracle next =>
      simp only [execute, bind_pure_comp, Functor.map_map]
      congr 1

/-- A blank saved-coin cell halts replay in one instruction, without calling an oracle. -/
theorem run_stop [DecidableEq Oracle] {Query : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool State Oracle)
    (query : Oracle → List Bool → OracleComp spec (List Bool))
    (cfg : Config k Bool State Oracle input) (tape : ℤ → Option Bool)
    (position : ℤ) (hcell : tape position = none) :
    machine.replayWithOracle.runConfigFrom (pure false) query 1 (config cfg tape position none) =
      pure (stopped cfg tape position) := by
  simp only [runConfigFrom, MultiTapeMachine.runConfigFrom, config_state,
    config_inputSymbol, config_workTapeSymbols_last,
    config_answerSymbols, replayWithOracle, hcell, advance, map_pure, pure_bind]
  rw [step_stop]

/-- Replay a stored sequence in `2 * coins.length + 1` transitions, including the final stop.
The equality retains source tapes, heads, output, channels and oracle effects. The final
controller is halted, so the source finite control is discarded. -/
theorem run_coins [DecidableEq Oracle] {Query : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool State Oracle)
    (query : Oracle → List Bool → OracleComp spec (List Bool))
    (cfg : Config k Bool State Oracle input) (coins : List Bool)
    (tape : ℤ → Option Bool) (position : ℤ)
    (hcoins : ∀ i : ℕ, i < coins.length → tape (position + i) = coins[i]?)
    (hstop : tape (position + coins.length) = none) :
    machine.replayWithOracle.runConfigFrom (pure false) query (2 * coins.length + 1)
        (config cfg tape position none) =
      (fun final => stopped final tape (position + coins.length)) <$>
        machine.runConfigFromCoins query coins cfg := by
  induction coins generalizing cfg position with
  | nil =>
    simpa using run_stop machine query cfg tape position (by simpa using hstop)
  | cons bit coins ih =>
    have hcell : tape position = some bit := by simpa using hcoins 0 (by simp)
    have htail (i : ℕ) (hi : i < coins.length) :
        tape (position + 1 + i) = coins[i]? := by
      have h := hcoins (i + 1) (by simp only [List.length_cons]; omega)
      simpa [Int.natCast_add, add_assoc, add_comm, add_left_comm] using h
    have hend : tape (position + 1 + coins.length) = none := by
      simpa [add_assoc, add_comm, add_left_comm] using hstop
    rw [List.length_cons, show 2 * (coins.length + 1) + 1 = 2 + (2 * coins.length + 1) by omega]
    rw [runConfigFrom, MultiTapeMachine.runConfigFrom_add]
    change (machine.replayWithOracle.runConfigFrom (pure false) query 2
      (config cfg tape position none) >>= _) = _
    rw [run_two machine query cfg tape position bit hcell]
    simp only [bind_map_left]
    change (machine.runConfigFrom (pure bit) query 1 cfg >>= fun final =>
      machine.replayWithOracle.runConfigFrom (pure false) query (2 * coins.length + 1)
        (config final tape (position + 1) none)) = _
    simp_rw [ih _ _ htail hend]
    simp [runConfigFromCoins_cons, map_bind, add_left_comm, add_comm]

/-- Padding after the saved-coin tape ends cannot change the data or cause another oracle call. -/
theorem run_coins_add [DecidableEq Oracle] {Query : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool State Oracle)
    (query : Oracle → List Bool → OracleComp spec (List Bool))
    (cfg : Config k Bool State Oracle input) (coins : List Bool)
    (tape : ℤ → Option Bool) (position : ℤ) (padding : ℕ)
    (hcoins : ∀ i : ℕ, i < coins.length → tape (position + i) = coins[i]?)
    (hstop : tape (position + coins.length) = none) :
    machine.replayWithOracle.runConfigFrom (pure false) query (2 * coins.length + 1 + padding)
        (config cfg tape position none) =
      (fun final => stopped final tape (position + coins.length)) <$>
        machine.runConfigFromCoins query coins cfg := by
  rw [runConfigFrom, MultiTapeMachine.runConfigFrom_add]
  change (machine.replayWithOracle.runConfigFrom (pure false) query (2 * coins.length + 1)
    (config cfg tape position none) >>= _) = _
  rw [run_coins machine query cfg coins tape position hcoins hstop]
  simp only [bind_map_left,
    MultiTapeMachine.runConfigFrom_halted _ _ _ _ _ (stopped_state ..), bind_pure_comp]

/-- The controller's fresh private samples are ignored, so any stateless coin law agrees with
constant private coins, retaining the full external state. The saved source coins are unchanged. -/
theorem run_interpret_coin_independent [DecidableEq Oracle]
    {Query Store : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Bool → OracleComp spec (List Bool))
    (oracle : (q : Query) → StateT Store PMF (spec q)) (coinLaw : PMF Bool)
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s)))
    (fuel : ℕ) (cfg : Config (k + 1) Bool (Control State) Oracle input) (s : Store) :
    (OracleComp.interpret oracle
      (machine.replayWithOracle.runConfigFrom coin query fuel cfg)).run s =
    (OracleComp.interpret oracle
      (machine.replayWithOracle.runConfigFrom (pure false) query fuel cfg)).run s := by
  have h := MultiTapeMachine.run_interpret_runConfigFrom_mul
    machine.replayWithOracle machine.replayWithOracle
    (fun choices => choices <$> (pure false : OracleComp spec Bool))
    (fun choices => choices <$> coin) query query id 1 oracle
    (fun cfg s => by
      cases hs : cfg.tapes.state with
      | none => simp [MultiTapeMachine.runConfigFrom, hs]
      | some state =>
        simp only [MultiTapeMachine.runConfigFrom, hs, replayWithOracle, bind_map_left,
          OracleComp.interpret_bind, StateT.run_bind, hcoin,
          PMF.bind_map, PMF.bind_const, Function.comp_def, map_pure, pure_bind,
          Probability.PMF.monad_bind_eq_bind, id_eq]
        exact (PMF.map_id _).symm) fuel cfg s
  have hmap := PMF.map_id ((OracleComp.interpret oracle
    (machine.replayWithOracle.runConfigFrom (pure false) query fuel cfg)).run s)
  simpa only [one_mul, runConfigFrom, id_eq] using h.trans hmap

end ReplayWithOracle

end Turing.MultiTapePTM
