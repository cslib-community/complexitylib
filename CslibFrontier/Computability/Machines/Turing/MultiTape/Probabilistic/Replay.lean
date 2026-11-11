/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# A deterministic controller for saved-coin replay

The controller reads the supplied coins from a fresh last work tape. Each stored bit supplies
one source instruction. After the source halts, only the coin head continues moving; the first
blank coin cell halts the controller. Thus a tape of `t` coins takes exactly `t + 1` transitions,
even if the source does not halt within its supplied clock.

This module accounts for execution from preloaded tapes. Writing the coins and preparing the
input are separate machine computations, not free initial data in a complexity certificate.

## Main definitions

* `Turing.MultiTapePTM.replay`: deterministic replay with one additional read-only work tape.

## Main results

* `Turing.MultiTapePTM.runFrom_replay`: agreement with fixed-coin execution and actual halting.

## References

Adapted from the cslib `crypto` branch's Oracle/Replay.lean at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common closed machine directly.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {State : Type} {input : List Bool}

namespace Replay

/-- Add a read-only coin tape, keeping the source's possibly halted state in live control. -/
def config (cfg : Config k Bool State Empty input) (tape : ℤ → Option Bool) (position : ℤ) :
    Cfg (k + 1) Bool (Option State) input where
  state := some cfg.tapes.state
  inputPos := cfg.tapes.inputPos
  workTapes := Fin.lastCases tape cfg.tapes.workTapes
  workTapePos := Fin.lastCases position cfg.tapes.workTapePos
  output := cfg.tapes.output

/-- Move only the coin head and update the controller. -/
def idle (next : Option (Option State)) (move : SignType) :
    Turing.Action (k + 1) Bool (Option State) where
  inputTape := 0
  workTapes := Fin.lastCases (none, move) (fun _ => (none, 0))
  output := none
  state := next

/-- Simulate an ordinary source action while advancing the coin head. -/
def liftAction (action : Turing.Action k Bool State) :
    Turing.Action (k + 1) Bool (Option State) where
  inputTape := action.inputTape
  workTapes := Fin.lastCases (none, 1) action.workTapes
  output := action.output
  state := some action.state

/-- Stop the controller without changing any tape or head. -/
def stopped (cfg : Config k Bool State Empty input) (tape : ℤ → Option Bool) (position : ℤ) :
    Cfg (k + 1) Bool (Option State) input :=
  (config cfg tape position).withState none

/-- A lifted action updates the source tapes and consumes one stored coin. -/
theorem apply_liftAction (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) (action : Turing.Action k Bool State)
    (symbol : Empty → Option Bool) (move : Empty → SignType) :
    (liftAction action).apply (config cfg tape position) =
      config (cfg.step action symbol move) tape (position + 1) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases <;>
    simp [config, liftAction, Config.step, Turing.Action.apply]

/-- Once the source halts, only the saved-coin head moves. -/
theorem apply_tick (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) :
    (idle (some cfg.tapes.state) 1).apply (config cfg tape position) =
      config cfg tape (position + 1) := by
  refine Cfg.ext rfl (by simp [idle, config, Turing.Action.apply]) ?_ ?_
    (by simp [idle, config, Turing.Action.apply]) <;>
    funext i <;> induction i using Fin.lastCases <;> simp [idle, config, Turing.Action.apply]

/-- Halting preserves every tape and head position. -/
theorem apply_stop (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) :
    (idle none 0).apply (config cfg tape position) = stopped cfg tape position := by
  refine Cfg.ext rfl (by simp [idle, config, stopped, Turing.Action.apply, Cfg.withState]) ?_ ?_
    (by simp [idle, config, stopped, Turing.Action.apply, Cfg.withState]) <;>
    funext i <;> induction i using Fin.lastCases <;>
    simp [idle, config, stopped, Turing.Action.apply, Cfg.withState]

@[simp] theorem config_inputSymbol (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) :
    (config cfg tape position).inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem config_workTapeSymbols_castSucc (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) (i : Fin k) :
    (config cfg tape position).workTapeSymbols i.castSucc = cfg.tapes.workTapeSymbols i := by
  simp [config, Cfg.workTapeSymbols]

@[simp] theorem config_workTapeSymbols_last (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) :
    (config cfg tape position).workTapeSymbols (Fin.last k) = tape position := by
  simp [config, Cfg.workTapeSymbols]

end Replay

/-- A deterministic replay controller. Its control is finite whenever the source control is. -/
def replay (machine : MultiTapePTM k Bool State) : MultiTapeTM (k + 1) Bool (Option State) :=
  MultiTapeTM.ofTr (some machine.initial) fun state symbol work =>
    match work (Fin.last k) with
    | none => Replay.idle none 0
    | some bit => match state with
      | none => Replay.idle (some none) 1
      | some state => Replay.liftAction
          (Action.emptyOracleEquiv
            (machine.tr state symbol (fun i => work i.castSucc) Empty.elim bit))

namespace Replay

/-- An available coin supplies exactly one deterministic source transition. -/
theorem step_some (machine : MultiTapePTM k Bool State) (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) (bit : Bool) (hcell : tape position = some bit) :
    machine.replay.step (config cfg tape position) =
      config ((machine.withCoin bit).step cfg) tape (position + 1) := by
  rw [MultiTapeTM.step_of_state (show (config cfg tape position).state = some cfg.tapes.state
    from rfl)]
  have hread : cfg.answerSymbols = Empty.elim := funext fun oracle => oracle.elim
  simp only [replay, MultiTapeTM.tr_ofTr, config_inputSymbol, config_workTapeSymbols_last,
    hcell, config_workTapeSymbols_castSucc, MultiTapeMachine.step, withCoin]
  cases hs : cfg.tapes.state with
  | none => simpa only [hs] using apply_tick cfg tape position
  | some state =>
    simp only [hread]
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols Empty.elim bit with
    | step action symbol move => exact apply_liftAction cfg tape position action symbol move
    | query oracle _ => exact oracle.elim

/-- The first blank saved-coin cell halts the controller. -/
theorem step_none (machine : MultiTapePTM k Bool State) (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) (hcell : tape position = none) :
    machine.replay.step (config cfg tape position) = stopped cfg tape position := by
  rw [MultiTapeTM.step_of_state (show (config cfg tape position).state = some cfg.tapes.state
    from rfl)]
  simpa only [replay, MultiTapeTM.tr_ofTr, config_workTapeSymbols_last, hcell] using
    apply_stop cfg tape position

/-- Replay a stored sequence starting at any coin position. The source may halt early or remain
live when the supplied sequence ends; the controller reaches the following blank in either case. -/
theorem runFrom_coins (machine : MultiTapePTM k Bool State) (cfg : Config k Bool State Empty input)
    (coins : List Bool) (tape : ℤ → Option Bool) (position : ℤ)
    (hcoins : ∀ i : ℕ, i < coins.length → tape (position + i) = coins[i]?)
    (hstop : tape (position + coins.length) = none) :
    machine.replay.runFrom (config cfg tape position) (coins.length + 1) =
      stopped (machine.runClosedConfigFromCoins coins cfg) tape (position + coins.length) := by
  induction coins generalizing cfg position with
  | nil =>
    simpa [MultiTapeTM.runFrom_one, runClosedConfigFromCoins] using
      step_none machine cfg tape position (by simpa using hstop)
  | cons bit coins ih =>
    have hcell : tape position = some bit := by simpa using hcoins 0 (by simp)
    have htail (i : ℕ) (hi : i < coins.length) :
        tape (position + 1 + i) = coins[i]? := by
      have h := hcoins (i + 1) (by simp only [List.length_cons]; lia)
      simpa [Int.natCast_add, add_assoc, add_comm, add_left_comm] using h
    have hend : tape (position + 1 + coins.length) = none := by
      simpa [add_assoc, add_comm, add_left_comm] using hstop
    rw [List.length_cons, show coins.length + 1 + 1 = 1 + (coins.length + 1) by lia,
      MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_one,
      step_some machine cfg tape position bit hcell, ih _ _ htail hend]
    simp [runClosedConfigFromCoins, add_comm, add_left_comm]

end Replay

/-- From preloaded coins and blank source tapes, replay agrees with the fixed-coin interpreter
and halts in the number of coins plus one transitions. -/
theorem runFrom_replay (machine : MultiTapePTM k Bool State) (coins input : List Bool) :
    machine.replay.runFrom
        (Replay.config (machine.initialConfig input) (tapeOfList coins) 0) (coins.length + 1) =
      Replay.stopped (machine.runClosedConfigFromCoins coins (machine.initialConfig input))
        (tapeOfList coins) coins.length := by
  simpa using Replay.runFrom_coins machine (machine.initialConfig input) coins
    (tapeOfList coins) 0 (by intros; simp) (by simp)

end Turing.MultiTapePTM
