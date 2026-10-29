/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Alternating
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The strict table of an alternating machine

An alternating machine running within `t` steps plays a game of `t` moves, each chosen by the
player that the state labels. This file makes the order of the players fixed: an existential and
a universal move per step. The strict table of a machine (`Turing.MultiTapeATM.strict`) spends two
coins on each step of the machine: it stores the first coin, and on the second takes the step of
the machine with the second coin in a universal state and with the first in an existential state.
The coin that is not used is a vacuous move.

Replaying a fixed finite fair-coin table is polynomial-time
(`Turing.MultiTapePTM.computableInPolyTime_runClosedCoins`), so the game verifier on the
strict table (`Turing.MultiTapeATM.gameVerifier`) is computable in polynomial time
(`Turing.MultiTapeATM.computableInPolyTime_gameVerifier`).

## Main definitions

* `Turing.MultiTapeATM.strict`: the strict table, two coins per step.
* `Turing.MultiTapeATM.gameVerifier`: the verifier replaying the strict table on an encoded
  instance and a move list.

## Main results

* `Turing.MultiTapeATM.Strict.stepCoins_cfg`,
  `Turing.MultiTapeATM.Strict.stepCoins_cfg_of_halted`: two coins per step on running
  configurations, and halted configurations stay unchanged.
* `Turing.MultiTapeATM.computableInPolyTime_gameVerifier`: replaying the strict table of a
  finite alternating machine is polynomial-time.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeATM

open MultiTapeMachine

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-! ### The strict table -/

namespace Strict

/-- The action of the strict table: in a state `(q, none)` store the coin; in a state
`(q, some x)` take the step of the machine with the coin `y` if `q` is universal and with `x`
otherwise. -/
def action (atm : MultiTapeATM k Symbol State) :
    State × Option Bool → Option Symbol → (Fin k → Option Symbol) → Bool →
      Turing.Action k Symbol (State × Option Bool)
  | (q, none), _, _, x => ⟨0, fun _ => (none, 0), none, some (q, some x)⟩
  | (q, some x), symbol, work, y =>
    let a := atm.action q symbol work (if atm.universal q then y else x)
    ⟨a.inputTape, a.workTapes, a.output, a.state.map fun q' => (q', none)⟩

/-- A configuration of the machine as one of the strict table, with the stored coin. -/
def cfg (c : Cfg k Symbol State input) (p : Option Bool) :
    Cfg k Symbol (State × Option Bool) input :=
  c.mapState (Option.map fun q => (q, p))

end Strict

/-- **The strict table** of an alternating machine: it spends two coins on each step, storing the
first, and takes the step of the machine with the second coin in a universal state and with the
first in an existential state. -/
def strict (atm : MultiTapeATM k Symbol State) : MultiTapePTM k Symbol (State × Option Bool) where
  initial := (atm.toPTM.initial, none)
  tr s symbol work _ bit := Action.emptyOracleEquiv.symm (Strict.action atm s symbol work bit)

namespace Strict

variable (atm : MultiTapeATM k Symbol State)

/-- A running instruction of the strict table applies `Strict.action`. -/
theorem step_strict {c : Cfg k Symbol (State × Option Bool) input} {s : State × Option Bool}
    (h : c.state = some s) (bit : Bool) :
    (atm.strict.withCoin bit).toTM.step c =
      (Strict.action atm s c.inputSymbol c.workTapeSymbols bit).apply c := by
  rw [MultiTapeTM.step_of_state h, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  rfl

/-- The strict table stores the existential coin. -/
theorem step_cfg_none {c : Cfg k Symbol State input} {q : State} (h : c.state = some q)
    (x : Bool) : (atm.strict.withCoin x).toTM.step (cfg c none) = cfg c (some x) := by
  rw [step_strict atm (s := (q, none)) (by simp [cfg, h])]
  simp only [Strict.action, Action.apply, cfg, Cfg.mapState, h, Option.map_some,
    moveInputPos_zero, SignType.coe_zero, add_zero, Option.toList_none, List.append_nil]

/-- With a stored coin, the strict table takes the step of the machine with the coin of the
player of its state. -/
theorem step_cfg_some {c : Cfg k Symbol State input} {q : State} (h : c.state = some q)
    (x y : Bool) : (atm.strict.withCoin y).toTM.step (cfg c (some x)) =
      cfg (atm.next (if atm.universal q then y else x) c) none := by
  rw [step_strict atm (s := (q, some x)) (by simp [cfg, h]), atm.next_of_state h]
  rfl

/-- One step of the machine costs two coins of the strict table. -/
theorem stepCoins_cfg {c : Cfg k Symbol State input} {q : State} (h : c.state = some q)
    (x y : Bool) (coins : List Bool) :
    atm.strict.stepCoins (x :: y :: coins) (cfg c none) =
      atm.strict.stepCoins coins (cfg (atm.next (if atm.universal q then y else x) c) none) := by
  rw [MultiTapePTM.stepCoins_cons, step_cfg_none atm h, MultiTapePTM.stepCoins_cons,
    step_cfg_some atm h]

/-- A halted configuration of the machine is a halted configuration of the strict table. -/
theorem stepCoins_cfg_of_halted {c : Cfg k Symbol State input} (h : c.state = none)
    (coins : List Bool) : atm.strict.stepCoins coins (cfg c none) = cfg c none := by
  induction coins with
  | nil => rfl
  | cons b coins ih =>
    rw [MultiTapePTM.stepCoins_cons, MultiTapeTM.step_of_halt (by simp [cfg, h]), ih]

/-- The strict table starts with the initial configuration of the machine. -/
theorem initialConfig_strict (input : List Symbol) :
    (atm.strict.initialConfig input).tapes = cfg (atm.toPTM.toNTM.initCfg input) none :=
  rfl

end Strict

/-! ### Replaying the strict table -/

open MultiTapeTM

variable {State : Type} [Finite State] {α : Type} {enc : α ↪ List Bool}

/-- The verifier of a game on the strict table: it accepts when the strict table, replayed from
the moves on the encoded instance, emits `[true]`. -/
def gameVerifier (atm : MultiTapeATM k Bool State) (enc : α ↪ List Bool)
    (x : α × List Bool) : Bool :=
  decide (atm.strict.runClosedCoins x.2 (enc x.1) = [true])

/-- The verifier of a game on the strict table is polynomial-time: it replays a fixed finite
fair-coin table. -/
@[fun_prop]
theorem computableInPolyTime_gameVerifier (atm : MultiTapeATM k Bool State) :
    ComputableInPolyTime (atm.gameVerifier enc) (encPair enc encBits) encBool := by
  have hswap : ComputableInPolyTime (fun x : α × List Bool => (x.2, enc x.1))
      (encPair enc encBits) (encPair encBits encBits) :=
    (ComputableInPolyTime.snd enc encBits).prod
      ((ComputableInPolyTime.of_eq (encOut := encBits) fun _ => rfl).comp
        (ComputableInPolyTime.fst enc encBits))
  exact ComputableInPolyTime.decide_eq'
    ((MultiTapePTM.computableInPolyTime_runClosedCoins atm.strict).comp hswap)
    (ComputableInPolyTime.const [true])

end Turing.MultiTapeATM
