/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Multi-tape machines with optional oracle channels

A `MultiTapeMachine` separates the tape interface from the choice of a transition. Ordinary steps
use `Turing.Action` on a `Turing.Cfg`; in addition, `Oracle` indexes communication operations.
Each operation has a write-only query buffer and a read-only answer tape, and `Empty` gives a
machine without communication.

The operation type names interfaces such as hashing, signing and decryption; it does not contain
their request payloads. Payloads are words written to the selected query buffer, so a finite
operation type still permits arbitrarily long requests. At the game level, `OracleComp` can use
typed payloads and operation-dependent replies; a machine realization must encode these as words.

Different operations may share one hidden interpreter state. Separate communication channels do
not assert independent oracles. In particular, a random-oracle handler must retain its sampled
answers across every user of that oracle, including calls made inside another game operation.

`Choose` describes the result of a transition. A fair-coin table uses `fun α => Bool → α`, which
keeps the action for each coin value, including when the two actions agree.

Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
The effect-free deterministic and nondeterministic interfaces are related step-exactly to
upstream machines in `MultiTape.Machine.Equivalence`.

## Main definitions

* `Turing.MultiTapeMachine`: a transition table parameterized by its choice mechanism.
* `Turing.MultiTapeMachine.Config`: upstream tapes and control, plus oracle communication channels.
* `Turing.MultiTapeMachine.Action.mapState`, `Turing.MultiTapeMachine.Config.mapState`: relabel
  control states, preserving halting, tape data and communication channels.

No finiteness or complexity assumptions are imposed here. A complexity predicate must require
fixed finite control, a finite alphabet and finitely many oracle channels. With these assumptions
an ordinary step inspects and updates a fixed number of tape cells. Query submission is a separate
step; writing the query and reading its reply require ordinary steps.
-/

@[expose] public section

namespace Turing

universe u v w x

namespace MultiTapeMachine

variable {k : ℕ} {Symbol : Type u} {State : Type v} {State' : Type x} {Oracle : Type w}
  {input : List Symbol}

/-- The local tape action and communication updates, or a call to a named oracle. -/
inductive Action (k : ℕ) (Symbol : Type u) (State : Type v) (Oracle : Type w) where
  /-- Update ordinary tapes, write at most one symbol per query buffer, and move answer heads. -/
  | step (action : Turing.Action k Symbol State)
      (querySymbol : Oracle → Option Symbol) (answerMove : Oracle → SignType)
  /-- Submit one buffer, install its reply, and resume in the specified state. -/
  | query (oracle : Oracle) (next : State)

/-- Rename the successor state of an instruction. -/
def Action.mapState (e : State → State') :
    Action k Symbol State Oracle → Action k Symbol State' Oracle
  | .step action symbol move => .step { action with state := action.state.map e } symbol move
  | .query oracle next => .query oracle (e next)

/-- The communication state for one oracle. It is separate from the oracle's private state. -/
@[ext] structure Channel (Symbol : Type u) where
  /-- Symbols written since the last query. -/
  queryBuffer : List Symbol := []
  /-- The last reply, read only through the answer head. -/
  answer : List Symbol := []
  /-- The first answer symbol has position zero. -/
  answerPos : ℤ := 0

/-- Ordinary machine tapes together with the communication state of each oracle channel. -/
@[ext] structure Config (k : ℕ) (Symbol : Type u) (State : Type v) (Oracle : Type w)
    (input : List Symbol) where
  /-- The shared configuration of ordinary tapes and control. -/
  tapes : Cfg k Symbol State input
  /-- Each oracle has its own query buffer and answer head. -/
  channels : Oracle → Channel Symbol := fun _ => {}

/-- Rename the control state of a configuration, keeping its tapes and channels. -/
def Config.mapState (e : State → State') (cfg : Config k Symbol State Oracle input) :
    Config k Symbol State' Oracle input where
  tapes := cfg.tapes.mapState (Option.map e)
  channels := cfg.channels

@[simp] theorem Config.mapState_tapes_state (e : State → State')
    (cfg : Config k Symbol State Oracle input) :
    (cfg.mapState e).tapes.state = cfg.tapes.state.map e := rfl

@[simp] theorem Config.mapState_tapes_output (e : State → State')
    (cfg : Config k Symbol State Oracle input) :
    (cfg.mapState e).tapes.output = cfg.tapes.output := rfl

/-- Read the cell under a channel's answer head; positions outside the reply are blank. -/
def Channel.answerSymbol (channel : Channel Symbol) : Option Symbol :=
  if 0 ≤ channel.answerPos then channel.answer[channel.answerPos.toNat]? else none

/-- Read one answer cell per channel. -/
def Config.answerSymbols (cfg : Config k Symbol State Oracle input) : Oracle → Option Symbol :=
  fun oracle => (cfg.channels oracle).answerSymbol

/-- Apply one ordinary tape action and the channel-local writes and head moves. -/
def Config.step (cfg : Config k Symbol State Oracle input)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) : Config k Symbol State Oracle input where
  tapes := action.apply cfg.tapes
  channels oracle := {
    queryBuffer := (cfg.channels oracle).queryBuffer ++ (symbol oracle).toList
    answer := (cfg.channels oracle).answer
    answerPos := (cfg.channels oracle).answerPos + move oracle }

/-- Install a reply on the selected channel, clear its query buffer, and reset its answer head.
All other communication channels and all ordinary tapes are preserved. -/
def Config.receive [DecidableEq Oracle] (cfg : Config k Symbol State Oracle input)
    (oracle : Oracle) (next : State) (answer : List Symbol) :
    Config k Symbol State Oracle input where
  tapes := { cfg.tapes with state := some next }
  channels := Function.update cfg.channels oracle ⟨[], answer, 0⟩

theorem Config.mapState_step (e : State → State') (cfg : Config k Symbol State Oracle input)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    (cfg.mapState e).step { action with state := action.state.map e } symbol move =
      (cfg.step action symbol move).mapState e := rfl

theorem Config.mapState_receive [DecidableEq Oracle] (e : State → State')
    (cfg : Config k Symbol State Oracle input) (oracle : Oracle) (next : State)
    (answer : List Symbol) :
    (cfg.mapState e).receive oracle (e next) answer = (cfg.receive oracle next answer).mapState e :=
  rfl

end MultiTapeMachine

/-- A multi-tape transition table with an explicit choice mechanism and optional oracle channels. -/
@[ext] structure MultiTapeMachine (k : ℕ) (Symbol : Type u) (State : Type v) (Oracle : Type w)
    (Choose : Type (max u v w) → Type x) where
  /-- Initial control state. -/
  initial : State
  /-- Inspect only the current state and the symbols under the input, work and answer heads. -/
  tr : State → Option Symbol → (Fin k → Option Symbol) →
    (Oracle → Option Symbol) → Choose (MultiTapeMachine.Action k Symbol State Oracle)

namespace MultiTapeMachine

variable {k : ℕ} {Symbol : Type u} {State : Type v} {Oracle : Type w}
  {Choose : Type (max u v w) → Type x}

/-- Start with the ordinary initial configuration and empty communication channels. -/
def initialConfig (machine : MultiTapeMachine k Symbol State Oracle Choose)
    (input : List Symbol) : Config k Symbol State Oracle input where
  tapes := Cfg.init machine.initial input

end MultiTapeMachine

end Turing
