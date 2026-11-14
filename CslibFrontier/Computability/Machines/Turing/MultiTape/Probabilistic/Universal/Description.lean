/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive
public import CslibFrontier.Foundations.Data.Fin.Decode

/-!
# Finite descriptions of fair-coin oracle machines

A `Turing.MultiTapePTM.Universal.Desc` is first-order syntax for a fair-coin multi-tape machine
over natural-number symbols and states. It gives the number of work tapes and oracle operations
explicitly. Each transition-table entry stores both Boolean branches, and each oracle query stores
its operation as a natural-number tag. Denotation checks the tag against the declared operation
count and produces an actual `Fin operations` channel; an out-of-range tag halts locally without
calling an oracle. Thus operation dispatch is part of the finite description, not a semantic
callback.

The encoding is a bit string with the following convention. The outer description uses the
right-associated tuple encoding `encPair encUnary (encPair encUnary (encPair encUnary
(encPair encUnary (encList ...))))`, in exact field order: work-tape count, user-state count,
operation count, initial-state tag, transition table. Thus the first four field words are framed in
turn, and the final `encList` word is the unframed tuple tail; that list is itself the concatenation
of one frame per table entry. A table entry is an `encPair` of its key and two stored branches, so
the key is framed and the branch pair is the tail. Keys list the ordinary state/input/work-head
fields before the answer heads, and branches are ordered `false`, then `true`. States, symbols and
operation tags use
`Turing.MultiTapeTM.encUnary`; blanks use `encOption`; lists use `encList`; and the two action
constructors use the leading-bit tags of `encSum`. Ordinary key and tape-action fields reuse the
existing `Turing.MultiTapeTM.Universal.eKey` and `.eAct` encodings. The resulting `descLen` is
therefore a rigorous unary model-code length, not an implementation byte count. It includes the
declared control and operation counts, every control and operation tag, and the complete transition
table.

`Desc.runOracle` is the open denotational semantics. Its equality with the common
`MultiTapePTM.runOracle` interpreter holds as a program, before any external handler is chosen;
`Desc.runWith_toMachine` records the consequent equality for an arbitrary shared stateful handler.
The handler's own computation remains external to the machine clock.

## Main definitions

* `Turing.MultiTapePTM.Universal.Key`, `.Act`, `.Branches`, `.Desc`: first-order syntax.
* `Turing.MultiTapePTM.Universal.eDesc`, `.descLen`: the injective encoding and its bit length.
* `Turing.MultiTapePTM.Universal.Desc.toMachine`: denotation as a `MultiTapePTM` with operation
  type `Fin d.operations`.
* `Turing.MultiTapePTM.Universal.Desc.runOracle`: exact open-oracle semantics.

## Main results

* `Turing.MultiTapePTM.Universal.Desc.runOracle_eq_toMachine`: denotation agrees as an open
  oracle program.
* `Turing.MultiTapePTM.Universal.Desc.runWith_toMachine`: the complete output/private-state law
  agrees for every shared stateful handler.

This module supplies syntax and denotation only. It does not claim the resource bounds of a fixed
universal interpreter or charge the cost of an implementation of the external handler. In
particular, runtime controller, copying and query-marshalling work are not part of `descLen` and
need separate bounds when an interpreter is introduced.

## References

The first-order description interface and its encoding are original to this module.
-/

@[expose] public section

namespace Turing.MultiTapePTM.Universal

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM

/-- A transition key: the ordinary input/work heads, extended by one answer-head symbol per
declared oracle operation. The work and answer lists are first-order finite vectors. -/
structure Key extends Turing.MultiTapeTM.Universal.Key where
  /-- Symbols under the oracle answer heads, in operation-tag order. -/
  answers : List (Option ℕ)
deriving DecidableEq, Inhabited

/-- A first-order oracle-machine action.

An ordinary step reuses the deterministic universal action and adds finite lists of query-buffer
writes and answer-head moves. A query stores a natural operation tag and successor state. -/
inductive Act where
  /-- Update ordinary tapes and all communication channels. Missing list entries mean no write or
  no move; entries past the declared operation count are ignored. -/
  | step (ordinary : Turing.MultiTapeTM.Universal.Act) (querySymbols : List (Option ℕ))
      (answerMoves : List SignType)
  /-- Submit the selected channel. An out-of-range tag denotes a local halting step. -/
  | query (operation : ℕ) (next : ℕ)
deriving Inhabited

/-- The two actions selected by one private fair coin. -/
structure Branches where
  /-- Action for coin value `false`. -/
  falseBranch : Act
  /-- Action for coin value `true`. -/
  trueBranch : Act
deriving Inhabited

/-- A finite fair-coin oracle-machine description. Table lookup uses the first matching key. -/
structure Desc where
  /-- Number of ordinary work tapes. -/
  tapes : ℕ
  /-- Number of user control states. Denotation adds one finite trap control for an invalid initial
  tag; it is not addressable by a valid transition. -/
  states : ℕ
  /-- Number of oracle-operation tags. -/
  operations : ℕ
  /-- Initial control state. -/
  q₀ : ℕ
  /-- Transition table, with both Boolean branches stored explicitly. -/
  table : List (Key × Branches)
deriving Inhabited

/-- Select the explicitly stored action for a coin value. -/
def Branches.get (branches : Branches) : Bool → Act
  | false => branches.falseBranch
  | true => branches.trueBranch

@[simp] theorem Branches.get_false (branches : Branches) :
    branches.get false = branches.falseBranch := rfl

@[simp] theorem Branches.get_true (branches : Branches) :
    branches.get true = branches.trueBranch := rfl

/-- Denotation uses exactly the declared user controls plus one malformed-initial trap control. -/
theorem Desc.card_control (d : Desc) :
    Fintype.card (Option (Fin d.states)) = d.states + 1 := by
  simp only [Fintype.card_option, Fintype.card_fin]

/-- Decode the optional successor of an ordinary action. A missing state or an invalid state tag
halts; a valid state resumes outside the malformed-initial trap. -/
def nextControl (states : ℕ) : Option ℕ → Option (Option (Fin states))
  | none => none
  | some tag => (Fin.ofNat? states tag).map some

@[simp] theorem nextControl_none (states : ℕ) : nextControl states none = none := rfl

@[simp] theorem nextControl_some_of_lt (states tag : ℕ) (h : tag < states) :
    nextControl states (some tag) = some (some ⟨tag, h⟩) := by
  simp only [nextControl, Fin.ofNat?_eq_some_of_lt states tag h, Option.map_some]

@[simp] theorem nextControl_some_of_not_lt (states tag : ℕ) (h : ¬ tag < states) :
    nextControl states (some tag) = none := by
  simp only [nextControl, Fin.ofNat?_eq_none_of_not_lt states tag h, Option.map_none]

/-- An ordinary local action represented with finite lists denotes an action on exactly `tapes`
work tapes and the finite control `Option (Fin states)`. Missing work-tape entries leave a tape
unchanged and do not move its head. -/
def localAction (tapes states : ℕ) (action : Turing.MultiTapeTM.Universal.Act) :
    Turing.Action tapes ℕ (Option (Fin states)) where
  inputTape := action.inputTape
  workTapes tape := action.workTapes.getD tape.val (none, 0)
  output := action.output
  state := nextControl states action.state

/-- The local halting action used for missing transitions and malformed query tags. -/
def haltAction (tapes states operations : ℕ) :
    Turing.MultiTapeMachine.Action tapes ℕ (Option (Fin states)) (Fin operations) :=
  .step
    { inputTape := 0
      workTapes := fun _ => (none, 0)
      output := none
      state := none }
    (fun _ => none) (fun _ => 0)

/-- Interpret one first-order action at fixed tape, state and operation counts. -/
def Act.toAction (tapes states operations : ℕ) :
    Act → Turing.MultiTapeMachine.Action tapes ℕ (Option (Fin states)) (Fin operations)
  | .step ordinary querySymbols answerMoves =>
    .step (localAction tapes states ordinary)
      (fun operation => querySymbols.getD operation.val none)
      (fun operation => answerMoves.getD operation.val 0)
  | .query operation next =>
    if hop : operation < operations then
      if hnext : next < states then .query ⟨operation, hop⟩ (some ⟨next, hnext⟩)
      else haltAction tapes states operations
    else haltAction tapes states operations

@[simp] theorem Act.toAction_step (tapes states operations : ℕ)
    (ordinary : Turing.MultiTapeTM.Universal.Act) (querySymbols : List (Option ℕ))
    (answerMoves : List SignType) :
    (Act.step ordinary querySymbols answerMoves).toAction tapes states operations =
      .step (localAction tapes states ordinary)
        (fun operation => querySymbols.getD operation.val none)
        (fun operation => answerMoves.getD operation.val 0) := rfl

@[simp] theorem Act.toAction_query_of_lt (tapes states operations operation next : ℕ)
    (hop : operation < operations) (hnext : next < states) :
    (Act.query operation next).toAction tapes states operations =
      .query ⟨operation, hop⟩ (some ⟨next, hnext⟩) := by
  simp only [Act.toAction, hop, hnext, dite_true]

@[simp] theorem Act.toAction_query_of_operation_not_lt
    (tapes states operations operation next : ℕ) (h : ¬ operation < operations) :
    (Act.query operation next).toAction tapes states operations =
      haltAction tapes states operations := by
  simp only [Act.toAction, h, dite_false]

@[simp] theorem Act.toAction_query_of_next_not_lt
    (tapes states operations operation next : ℕ) (hop : operation < operations)
    (hnext : ¬ next < states) :
    (Act.query operation next).toAction tapes states operations =
      haltAction tapes states operations := by
  simp only [Act.toAction, hop, hnext, dite_true, dite_false]

/-- Form the exact finite transition key read by a denoted description. -/
def key {tapes operations : ℕ} (state : ℕ) (input : Option ℕ)
    (work : Fin tapes → Option ℕ) (answers : Fin operations → Option ℕ) : Key where
  state := state
  input := input
  work := List.ofFn work
  answers := List.ofFn answers

/-- Look up and interpret the branch chosen by `coin`. A missing transition halts locally. -/
def Desc.action (d : Desc) (state : Option (Fin d.states)) (input : Option ℕ)
    (work : Fin d.tapes → Option ℕ) (answers : Fin d.operations → Option ℕ)
    (coin : Bool) :
    Turing.MultiTapeMachine.Action d.tapes ℕ (Option (Fin d.states)) (Fin d.operations) :=
  match state with
  | none => haltAction d.tapes d.states d.operations
  | some state =>
    match d.table.find? (·.1 = key state.val input work answers) with
    | none => haltAction d.tapes d.states d.operations
    | some entry => (entry.2.get coin).toAction d.tapes d.states d.operations

/-- Denote a finite description as a fair-coin multi-tape machine. The operation type is the
description's finite tag set; no operation-dispatch callback remains in the denotation. -/
def Desc.toMachine (d : Desc) :
    MultiTapePTM d.tapes ℕ (Option (Fin d.states)) (Fin d.operations) where
  initial := Fin.ofNat? d.states d.q₀
  tr state input work answers coin := d.action state input work answers coin

@[simp] theorem Desc.toMachine_initial (d : Desc) :
    d.toMachine.initial = Fin.ofNat? d.states d.q₀ := rfl

theorem Desc.toMachine_tr (d : Desc) (state : Option (Fin d.states))
    (input : Option ℕ)
    (work : Fin d.tapes → Option ℕ) (answers : Fin d.operations → Option ℕ)
    (coin : Bool) :
    d.toMachine.tr state input work answers coin = d.action state input work answers coin := rfl

/-! ### Injective description encoding -/

/-- Transition keys retain the deterministic key layout and append the framed answer-symbol
vector. -/
enc_structure eKey : Key flattened toKey : Turing.MultiTapeTM.Universal.eKey where
  state : encUnary, input : Turing.MultiTapeTM.Universal.eSym,
  work : (encList Turing.MultiTapeTM.Universal.eSym),
  answers : (encList Turing.MultiTapeTM.Universal.eSym)

/-- Actions use an `encSum` constructor tag. The ordinary-step payload contains the existing
ordinary action, then framed query-write and answer-move vectors; the query payload contains unary
operation and state tags. -/
enc_inductive eAct : Act where
  | step : Turing.MultiTapeTM.Universal.eAct,
      (encList Turing.MultiTapeTM.Universal.eSym), (encList encSign)
  | query : encUnary, encUnary

-- These two implementation declarations are generated with fixed names by `enc_inductive`.
attribute [nolint defsWithUnderscore] eAct_toSum eAct_elim

/-- The pair of explicitly stored Boolean branches, in `false`, `true` order. -/
enc_structure eBranches : Branches where falseBranch : eAct, trueBranch : eAct

/-- Description encoding as a right-associated tuple in declaration order: unary tape count,
unary user-state count, unary operation count, unary initial-state tag, then the framed list of
framed key/branch pairs. -/
enc_structure eDesc : Desc where
  tapes : encUnary, states : encUnary, operations : encUnary, q₀ : encUnary,
  table : (encList (encPair eKey eBranches))

/-- The transition-key encoding is injective. -/
theorem eKey_injective : Function.Injective eKey := eKey.injective

/-- The tagged action encoding is injective. -/
theorem eAct_injective : Function.Injective eAct := eAct.injective

/-- The complete description encoding is injective. -/
theorem eDesc_injective : Function.Injective eDesc := eDesc.injective

/-- Bit length of the injective first-order description encoding. -/
def descLen (d : Desc) : ℕ := (eDesc d).length

/-! ### Exact open semantics -/

/-- Run a description with private fair coins and exposed word-valued oracle channels. -/
noncomputable def Desc.runOracle (d : Desc) (fuel : ℕ) (input : List ℕ) :
    ProbOracleComp (fun _ : Fin d.operations × List ℕ => List ℕ) (List ℕ) :=
  d.toMachine.runOracle fuel input

/-- Description execution is exactly its common-machine denotation, as an open oracle program and
before choosing or interpreting any external handler. -/
theorem Desc.runOracle_eq_toMachine (d : Desc) (fuel : ℕ) (input : List ℕ) :
    d.runOracle fuel input = d.toMachine.runOracle fuel input := rfl

/-- Exact open-run semantics for every shared stateful handler, including its final private
state. This is equality of full probability laws; no statelessness or channel independence is
assumed. -/
theorem Desc.runWith_toMachine {OracleState : Type} (d : Desc)
    (handler : Fin d.operations × List ℕ → StateT OracleState PMF (List ℕ))
    (fuel : ℕ) (input : List ℕ) (state : OracleState) :
    ProbOracleComp.runWith handler (d.runOracle fuel input) state =
      ProbOracleComp.runWith handler (d.toMachine.runOracle fuel input) state := rfl

@[simp] theorem Desc.runOracle_zero (d : Desc) (input : List ℕ) :
    d.runOracle 0 input = pure [] := rfl

/-- The empty table always selects the local halting action, independently of the coin. -/
theorem Desc.action_empty (tapes states operations q₀ : ℕ)
    (state : Option (Fin states)) (input : Option ℕ) (work : Fin tapes → Option ℕ)
    (answers : Fin operations → Option ℕ) (coin : Bool) :
    ({ tapes := tapes, states := states, operations := operations, q₀ := q₀,
        table := [] } : Desc).action state input work answers coin =
      haltAction tapes states operations := by
  cases state <;> rfl

/-- A successful first-match table lookup determines the selected branch exactly. This exposes
table semantics without requiring clients to unfold the denotation. -/
theorem Desc.action_of_find_eq_some (d : Desc) (state : Fin d.states)
    (input : Option ℕ) (work : Fin d.tapes → Option ℕ)
    (answers : Fin d.operations → Option ℕ) (coin : Bool) (entry : Key × Branches)
    (hfind : d.table.find? (·.1 = key state.val input work answers) = some entry) :
    d.action (some state) input work answers coin =
      (entry.2.get coin).toAction d.tapes d.states d.operations := by
  simp only [Desc.action, hfind]

/-- A matching head entry is selected before the rest of the table. This equation also exposes
the exact conversion of the selected Boolean branch to a machine action. -/
theorem Desc.action_cons_hit (tapes states operations q₀ : ℕ)
    (state : Fin states) (input : Option ℕ) (work : Fin tapes → Option ℕ)
    (answers : Fin operations → Option ℕ) (branches : Branches)
    (table : List (Key × Branches)) (coin : Bool) :
    ({ tapes := tapes, states := states, operations := operations, q₀ := q₀,
        table := (key state.val input work answers, branches) :: table } : Desc).action
      (some state) input work answers coin =
      (branches.get coin).toAction tapes states operations := by
  simp [Desc.action]

theorem Desc.action_cons_hit_false (tapes states operations q₀ : ℕ)
    (state : Fin states) (input : Option ℕ) (work : Fin tapes → Option ℕ)
    (answers : Fin operations → Option ℕ) (branches : Branches)
    (table : List (Key × Branches)) :
    ({ tapes := tapes, states := states, operations := operations, q₀ := q₀,
        table := (key state.val input work answers, branches) :: table } : Desc).action
      (some state) input work answers false =
      branches.falseBranch.toAction tapes states operations := by
  simpa only [Branches.get_false] using
    Desc.action_cons_hit tapes states operations q₀ state input work answers branches table false

theorem Desc.action_cons_hit_true (tapes states operations q₀ : ℕ)
    (state : Fin states) (input : Option ℕ) (work : Fin tapes → Option ℕ)
    (answers : Fin operations → Option ℕ) (branches : Branches)
    (table : List (Key × Branches)) :
    ({ tapes := tapes, states := states, operations := operations, q₀ := q₀,
        table := (key state.val input work answers, branches) :: table } : Desc).action
      (some state) input work answers true =
      branches.trueBranch.toAction tapes states operations := by
  simpa only [Branches.get_true] using
    Desc.action_cons_hit tapes states operations q₀ state input work answers branches table true

end Turing.MultiTapePTM.Universal
