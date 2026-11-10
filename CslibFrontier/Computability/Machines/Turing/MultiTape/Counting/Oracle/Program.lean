/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Program

/-!
# Occurrence programs with word oracles

The existing shared machine program separates occurrence-index queries from word-oracle calls.
Its List interpreter keeps the oracle's private state local to each branch: sibling occurrences
start with the same state, while successive calls within a branch share the updated state.
The observer records every live transition index, including indices of query instructions.
Equal actions at different positions remain distinct occurrences.

This is an interpretation of `MultiTapeMachine.runConfigFrom`, not another machine model.
A query instruction costs one native transition; request construction and reply-head access use
ordinary transitions. The oracle's computation is external. Retaining a complete reply in this
semantic configuration is not a claim that an encoded interpreter can copy it at unit cost.

## Main definitions

* `Turing.MultiTapeMachine.occurrenceOracleSpec`: separate occurrence and word-query interfaces.
* `Turing.MultiTapeMachine.runOccurrenceProgram`: the existing shared run with occurrence choices.
* `Turing.MultiTapeMachine.occurrenceTraceHandler`: branch-local state and an occurrence observer.
* `Turing.MultiTapeMachine.runOccurrenceTrace`: full configurations, traces and private states.

## Main results

* `Turing.MultiTapeMachine.interpret_runOccurrenceProgram_succ`: actual indexed transitions.
* `Turing.MultiTapeMachine.runOccurrenceTrace_erase`: erasure gives the ordinary interpretation.

The raw clocked run retains live endpoints. Attempting an empty local list has no outcome.
Neither the List interpretation nor a clock alone asserts nonblocking, halting or polynomial-time
realizability.
In particular, the generic PMF-based `MultiTapeMachine.HaltsWithin` is not used: the occurrence
interface includes `Fin 0`, which admits no probability distribution.

## References

Reuses the shared native machine and program infrastructure credited in `MultiTape.Machine` and
`MultiTape.Machine.Program`, and occurrence enumeration from `MultiTape.Counting.Program`.
The typed oracle calculus credits Samuel Schlesinger, Devon Tuma, Quang Dao and VCVio in
`Languages.Probabilistic.Basic`. Language-oracle/path-counting conventions are described in
[L. Fortnow, *Counting Complexity*][Fortnow1997], Section 2 and Definition 3.1; arbitrary stateful
word handlers here are an explicit generalization of the language-oracle interface.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

/-- Occurrence positions and external word calls are separate effects. -/
abbrev occurrenceOracleSpec (Operation Symbol : Type) : ℕ ⊕ (Operation × List Symbol) → Type
  | .inl n => MultiTapeCTM.occurrenceSpec n
  | .inr _ => List Symbol

variable {k : ℕ} {Symbol Control Operation : Type} [DecidableEq Operation]
  {input : List Symbol}

/-- The shared clocked program with occurrence choices and actual buffered word queries. -/
def runOccurrenceProgram (machine : MultiTapeMachine k Symbol Control Operation List)
    (fuel : ℕ) (cfg : Config k Symbol Control Operation input) :
    OracleComp (occurrenceOracleSpec Operation Symbol) (Config k Symbol Control Operation input) :=
  machine.runConfigFrom
    (fun choices => OracleComp.interpret
      (fun n => OracleComp.query (spec := occurrenceOracleSpec Operation Symbol) (.inl n))
      (MultiTapeCTM.chooseOccurrence choices))
    (fun op word => OracleComp.query (spec := occurrenceOracleSpec Operation Symbol)
      (.inr (op, word))) fuel cfg

/-- Enumerate occurrences with separate copies of the incoming state. Queries update only the
state of their own branch; the trace records indices, not external calls or terminal padding. -/
def occurrenceTraceHandler {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) :
    (q : ℕ ⊕ (Operation × List Symbol)) →
      StateT (List ℕ × S) List (occurrenceOracleSpec Operation Symbol q)
  | .inl n => fun (trace, s) =>
      List.ofFn fun index : Fin n => (index, (trace ++ [index.val], s))
  | .inr q => fun (trace, s) =>
      let (answer, next) := oracle q s
      [(answer, (trace, next))]

/-- Observe the shared run from an empty trace, retaining live cutoff configurations. -/
def runOccurrenceTrace (machine : MultiTapeMachine k Symbol Control Operation List)
    (fuel : ℕ) (cfg : Config k Symbol Control Operation input) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    List ((List ℕ × Config k Symbol Control Operation input) × S) :=
  ((OracleComp.interpret (occurrenceTraceHandler oracle)
    (machine.runOccurrenceProgram fuel cfg)).run ([], s)).map
      fun (final, trace, state) => ((trace, final), state)

@[simp] theorem runOccurrenceProgram_zero
    (machine : MultiTapeMachine k Symbol Control Operation List)
    (cfg : Config k Symbol Control Operation input) :
    machine.runOccurrenceProgram 0 cfg = pure cfg := rfl

/-- No further occurrence or oracle call is made after halting. -/
theorem runOccurrenceProgram_halted (machine : MultiTapeMachine k Symbol Control Operation List)
    (fuel : ℕ) {cfg : Config k Symbol Control Operation input} (h : cfg.tapes.state = none) :
    machine.runOccurrenceProgram fuel cfg = pure cfg :=
  machine.runConfigFrom_halted _ _ fuel cfg h

/-- One live instruction preserves index order and threads private state only along its branch. -/
theorem interpret_runOccurrenceProgram_succ
    (machine : MultiTapeMachine k Symbol Control Operation List)
    (fuel : ℕ) (cfg : Config k Symbol Control Operation input) (state : Control)
    (h : cfg.tapes.state = some state) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (trace : List ℕ) (s : S) :
    (OracleComp.interpret (occurrenceTraceHandler oracle)
      (machine.runOccurrenceProgram (fuel + 1) cfg)).run (trace, s) =
      (List.ofFn (id : Fin (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols).length → _)).flatMap fun index =>
        match (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols)[index] with
        | .step action symbol move =>
          (OracleComp.interpret (occurrenceTraceHandler oracle)
            (machine.runOccurrenceProgram fuel (cfg.step action symbol move))).run
              (trace ++ [index.val], s)
        | .query op next =>
          let (answer, nextState) := oracle (op, (cfg.channels op).queryBuffer) s
          (OracleComp.interpret (occurrenceTraceHandler oracle)
            (machine.runOccurrenceProgram fuel (cfg.receive op next answer))).run
              (trace ++ [index.val], nextState) := by
  simp only [runOccurrenceProgram, runConfigFrom, h, MultiTapeCTM.chooseOccurrence,
    OracleComp.interpret_map, OracleComp.interpret_query, OracleComp.interpret_bind,
    StateT.run_bind, StateT.run_map]
  dsimp only [occurrenceTraceHandler, StateT.run]
  simp only [List.map_eq_map, List.ofFn_eq_map, List.map_map,
    List.bind_eq_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro index _
  simp only [Function.comp_apply, id_eq]
  cases (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
    cfg.answerSymbols)[index.val] with
  | step => rfl
  | query op next =>
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query]
    change _ ++ [] = _
    exact List.append_nil _

/-- The same branch-local interpreter without the trace observer. -/
def occurrenceHandler {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) :
    (q : ℕ ⊕ (Operation × List Symbol)) →
      StateT S List (occurrenceOracleSpec Operation Symbol q)
  | .inl n => fun s => List.ofFn fun index : Fin n => (index, s)
  | .inr q => fun s => [oracle q s]

omit [DecidableEq Operation] in
/-- Erasing the observer preserves the ordinary interpretation and the complete private state. -/
theorem interpret_occurrenceTraceHandler_erase {S α : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S)
    (program : OracleComp (occurrenceOracleSpec Operation Symbol) α) (trace : List ℕ) (s : S) :
    ((OracleComp.interpret (occurrenceTraceHandler oracle) program).run (trace, s)).map
        (fun (a, _, state) => (a, state)) =
      (OracleComp.interpret (occurrenceHandler oracle) program).run s := by
  induction program using PFunctor.FreeM.induction generalizing trace s with
  | pure a => simp
  | lift_bind q next ih =>
    change ((OracleComp.interpret (occurrenceTraceHandler oracle)
      (OracleComp.query q >>= next)).run _).map _ =
      (OracleComp.interpret (occurrenceHandler oracle) (OracleComp.query q >>= next)).run _
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind]
    cases q with
    | inl n =>
      dsimp only [occurrenceTraceHandler, occurrenceHandler, StateT.run]
      simp only [List.bind_eq_flatMap, List.ofFn_eq_map, List.flatMap_map, List.map_flatMap]
      apply List.flatMap_congr
      intro index _
      exact ih index (trace ++ [index.val]) s
    | inr q =>
      dsimp only [occurrenceTraceHandler, occurrenceHandler, StateT.run]
      simpa only [List.bind_eq_flatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        StateT.run] using
        ih (oracle q s).1 trace (oracle q s).2

/-- The recorded run differs from the ordinary shared-program interpretation only by its log. -/
theorem runOccurrenceTrace_erase (machine : MultiTapeMachine k Symbol Control Operation List)
    (fuel : ℕ) (cfg : Config k Symbol Control Operation input) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    (machine.runOccurrenceTrace fuel cfg oracle s).map (fun ((_, final), state) => (final, state)) =
      (OracleComp.interpret (occurrenceHandler oracle)
        (machine.runOccurrenceProgram fuel cfg)).run s := by
  simpa only [runOccurrenceTrace, List.map_map, Function.comp_def] using
    interpret_occurrenceTraceHandler_erase oracle (machine.runOccurrenceProgram fuel cfg) [] s

end Turing.MultiTapeMachine
