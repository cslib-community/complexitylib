/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Oracle.Program
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Certificate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Execution

/-!
# Canonical replay of oracle occurrence traces

Replay follows the existing native instructions and makes their actual buffered oracle calls.
A fixed-length certificate contains one occurrence index per live instruction, followed only by
zeros after the first halt. Those padding zeros are not recorded as transitions. Exhausting a
certificate at a live configuration retains that configuration; terminal filtering is separate.

## Main definitions

* `Turing.MultiTapeMachine.indexWords`: chronological fixed-length index enumeration.
* `Turing.MultiTapeMachine.replayIndices`: actual word-query replay with canonical padding.
* `Turing.MultiTapeMachine.replayResult`: retain successful replay and its final private state.
* `Turing.MultiTapeMachine.replayTerminal`: terminal observation, excluding live cutoffs.

## Main results

* `Turing.MultiTapeMachine.filterMap_replayResult`: exact ordered enumeration of native runs.
* `Turing.MultiTapeMachine.countP_replayResult_terminal`: equality of terminal verdict counts.
* `Turing.MultiTapeMachine.runOccurrenceTrace_empty`: raw closed-run compatibility.
* `Turing.MultiTapeMachine.replayTerminal_empty`: the existing closed certificate decoder.

All replayed certificates start with the same external state. Different certificates may reach
equal configurations, but distinct consumed indices and their List multiplicities are retained.
The explicit positive arity bound concerns list lengths, not the number of distinct actions.
No nonblocking, halting or encoded polynomial-time conclusion is implicit. This is a semantic
replay program, not yet a certified efficient binary checker. The query and reply cost boundary
are stated in `MultiTape.Counting.Oracle.Program`.

## References

Reuses the existing occurrence certificates in `MultiTape.Counting.Certificate` and the native
program and List interpretation in `MultiTape.Counting.Oracle.Program`; their formalization and
mathematical source credits apply here. The stateful word interface is explicitly more general
than the language-oracle interface in [Fortnow1997], Section 2 and Definition 3.1.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

/-- Enumerate fixed-width index words in chronological order: the current digit is outermost.
Generating all `bound ^ fuel` words is not asserted to take polynomial time in `fuel`. -/
def indexWords (bound : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | fuel + 1 => (List.range bound).flatMap fun index =>
      (indexWords bound fuel).map (index :: ·)

/-- The enumeration contains exactly the words of the required length and digit range. -/
theorem mem_indexWords (bound fuel : ℕ) (word : List ℕ) :
    word ∈ indexWords bound fuel ↔ word.length = fuel ∧ ∀ index ∈ word, index < bound := by
  induction fuel generalizing word with
  | zero => cases word <;> simp [indexWords]
  | succ fuel ih =>
    cases word with
    | nil => simp [indexWords]
    | cons index rest => simp [indexWords, ih, and_assoc, and_left_comm]

/-- Each fixed-length index word occurs once. -/
theorem nodup_indexWords (bound fuel : ℕ) : (indexWords bound fuel).Nodup := by
  induction fuel with
  | zero => simp [indexWords]
  | succ fuel ih =>
    change ((List.range bound).flatMap _).Nodup
    refine List.nodup_flatMap.mpr ⟨fun _ _ => ih.map List.cons_injective, ?_⟩
    apply List.nodup_range.imp
    intro left right hne
    simp only [List.disjoint_left, List.mem_map]
    rintro word ⟨xs, _, rfl⟩ ⟨ys, _, heq⟩
    exact hne (List.cons.inj heq).1.symm

variable {k : ℕ} {Symbol Control Operation : Type} [DecidableEq Operation]
  {input : List Symbol}

/-- Replay after an already recorded trace; newly consumed indices are appended to it.
The trace is an observer and does not alter the native machine configuration. -/
def replayIndicesFrom (machine : MultiTapeMachine k Symbol Control Operation List) :
    Config k Symbol Control Operation input → List ℕ → List ℕ →
      OracleComp (fun _ : Operation × List Symbol => List Symbol)
        (Option (List ℕ × Config k Symbol Control Operation input))
  | cfg, trace, [] => pure (some (trace, cfg))
  | cfg, trace, index :: rest => match cfg.tapes.state with
    | none => if index = 0 then replayIndicesFrom machine cfg trace rest else pure none
    | some state => match (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols)[index]? with
      | none => pure none
      | some (.step action symbol move) =>
        replayIndicesFrom machine (cfg.step action symbol move) (trace ++ [index]) rest
      | some (.query op next) => do
        let answer ← OracleComp.query (op, (cfg.channels op).queryBuffer)
        replayIndicesFrom machine (cfg.receive op next answer) (trace ++ [index]) rest

/-- Replay real instructions, rejecting invalid indices and nonzero padding after halting.
At exhaustion a live endpoint is retained. Only live instructions enter the consumed trace. -/
def replayIndices (machine : MultiTapeMachine k Symbol Control Operation List)
    (cfg : Config k Symbol Control Operation input) (word : List ℕ) :
    OracleComp (fun _ : Operation × List Symbol => List Symbol)
      (Option (List ℕ × Config k Symbol Control Operation input)) :=
  replayIndicesFrom machine cfg [] word

private def replayAuxResult (machine : MultiTapeMachine k Symbol Control Operation List)
    (cfg : Config k Symbol Control Operation input) (trace word : List ℕ) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    Option ((List ℕ × Config k Symbol Control Operation input) × S) :=
  let (result, next) := Id.run ((OracleComp.interpret (m := StateT S Id) oracle
    (replayIndicesFrom machine cfg trace word)).run s)
  result.map (·, next)

/-- Successful replay together with its final external state. Failed certificates are excluded,
including any private-state effects before a late failure; sibling replays never share them. -/
def replayResult (machine : MultiTapeMachine k Symbol Control Operation List)
    (cfg : Config k Symbol Control Operation input) (word : List ℕ) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    Option ((List ℕ × Config k Symbol Control Operation input) × S) :=
  let (result, next) := Id.run ((OracleComp.interpret (m := StateT S Id) oracle
    (machine.replayIndices cfg word)).run s)
  result.map (·, next)

private theorem replayAuxResult_halted
    (machine : MultiTapeMachine k Symbol Control Operation List)
    (cfg : Config k Symbol Control Operation input) (h : cfg.tapes.state = none)
    (trace rest : List ℕ) (index : ℕ) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    replayAuxResult machine cfg trace (index :: rest) oracle s =
      if index = 0 then replayAuxResult machine cfg trace rest oracle s else none := by
  unfold replayAuxResult
  simp only [replayIndicesFrom, h]
  split_ifs <;> rfl

private theorem replayAuxResult_live
    (machine : MultiTapeMachine k Symbol Control Operation List)
    (cfg : Config k Symbol Control Operation input) (state : Control)
    (h : cfg.tapes.state = some state) (trace rest : List ℕ) (index : ℕ) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    replayAuxResult machine cfg trace (index :: rest) oracle s =
      match (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols)[index]? with
      | none => none
      | some (.step action symbol move) =>
        replayAuxResult machine (cfg.step action symbol move) (trace ++ [index]) rest oracle s
      | some (.query op next) =>
        let (answer, nextState) := oracle (op, (cfg.channels op).queryBuffer) s
        replayAuxResult machine (cfg.receive op next answer) (trace ++ [index]) rest oracle
          nextState := by
  unfold replayAuxResult
  simp only [replayIndicesFrom, h]
  cases (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
    cfg.answerSymbols)[index]? with
  | none => rfl
  | some action => cases action <;> rfl

private theorem flatMap_range_getElem? {α β : Type} (choices : List α)
    (f : ℕ → α → List β) (bound : ℕ) (hbound : choices.length ≤ bound) :
    (List.range bound).flatMap (fun index => (choices[index]?).toList.flatMap (f index)) =
      (List.finRange choices.length).flatMap (fun index => f index.val choices[index]) := by
  have trim : ∀ n, choices.length ≤ n →
      (List.range n).flatMap (fun index => (choices[index]?).toList.flatMap (f index)) =
        (List.range choices.length).flatMap
          (fun index => (choices[index]?).toList.flatMap (f index)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      simp [List.range_succ, List.flatMap_append, List.getElem?_eq_none hn, ih]
  rw [trim bound hbound]
  have hrange : (List.finRange choices.length).map Fin.val = List.range choices.length := by
    apply List.ext_getElem <;> simp
  rw [← hrange, List.flatMap_map]
  apply List.flatMap_congr
  intro index _
  simp

private theorem flatMap_range_zero {α : Type} (bound : ℕ) (hbound : 0 < bound) (values : List α) :
    (List.range bound).flatMap (fun index => if index = 0 then values else []) = values := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hbound)
  simp [List.range_succ_eq_map, List.flatMap_map]

private theorem filterMap_replayAuxResult
    (machine : MultiTapeMachine k Symbol Control Operation List) (bound : ℕ) (hpos : 0 < bound)
    (hbound : ∀ state symbol work answers, (machine.tr state symbol work answers).length ≤ bound)
    (fuel : ℕ) (cfg : Config k Symbol Control Operation input) (trace : List ℕ) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    (indexWords bound fuel).filterMap
        (fun word => replayAuxResult machine cfg trace word oracle s) =
      ((OracleComp.interpret (occurrenceTraceHandler oracle)
        (machine.runOccurrenceProgram fuel cfg)).run (trace, s)).map
          (fun (final, choices, state) => ((choices, final), state)) := by
  induction fuel generalizing cfg trace s with
  | zero => rfl
  | succ fuel ih =>
    simp only [indexWords, List.filterMap_flatMap, List.filterMap_map, Function.comp_def]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [replayAuxResult_halted machine cfg hs]
      have hz (index : ℕ) :
          (indexWords bound fuel).filterMap (fun rest =>
            if index = 0 then replayAuxResult machine cfg trace rest oracle s else none) =
          if index = 0 then
            (indexWords bound fuel).filterMap
              (fun rest => replayAuxResult machine cfg trace rest oracle s) else [] := by
        by_cases hi : index = 0 <;> simp [hi]
      simp_rw [hz]
      rw [flatMap_range_zero bound hpos, ih]
      simp [machine.runOccurrenceProgram_halted fuel hs,
        machine.runOccurrenceProgram_halted (fuel + 1) hs]
    | some state =>
      let following (index : ℕ) (action : Action k Symbol Control Operation) :=
        match action with
        | .step action symbol move =>
          (indexWords bound fuel).filterMap fun rest =>
            replayAuxResult machine (cfg.step action symbol move) (trace ++ [index]) rest oracle s
        | .query op next =>
          let (answer, nextState) := oracle (op, (cfg.channels op).queryBuffer) s
          (indexWords bound fuel).filterMap fun rest =>
            replayAuxResult machine (cfg.receive op next answer) (trace ++ [index]) rest oracle
              nextState
      have hf (index : ℕ) :
          (indexWords bound fuel).filterMap
              (fun rest => replayAuxResult machine cfg trace (index :: rest) oracle s) =
            ((machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
              cfg.answerSymbols)[index]?).toList.flatMap (following index) := by
        simp only [replayAuxResult_live machine cfg state hs]
        cases (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols)[index]? with
        | none => simp
        | some action => cases action <;> simp [following]
      simp_rw [hf]
      rw [flatMap_range_getElem? _ following bound (hbound ..),
        interpret_runOccurrenceProgram_succ machine fuel cfg state hs oracle trace s,
        List.map_flatMap]
      change (List.finRange _).flatMap _ = (List.finRange _).flatMap _
      apply List.flatMap_congr
      intro index _
      dsimp only [following]
      cases (machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols)[index.val] <;> exact ih _ _ _

/-- Canonical fixed-clock certificates enumerate the exact ordered native run, retaining every
consumed index, complete configuration and branch-local private state. Live cutoff endpoints are
retained. This equality requires neither nonblocking nor a halting premise. -/
theorem filterMap_replayResult (machine : MultiTapeMachine k Symbol Control Operation List)
    (bound : ℕ) (hpos : 0 < bound)
    (hbound : ∀ state symbol work answers, (machine.tr state symbol work answers).length ≤ bound)
    (fuel : ℕ) (cfg : Config k Symbol Control Operation input) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    (indexWords bound fuel).filterMap (fun word => machine.replayResult cfg word oracle s) =
      machine.runOccurrenceTrace fuel cfg oracle s :=
  filterMap_replayAuxResult machine bound hpos hbound fuel cfg [] oracle s

/-- A halted replay accepts exactly the all-zero suffix and makes no external call. -/
theorem replayIndicesFrom_halted
    (machine : MultiTapeMachine k Symbol Control Operation List)
    (cfg : Config k Symbol Control Operation input) (h : cfg.tapes.state = none)
    (trace word : List ℕ) :
    machine.replayIndicesFrom cfg trace word =
      pure (if word = List.replicate word.length 0 then some (trace, cfg) else none) := by
  induction word with
  | nil => rfl
  | cons index rest ih =>
    simp only [replayIndicesFrom, h, List.length_cons, List.replicate_succ, List.cons.injEq]
    by_cases hi : index = 0 <;> simp [hi, ih]

/-- Terminal observation is separate from raw replay. Live cutoff endpoints fail this check. -/
def replayTerminal (machine : MultiTapeMachine k Symbol Control Operation List)
    (cfg : Config k Symbol Control Operation input) (word : List ℕ) :
    OracleComp (fun _ : Operation × List Symbol => List Symbol)
      (Option (List ℕ × Config k Symbol Control Operation input)) :=
  (Option.filter fun result => result.2.tapes.state.isNone) <$> machine.replayIndices cfg word

/-- Filtering canonical replay and filtering the native run give the same terminal occurrences. -/
theorem filterMap_replayResult_terminal
    (machine : MultiTapeMachine k Symbol Control Operation List) (bound : ℕ) (hpos : 0 < bound)
    (hbound : ∀ state symbol work answers, (machine.tr state symbol work answers).length ≤ bound)
    (fuel : ℕ) (cfg : Config k Symbol Control Operation input) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S) :
    (indexWords bound fuel).filterMap (fun word =>
        (machine.replayResult cfg word oracle s).filter fun result =>
          result.1.2.tapes.state.isNone) =
      (machine.runOccurrenceTrace fuel cfg oracle s).filter fun result =>
        result.1.2.tapes.state.isNone := by
  rw [← machine.filterMap_replayResult bound hpos hbound fuel cfg oracle s,
    List.filter_filterMap]

/-- Both verdict counts require successful terminal replay; invalid and live certificates count
for neither verdict, including when `verdict` is negated. -/
theorem countP_replayResult_terminal
    (machine : MultiTapeMachine k Symbol Control Operation List) (bound : ℕ) (hpos : 0 < bound)
    (hbound : ∀ state symbol work answers, (machine.tr state symbol work answers).length ≤ bound)
    (fuel : ℕ) (cfg : Config k Symbol Control Operation input) {S : Type}
    (oracle : Operation × List Symbol → S → List Symbol × S) (s : S)
    (verdict : List Symbol → Bool) :
    (indexWords bound fuel).countP (fun word => (machine.replayResult cfg word oracle s).any
        fun result => result.1.2.tapes.state.isNone && verdict result.1.2.tapes.output) =
      (machine.runOccurrenceTrace fuel cfg oracle s).countP
        (fun result => result.1.2.tapes.state.isNone && verdict result.1.2.tapes.output) := by
  rw [← machine.filterMap_replayResult bound hpos hbound fuel cfg oracle s,
    List.countP_filterMap]
  congr 1
  funext word
  cases machine.replayResult cfg word oracle s <;> rfl

private theorem runOccurrenceProgram_empty (machine : MultiTapeCTM k Symbol Control)
    (fuel : ℕ) (cfg : Config k Symbol Control Empty input) :
    machine.runOccurrenceProgram fuel cfg =
      OracleComp.interpret
        (fun n => OracleComp.query (spec := occurrenceOracleSpec Empty Symbol) (.inl n))
        (machine.runConfigFrom MultiTapeCTM.chooseOccurrence Empty.elim fuel cfg) := by
  rw [interpret_runConfigFrom]
  unfold runOccurrenceProgram
  congr 1
  funext op
  exact op.elim

private theorem interpret_runOccurrenceProgram_empty (machine : MultiTapeCTM k Symbol Control)
    (fuel : ℕ) (cfg : Config k Symbol Control Empty input) {S : Type} (s : S) :
    (OracleComp.interpret (occurrenceHandler (fun q : Empty × List Symbol => q.1.elim))
      (machine.runOccurrenceProgram fuel cfg)).run s =
      (machine.runList fuel cfg.tapes).map
        (fun final => (Config.emptyOracleEquiv.symm final, s)) := by
  rw [runOccurrenceProgram_empty, OracleComp.interpret_interpret]
  simp only [OracleComp.interpret_query]
  have heq := OracleComp.run_interpret_stateless
    (fun n => List.ofFn (id : Fin n → Fin n))
    (machine.runConfigFrom MultiTapeCTM.chooseOccurrence Empty.elim fuel cfg) s
  have hhandler : (fun n => occurrenceHandler (S := S)
      (fun q : Empty × List Symbol => q.1.elim)
      (.inl n)) = (fun n state => (fun index => (index, state)) <$>
        List.ofFn (id : Fin n → Fin n)) := by
    funext n state
    simp [occurrenceHandler, List.map_ofFn]
  rw [hhandler, heq, machine.interpret_runConfigFrom_eq_map_runList]
  simp [List.map_map, Function.comp_def]

/-- With no oracle channels, erasing the trace gives exactly the existing closed `runList`.
Both sides retain live cutoff endpoints and preserve repeated final configurations. -/
theorem runOccurrenceTrace_empty (machine : MultiTapeCTM k Symbol Control) (fuel : ℕ)
    (cfg : Cfg k Symbol Control input) {S : Type} (s : S) :
    (machine.runOccurrenceTrace fuel (Config.emptyOracleEquiv.symm cfg)
        (fun q : Empty × List Symbol => q.1.elim) s).map
        (fun ((_, final), state) => (final.tapes, state)) =
      (machine.runList fuel cfg).map (fun final => (final, s)) := by
  have heq := congrArg (List.map (fun (result : Config k Symbol Control Empty input × S) =>
      (result.1.tapes, result.2)))
    (machine.runOccurrenceTrace_erase fuel (Config.emptyOracleEquiv.symm cfg)
      (fun q : Empty × List Symbol => q.1.elim) s)
  rw [interpret_runOccurrenceProgram_empty] at heq
  simpa [List.map_map, Function.comp_def, Config.emptyOracleEquiv] using heq

private theorem replayIndicesFrom_empty_terminal (machine : MultiTapeCTM k Symbol Control)
    (cfg : Cfg k Symbol Control input) (trace word : List ℕ) :
    ((Id.run (OracleComp.interpret (m := Id) (fun q : Empty × List Symbol => q.1.elim)
        (machine.replayIndicesFrom (Config.emptyOracleEquiv.symm cfg) trace word))).filter
          (fun result => result.2.tapes.state.isNone)).map (fun (choices, final) =>
            (choices, final.tapes)) =
      (machine.decodeCertificate cfg word).map
        (fun (choices, final) => (trace ++ choices, final)) := by
  induction word generalizing cfg trace with
  | nil =>
    cases hs : cfg.state <;>
      simp [replayIndicesFrom, MultiTapeCTM.decodeCertificate, Config.emptyOracleEquiv, hs]
  | cons index rest ih =>
    cases hs : cfg.state with
    | none =>
      rw [replayIndicesFrom_halted machine _ hs]
      simp [MultiTapeCTM.decodeCertificate, hs, OracleComp.interpret_pure,
        Config.emptyOracleEquiv, apply_ite]
    | some state =>
      have ht : (Config.emptyOracleEquiv.symm cfg :
          Config k Symbol Control Empty input).tapes = cfg := rfl
      have ha : (Config.emptyOracleEquiv.symm cfg :
          Config k Symbol Control Empty input).answerSymbols = Empty.elim :=
        funext fun op => op.elim
      simp only [replayIndicesFrom, ht, ha, MultiTapeCTM.decodeCertificate,
        MultiTapeCTM.step?, MultiTapeCTM.actions, hs, List.getElem?_map]
      cases hg : (machine.tr state cfg.inputSymbol cfg.workTapeSymbols Empty.elim)[index]? with
      | none => simp
      | some action =>
        cases action with
        | query op next => exact op.elim
        | step action symbol move =>
          have hstep : (Config.emptyOracleEquiv.symm cfg : Config k Symbol Control Empty input).step
              action symbol move = Config.emptyOracleEquiv.symm (action.apply cfg) :=
            Config.ext rfl (funext fun op => op.elim)
          simpa [hg, hstep, Action.emptyOracleEquiv, List.append_assoc, Option.map_map,
            Function.comp_def] using
            ih (action.apply cfg) (trace ++ [index])

/-- The terminal closed specialization is exactly the existing canonical decoder. Raw replay
itself also retains live cutoffs, so the terminal observation in this statement is essential. -/
theorem replayTerminal_empty (machine : MultiTapeCTM k Symbol Control)
    (cfg : Cfg k Symbol Control input) (word : List ℕ) :
    (Id.run (OracleComp.interpret (m := Id) (fun q : Empty × List Symbol => q.1.elim)
      (machine.replayTerminal (Config.emptyOracleEquiv.symm cfg) word))).map
        (fun (choices, final) => (choices, final.tapes)) = machine.decodeCertificate cfg word := by
  simpa [replayTerminal, replayIndices, OracleComp.interpret_map] using
    replayIndicesFrom_empty_terminal machine cfg [] word

end Turing.MultiTapeMachine
