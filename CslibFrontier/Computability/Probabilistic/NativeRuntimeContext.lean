/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeResponseExecution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Runtime context update and a second native query

A fixed finite-control machine scans an arbitrary context word on work tape zero,
appends a framed actual reply, and emits the updated context. Native marking and
rewinding then make that same tape the input of the full native query reader.
The next request depends on both runtime context and response, without compiling
context into a continuation or resetting the shared oracle state.

This is a transport milestone for [Wang2027], model PDF pp. 4--6 and Theorem 5,
PDF p. 12/App. A.5 p. 16. The supported scheduler submits the updated context word;
it does not compile arbitrary schedulers or certify the source concurrent-batch
codec, retention/stopping policy, quantitative upper endpoint or full selector.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeRuntimeContext
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

/-- A runtime header can carry the selector's complete visible state. Fields are
transported as data; the append scheduler below updates the framed reply trailer,
not the header's budget, availability or stopping decisions. Original encodings
and the source batch codec remain separate obligations. -/
structure Header where
  /-- Encoded original instance, never compiled into control states. -/
  originalInstance : List Bool
  /-- Previously issued raw requests. -/
  requests : List (List Bool)
  /-- Previously received raw replies. -/
  replies : List (List Bool)
  /-- Private selector storage, including saved random choices. -/
  privateSelector : List Bool
  /-- Remaining turn allowance. -/
  remainingTurns : ℕ
  /-- Encoded remaining opportunities. -/
  opportunities : List Bool
  /-- Stored stopping decision. -/
  stopped : Bool
  /-- Stored output word. -/
  output : List Bool
  deriving DecidableEq

/-- Self-delimiting header fields, with the final output word as the last component. -/
@[expose] def Header.encode (header : Header) : List Bool :=
  frame header.originalInstance ++ frame (encList encBits header.requests) ++
    frame (encList encBits header.replies) ++ frame header.privateSelector ++
    frame (encUnary header.remainingTurns) ++ frame header.opportunities ++
    frame [header.stopped] ++ header.output

/-- No original instance, history, private word, budget, opportunity, stop or output
field is lost in the runtime encoding. This is a byte-format theorem, not a native
semantic parser or source-admission certificate. -/
theorem Header.encode_injective : Function.Injective Header.encode := by
  intro a b h
  simp only [Header.encode, List.append_assoc] at h
  obtain ⟨ho, h⟩ := frame_append_inj h
  obtain ⟨hreq, h⟩ := frame_append_inj h
  obtain ⟨hrep, h⟩ := frame_append_inj h
  obtain ⟨hp, h⟩ := frame_append_inj h
  obtain ⟨ht, h⟩ := frame_append_inj h
  obtain ⟨ha, h⟩ := frame_append_inj h
  obtain ⟨hs, hout⟩ := frame_append_inj h
  have hrq := (encList encBits).injective hreq
  have hrp := (encList encBits).injective hrep
  have hturn := encUnary.injective ht
  have hstop := List.singleton_injective hs
  cases a
  cases b
  simp_all

/-- Frame the header once; every native update appends one further framed reply. -/
@[expose] def Header.initialWord (header : Header) : List Bool := frame header.encode

/-- The native append format preserves the entire original header and the exact new
reply, even when either payload is empty. -/
theorem header_reply_roundtrip (header : Header) (reply : List Bool) :
    unframe (header.initialWord ++ frame reply) = header.encode ∧
      unframe (dropFrame (header.initialWord ++ frame reply)) = reply := by
  simp [Header.initialWord]

/-- Scan the stored context, then write each reply bit with its framing tag. -/
inductive Control where
  | scan
  | tag
  | value
  deriving DecidableEq

instance : Finite Control :=
  Finite.of_injective (fun | .scan => (0 : Fin 3) | .tag => 1 | .value => 2)
    (fun a b h => by cases a <;> cases b <;> simp_all)

/-- One uniform native transducer. Tape zero holds the runtime context; tape one
is reserved for virtual-input marking. No context word occurs in this code. -/
@[expose] def update : MultiTapeTM 2 Bool Control :=
  MultiTapeTM.ofTr .scan fun state input work => match state with
    | .scan => match work 0 with
      | some bit => ⟨0, fun i => if i = 0 then (none, 1) else (none, 0),
          some bit, some .scan⟩
      | none => ⟨0, fun _ => (none, 0), none, some .tag⟩
    | .tag => match input with
      | some _ => ⟨0, fun i => if i = 0 then (some (some true), 1) else (none, 0),
          some true, some .value⟩
      | none => ⟨0, fun i => if i = 0 then (some (some false), 1) else (none, 0),
          some false, none⟩
    | .value => match input with
      | some bit => ⟨1, fun i => if i = 0 then (some (some bit), 1) else (none, 0),
          some bit, some .tag⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩

/-- Exact ordinary storage and cursors of the context transducer. -/
@[expose] def updateConfig {input : List Bool} (state : Option Control) (pos : ℕ)
    (hp : pos ≤ input.length) (word : List Bool) (head : ℕ) (out : List Bool) :
    Cfg 2 Bool Control input :=
  ⟨state, ⟨pos + 1, by omega⟩, ![tapeOfList word, fun _ => none], ![(head : ℤ), 0], out⟩

private theorem tag_step {input : List Bool} (pre rest word : List Bool) (bit : Bool)
    (hi : input = pre ++ bit :: rest) :
    update.step (updateConfig (input := input) (some .tag) pre.length (by rw [hi]; simp)
      word word.length word) =
      updateConfig (input := input) (some .value) pre.length (by rw [hi]; simp)
        (word ++ [true]) (word.length + 1) (word ++ [true]) := by
  rw [step_of_state rfl,
    inputSymbolInner pre.length (by simp [updateConfig]; omega) (by rw [hi]; simp)]
  have hb : input[pre.length]'(by rw [hi]; simp) = bit := by simp [hi]
  simp only [update, tr_ofTr, hb]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [updateConfig, Action.apply]
  · simp [updateConfig, Action.apply]
  · funext i; fin_cases i <;> simp [updateConfig, Action.apply, tapeOfList_append_single]
  · funext i; fin_cases i <;> simp [updateConfig, Action.apply]
  · simp [updateConfig, Action.apply]

private theorem value_step {input : List Bool} (pre rest word : List Bool) (bit : Bool)
    (hi : input = pre ++ bit :: rest) :
    update.step (updateConfig (input := input) (some .value) pre.length (by rw [hi]; simp)
      word word.length word) =
      updateConfig (input := input) (some .tag) (pre.length + 1) (by rw [hi]; simp)
        (word ++ [bit]) (word.length + 1) (word ++ [bit]) := by
  rw [step_of_state rfl,
    inputSymbolInner pre.length (by simp [updateConfig]; omega) (by rw [hi]; simp)]
  have hb : input[pre.length]'(by rw [hi]; simp) = bit := by simp [hi]
  have hm : moveInputPos (⟨pre.length + 1, by rw [hi]; simp⟩ :
      Fin (input.length + 2)) 1 = ⟨pre.length + 1 + 1, by rw [hi]; simp⟩ :=
    moveInputPos_pos_of_ne_right _ (by change pre.length + 1 ≠ input.length + 1; rw [hi]; simp)
  simp only [update, tr_ofTr, hb]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [updateConfig, Action.apply]
  · exact hm
  · funext i; fin_cases i <;> simp [updateConfig, Action.apply, tapeOfList_append_single]
  · funext i; fin_cases i <;> simp [updateConfig, Action.apply]
  · simp [updateConfig, Action.apply]

private theorem tag_end (input word : List Bool) :
    update.step (updateConfig (input := input) (some .tag) input.length le_rfl
      word word.length word) =
      updateConfig (input := input) none input.length le_rfl
      (word ++ [false]) (word.length + 1) (word ++ [false]) := by
  rw [step_of_state rfl, inputSymbol_eq_none_of_boundary (Or.inr rfl)]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [update, updateConfig, Action.apply]
  · simp [update, updateConfig, Action.apply]
  · funext i; fin_cases i <;> simp [update, updateConfig, Action.apply, tapeOfList_append_single]
  · funext i; fin_cases i <;> simp [update, updateConfig, Action.apply]
  · simp [update, updateConfig, Action.apply]

private theorem run_next {input : List Bool} (cfg : Cfg 2 Bool Control input) (t : ℕ) :
    update.runFrom cfg (t + 1) = update.runFrom (update.step cfg) t := by
  rw [show t + 1 = 1 + t by omega, MultiTapeTM.runFrom_add]
  rfl

private theorem append_run (input rest : List Bool) : ∀ pre word (hi : input = pre ++ rest),
    update.runFrom (updateConfig (input := input) (some .tag) pre.length (by rw [hi]; simp)
      word word.length word)
        (2 * rest.length + 1) =
      updateConfig (input := input) none input.length le_rfl (word ++ frame rest)
      (word ++ frame rest).length
        (word ++ frame rest) := by
  induction rest with
  | nil =>
    intro pre word hi
    have he : pre = input := by simpa using hi.symm
    subst pre
    simpa [frame, run_next, MultiTapeTM.runFrom] using tag_end input word
  | cons bit rest ih =>
    intro pre word hi
    rw [show 2 * (bit :: rest).length + 1 = (2 * rest.length + 1) + 1 + 1 by simp; omega,
      run_next, tag_step pre rest word bit hi,
      show word.length + 1 = (word ++ [true]).length by simp,
      run_next, value_step pre rest (word ++ [true]) bit hi]
    have h := ih (pre ++ [bit]) ((word ++ [true]) ++ [bit]) (by simpa using hi)
    simpa [frame, List.append_assoc] using h

private theorem scan_run (input rest : List Bool) : ∀ pre,
    update.runFrom (updateConfig (input := input) (some .scan) 0 (by omega)
        (pre ++ rest) pre.length pre) (rest.length + 1) =
      updateConfig (input := input) (some .tag) 0 (by omega) (pre ++ rest)
      (pre ++ rest).length (pre ++ rest) := by
  induction rest with
  | nil =>
    intro pre
    change update.step (updateConfig (input := input) (some .scan) 0 (by omega)
      (pre ++ []) pre.length pre) = _
    simp only [List.append_nil]
    rw [step_of_state rfl]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
    · simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
    · funext i; fin_cases i <;> simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
    · funext i; fin_cases i <;> simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
    · simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
  | cons bit rest ih =>
    intro pre
    rw [show (bit :: rest).length + 1 = (rest.length + 1) + 1 by simp,
      run_next]
    have hs : update.step (updateConfig (input := input) (some .scan) 0 (by omega)
        (pre ++ bit :: rest) pre.length pre) =
      updateConfig (input := input) (some .scan) 0 (by omega) ((pre ++ [bit]) ++ rest)
        (pre ++ [bit]).length (pre ++ [bit]) := by
      rw [step_of_state rfl]
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_
      · simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
      · simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
      · funext i; fin_cases i <;>
          simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols, List.append_assoc]
      · funext i; fin_cases i <;> simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
      · simp [update, updateConfig, Action.apply, Cfg.workTapeSymbols]
    rw [hs, ih]
    simp [List.append_assoc]

/-- Actual finite execution of the uniform runtime-word update, including empty
context and empty reply. The clock depends on the received reply, not only on the
original request. The context is real tape data, not a code-generation argument. -/
theorem update_run (input context : List Bool) :
    update.runFrom (updateConfig (input := input) (some .scan) 0 (by omega) context 0 [])
        (context.length + 2 * input.length + 2) =
      updateConfig (input := input) none input.length le_rfl (context ++ frame input)
      (context ++ frame input).length
        (context ++ frame input) := by
  have hs := scan_run input context []
  have ha := append_run input input [] context (by simp)
  rw [show context.length + 2 * input.length + 2 =
    (context.length + 1) + (2 * input.length + 1) by omega, MultiTapeTM.runFrom_add]
  have hs' : update.runFrom (updateConfig (input := input) (some .scan) 0 (by omega)
      context 0 []) (context.length + 1) =
      updateConfig (input := input) (some .tag) 0 (by omega) context context.length context :=
    by simpa using hs
  rw [hs']
  exact ha

/-- Update the actual context tape, prepare it, and submit/read the second query.
The code is independent of both context and response words. -/
def continuation : MultiTapePTM 2 Bool
    (Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ NativeQueryAll.Control) Unit :=
  (MultiTapePTM.ofDeterministic update).seq
    ((NativeResponseExecution.prepare 0).seq (NativeQueryAll.machine () 0).inputFromTape)

/-- Enter the update with a runtime context and the actual previously received channel. -/
@[expose] def start {P : Type} (input context : List Bool) (channel : Channel Bool)
    (memory : Memory Unit P) : World 2 Control Unit P input :=
  ⟨⟨updateConfig (some .scan) 0 (by omega) context 0 [], fun _ => channel⟩, memory⟩

private def updated {P : Type} (input context : List Bool) (channel : Channel Bool)
    (memory : Memory Unit P) : World 2 Control Unit P input :=
  ⟨⟨updateConfig none input.length le_rfl (context ++ frame input)
    (context ++ frame input).length (context ++ frame input), fun _ => channel⟩, memory⟩

private theorem update_terminal {P : Type} (env : Environment Unit P)
    (input context : List Bool) (channel : Channel Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (MultiTapePTM.ofDeterministic update) env
      (start input context channel memory) =
        PMF.pure (some (updated input context channel memory)) := by
  apply NativeResponseExecution.terminal_of_clock _ env _
    (updated input context channel memory) (context.length + 2 * input.length + 2) ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic update).runOracleConfigFrom
      (context.length + 2 * input.length + 2) (start input context channel memory).config)).run
      memory).map (fun p => (⟨p.1, p.2⟩ : World 2 Control Unit P input)) = _
  rw [← OracleComp.runWith, ← ProbOracleComp.runWith,
    MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  change PMF.pure (⟨⟨update.runFrom (updateConfig (input := input) (some .scan)
    0 (by omega) context 0 []) (context.length + 2 * input.length + 2), fun _ => channel⟩,
      memory⟩ : World 2 Control Unit P input) = _
  rw [update_run]
  rfl

/-- The virtual source query starts with the updated context also available for readback. -/
@[expose] def queryStart {P : Type} (word : List Bool) (channel : Channel Bool)
    (memory : Memory Unit P) : World 0 NativeQueryAll.Control Unit P word :=
  ⟨{ (NativeQueryAll.machine () 0).initialConfig word with
    tapes := { ((NativeQueryAll.machine () 0).initialConfig word).tapes with output := word }
    channels := fun _ => channel }, memory⟩

private def ready {P : Type} (input context : List Bool) (channel : Channel Bool)
    (memory : Memory Unit P) : World 2 NativeQueryAll.Control Unit P input :=
  NativeResponseExecution.inputWorld (queryStart (context ++ frame input) channel memory)
    input ⟨input.length + 1, by omega⟩

private def prepared {P : Type} (input context : List Bool) (channel : Channel Bool)
    (memory : Memory Unit P) :
    World 2 (MarkWorkState ⊕ RewindWorkState) Unit P input :=
  ⟨{ (ready input context channel memory).config with
    tapes := { (ready input context channel memory).config.tapes with state := none } }, memory⟩

private theorem prepare_run {P : Type} (input context : List Bool) (channel : Channel Bool)
    (memory : Memory Unit P) :
    (prepareInput 0 true).runFrom
      (NativeSequential.resume (NativeResponseExecution.prepare 0)
        (updated input context channel memory)).config.tapes
      ((context ++ frame input).length + 4) =
        (prepared input context channel memory).config.tapes := by
  rw [show (NativeSequential.resume (NativeResponseExecution.prepare 0)
      (updated input context channel memory)).config.tapes =
      (updated input context channel memory).config.tapes.withState
        (some (prepareInput 0 true).q₀) from rfl,
    runFrom_prepareInput true _ (context ++ frame input) rfl rfl rfl]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i; fin_cases i <;>
      simp [updated, updateConfig, prepared, ready, NativeResponseExecution.inputWorld,
        queryStart, InputFromTape.config, inCfg, Fin.append_left_nil _ _ rfl,
        MultiTapeMachine.initialConfig, Cfg.init]
  · funext i; fin_cases i <;>
      simp [updated, updateConfig, prepared, ready, NativeResponseExecution.inputWorld,
        queryStart, InputFromTape.config, inCfg, Fin.append_left_nil _ _ rfl,
        MultiTapeMachine.initialConfig, Cfg.init]

private theorem prepare_terminal {P : Type} (env : Environment Unit P)
    (input context : List Bool) (channel : Channel Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (NativeResponseExecution.prepare 0) env
      (NativeSequential.resume (NativeResponseExecution.prepare 0)
        (updated input context channel memory)) =
        PMF.pure (some (prepared input context channel memory)) := by
  apply NativeResponseExecution.terminal_of_clock _ env _
    (prepared input context channel memory) ((context ++ frame input).length + 4) ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic (prepareInput 0 true)).runOracleConfigFrom
      ((context ++ frame input).length + 4)
      (NativeSequential.resume (NativeResponseExecution.prepare 0)
        (updated input context channel memory)).config)).run memory).map
      (fun p => (⟨p.1, p.2⟩ : World 2 (MarkWorkState ⊕ RewindWorkState) Unit P input)) = _
  rw [← OracleComp.runWith, ← ProbOracleComp.runWith,
    MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map,
    prepare_run]
  rfl

/-- The actual continuation result, retaining its context tape, received channel
and resource-bearing oracle memory rather than just an output marginal. -/
@[expose] def finish {P : Type} (input context : List Bool) (channel : Channel Bool)
    (memory : Memory Unit P) (reply : Reply) (next : P) :
    World 2 (Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ NativeQueryAll.Control)
      Unit P input :=
  NativeSequential.right (First := Control)
    (NativeSequential.right (First := MarkWorkState ⊕ RewindWorkState)
      (NativeResponseExecution.inputWorld
        (NativeQueryAll.finishFrom () (queryStart (context ++ frame input) channel memory)
          reply next) input ⟨input.length + 1, by omega⟩))

/-- Exact unbounded joint law of the concrete runtime update/second-query program.
The only entry condition is the real empty query buffer. No representation, response
length, successful output, scheduler-existence or independent-response premise occurs. -/
theorem terminal_continuation {P : Type} (env : Environment Unit P)
    (input context : List Bool) (channel : Channel Bool) (memory : Memory Unit P)
    (hb : channel.queryBuffer = []) :
    NativeUnboundedExecution.terminal continuation env
      (NativeSequential.left
        ((NativeResponseExecution.prepare 0).seq (NativeQueryAll.machine () 0).inputFromTape)
        (start input context channel memory)) =
      (env ((), context ++ frame input) memory).map fun (reply, next) =>
        some (finish input context channel memory reply next) := by
  rw [continuation, NativeSequential.terminal_seq, update_terminal, PMF.pure_bind]
  have hr : NativeSequential.resume
      ((NativeResponseExecution.prepare 0).seq (NativeQueryAll.machine () 0).inputFromTape)
      (updated input context channel memory) =
      NativeSequential.left (NativeQueryAll.machine () 0).inputFromTape
        (NativeSequential.resume (NativeResponseExecution.prepare 0)
          (updated input context channel memory)) := rfl
  change (NativeUnboundedExecution.terminal
    ((NativeResponseExecution.prepare 0).seq (NativeQueryAll.machine () 0).inputFromTape) env
    (NativeSequential.resume
      ((NativeResponseExecution.prepare 0).seq (NativeQueryAll.machine () 0).inputFromTape)
      (updated input context channel memory))).map _ = _
  rw [hr, NativeSequential.terminal_seq, prepare_terminal, PMF.pure_bind]
  have hp : NativeSequential.resume (NativeQueryAll.machine () 0).inputFromTape
      (prepared input context channel memory) = ready input context channel memory := rfl
  change ((NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0).inputFromTape env
    (NativeSequential.resume (NativeQueryAll.machine () 0).inputFromTape
      (prepared input context channel memory))).map _).map _ = _
  rw [hp, ready, NativeResponseExecution.terminal_inputWorld,
    NativeQueryAll.terminal_from () env _ rfl rfl hb, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  rfl

/-- One actual native two-query program, not a host-side composition of compiled contexts. -/
def program := NativeResponseExecution.machine continuation

/-- Load the arbitrary runtime context on ordinary tape zero. The inner flag,
outer response buffer and outer flag begin blank. -/
@[expose] def entry {P : Type} (request context : List Bool) (memory : Memory Unit P) :=
  NativeResponseExecution.startFrom continuation request memory
    (NativeResponseExecution.Workspace.words ![context, []])

private theorem handoff {P : Type} (request context : List Bool) (memory : Memory Unit P)
    (reply : Reply) (next : P) :
    NativeResponseExecution.localStartFrom continuation request memory reply next
        (NativeResponseExecution.Workspace.words ![context, []]) =
      NativeSequential.left
        ((NativeResponseExecution.prepare 0).seq (NativeQueryAll.machine () 0).inputFromTape)
        (start reply.word context ⟨[], reply.word, reply.word.length⟩
          (memory.record ((), request) reply next)) := by
  apply congrArg (fun cfg =>
    (⟨cfg, memory.record ((), request) reply next⟩ : World 2 _ Unit P reply.word))
  apply Config.ext
  · refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; fin_cases i
      · rfl
      · exact tapeOfList_nil
    · funext i; fin_cases i <;> rfl
  · funext op; cases op
    simp [NativeQueryAll.finish,
      NativeQueryAll.finishFrom, NativeQueryAll.start, start, Sequential.left]

/-- Exact full native two-response law. The same code handles every initial context,
request and response length, with the second request formed on tape from the actual
first reply and the retained original context before the second sample is drawn. -/
theorem terminal_program {P : Type} (env : Environment Unit P)
    (request context : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal program env (entry request context memory) =
      (env ((), request) memory).bind fun (first, next) =>
        let recorded := memory.record ((), request) first next
        (env ((), context ++ frame first.word) recorded).map fun (second, last) =>
          some (NativeResponseExecution.resultWorld request
            (finish first.word context ⟨[], first.word, first.word.length⟩
              recorded second last)) := by
  rw [program, entry, NativeResponseExecution.terminal_from]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨first, next⟩ := pair
  change (NativeUnboundedExecution.terminal continuation env
    (NativeResponseExecution.localStartFrom continuation request memory first next
      (NativeResponseExecution.Workspace.words ![context, []]))).map _ = _
  rw [handoff, terminal_continuation _ _ _ _ _ rfl, PMF.map_comp]
  rfl

/-- Readback of one complete response-dependent execution, including actual context
storage and both resource-bearing oracle events. -/
structure Observation (P : Type) where
  /-- The context prefix followed by the complete second response. -/
  output : List Bool
  /-- The updated context remains on a genuine ordinary work tape. -/
  contextTape : ℤ → Option Bool
  /-- Its actual head position after reading the second request. -/
  contextHead : ℤ
  /-- The inner virtual-input flag, read directly for reuse checks. -/
  flagTape : ℤ → Option Bool
  /-- The same jointly updated private state and resource/event ledger. -/
  memory : Memory Unit P

/-- Read ordinary tape zero directly; there is no externally decoded context supplied. -/
@[expose] def observe {S P : Type} {input : List Bool}
    (world : World 4 S Unit P input) : Observation P :=
  ⟨world.config.tapes.output, world.config.tapes.workTapes 0,
    world.config.tapes.workTapePos 0, world.config.tapes.workTapes 1, world.memory⟩

private theorem observe_finish {P : Type} (request context : List Bool)
    (memory : Memory Unit P) (first : Reply) (next : P) (second : Reply) (last : P) :
    observe (NativeResponseExecution.resultWorld request
      (finish first.word context ⟨[], first.word, first.word.length⟩
        (memory.record ((), request) first next) second last)) =
      (⟨(context ++ frame first.word) ++ second.word,
        tapeOfList (context ++ frame first.word), (context ++ frame first.word).length,
        Function.update (fun _ => none) (-1) (some true),
        (memory.record ((), request) first next).record
          ((), context ++ frame first.word) second last⟩ : Observation P) := by
  simp [observe, NativeResponseExecution.resultWorld, finish, NativeSequential.right,
    Sequential.right, NativeResponseExecution.inputWorld, InputFromTape.config,
    NativeQueryAll.finishFrom, queryStart, inCfg,
    MultiTapeMachine.initialConfig, Cfg.init, Fin.append, Fin.addCases, Cfg.mapState]

/-- Joint context/output/memory readback of the actual two-query native program. -/
theorem program_observation {P : Type} (env : Environment Unit P)
    (request context : List Bool) (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal program env (entry request context memory)).map
        (Option.map observe) =
      (env ((), request) memory).bind fun (first, next) =>
        let recorded := memory.record ((), request) first next
        (env ((), context ++ frame first.word) recorded).map fun (second, last) =>
          some (⟨(context ++ frame first.word) ++ second.word,
            tapeOfList (context ++ frame first.word), (context ++ frame first.word).length,
            Function.update (fun _ => none) (-1) (some true),
            recorded.record ((), context ++ frame first.word) second last⟩ : Observation P) := by
  rw [terminal_program, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨first, next⟩ := pair
  rw [PMF.map_comp]
  congr 1
  funext pair
  obtain ⟨second, last⟩ := pair
  exact congrArg some (observe_finish request context memory first next second last)


/-- Rewind the virtual context input, then erase its boundary marker. Both heads
return to zero, so the stored context can be used by another native phase. -/
@[expose] def cleanup : MultiTapePTM 2 Bool (RewindState ⊕ MarkWorkState) Unit :=
  (MultiTapePTM.ofDeterministic (rewindInput Bool)).inputFromTape.seq
    (MultiTapePTM.ofDeterministic
      ((markWork Bool none).extendTapes (tapeEmb (1 : Fin 2))))

private def rewound {P : Type} (word : List Bool) (channel : Channel Bool)
    (memory : Memory Unit P) (reply : Reply) (next : P) :
    World 0 RewindState Unit P word :=
  let final := NativeQueryAll.finishFrom () (queryStart word channel memory) reply next
  ⟨{ final.config with tapes := { final.config.tapes with state := none, inputPos := 1 } },
    final.memory⟩

private theorem rewind_terminal {P : Type} (env : Environment Unit P)
    (word : List Bool) (channel : Channel Bool) (memory : Memory Unit P)
    (reply : Reply) (next : P) :
    NativeUnboundedExecution.terminal (MultiTapePTM.ofDeterministic (rewindInput Bool)) env
      (NativeSequential.resume (MultiTapePTM.ofDeterministic (rewindInput Bool))
        (NativeQueryAll.finishFrom () (queryStart word channel memory) reply next)) =
      PMF.pure (some (rewound word channel memory reply next)) := by
  apply NativeResponseExecution.terminal_of_clock _ env _
    (rewound word channel memory reply next) (word.length + 2) ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic (rewindInput Bool)).runOracleConfigFrom
      (word.length + 2) (NativeSequential.resume
        (MultiTapePTM.ofDeterministic (rewindInput Bool))
        (NativeQueryAll.finishFrom () (queryStart word channel memory) reply next)).config)).run
      (memory.record ((), word) reply next)).map
      (fun p => (⟨p.1, p.2⟩ : World 0 RewindState Unit P word)) = _
  rw [← OracleComp.runWith, ← ProbOracleComp.runWith,
    MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  have hr := runFrom_rewindInput (Symbol := Bool)
    (input := word) (⟨word.length + 1, by omega⟩ : Fin (word.length + 2))
    (fun _ _ => none) (fun _ => 0) (word ++ reply.word)
  change PMF.pure (⟨_, _⟩ : World 0 RewindState Unit P word) = _
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory.record ((), word) reply next⟩ :
    World 0 RewindState Unit P word))
  apply Config.ext
  · simpa [NativeSequential.resume, Sequential.start, NativeQueryAll.finishFrom,
      queryStart, MultiTapeMachine.initialConfig, Cfg.init, rewound,
      Cfg.withState, MultiTapePTM.ofDeterministic] using hr
  · rfl

/-- Final restored ordinary storage: the updated context, both heads at zero and
a blank reusable flag tape. No external event or invoice is discarded. -/
@[expose] def restored {P : Type} (input context : List Bool) (memory : Memory Unit P)
    (reply : Reply) (next : P) : World 2 MarkWorkState Unit P input :=
  ⟨⟨⟨none, ⟨input.length + 1, by omega⟩,
    ![tapeOfList (context ++ frame input), fun _ => none], fun _ => 0,
    (context ++ frame input) ++ reply.word⟩,
    fun _ => ⟨[], reply.word, reply.word.length⟩⟩,
    memory.record ((), context ++ frame input) reply next⟩

private theorem erase_terminal {P : Type} (env : Environment Unit P)
    (input context : List Bool) (channel : Channel Bool) (memory : Memory Unit P)
    (reply : Reply) (next : P) :
    NativeUnboundedExecution.terminal
      (MultiTapePTM.ofDeterministic
        ((markWork Bool none).extendTapes (tapeEmb (1 : Fin 2)))) env
      (NativeSequential.resume
        (MultiTapePTM.ofDeterministic
          ((markWork Bool none).extendTapes (tapeEmb (1 : Fin 2))))
        (NativeResponseExecution.inputWorld
          (rewound (context ++ frame input) channel memory reply next)
          input ⟨input.length + 1, by omega⟩)) =
        PMF.pure (some (restored input context memory reply next)) := by
  apply NativeResponseExecution.terminal_of_clock _ env _
    (restored input context memory reply next) 2 ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic
      ((markWork Bool none).extendTapes (tapeEmb (1 : Fin 2)))).runOracleConfigFrom 2
      (NativeSequential.resume
        (MultiTapePTM.ofDeterministic
          ((markWork Bool none).extendTapes (tapeEmb (1 : Fin 2))))
        (NativeResponseExecution.inputWorld
          (rewound (context ++ frame input) channel memory reply next)
          input ⟨input.length + 1, by omega⟩)).config)).run
      (memory.record ((), context ++ frame input) reply next)).map
      (fun p => (⟨p.1, p.2⟩ : World 2 MarkWorkState Unit P input)) = _
  rw [← OracleComp.runWith, ← ProbOracleComp.runWith,
    MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory.record ((), context ++ frame input) reply next⟩ :
    World 2 MarkWorkState Unit P input))
  apply Config.ext
  · rw [runFrom_tapeEmb]
    simp only [oneTapeCfg, NativeSequential.resume, Sequential.start,
      MultiTapePTM.ofDeterministic, extendTapes_q₀]
    have hc : (NativeResponseExecution.inputWorld
        (rewound (context ++ frame input) channel memory reply next) input
        ⟨input.length + 1, by omega⟩).config.tapes =
      ⟨none, ⟨input.length + 1, by omega⟩,
        ![tapeOfList (context ++ frame input),
          Function.update (fun _ => none) (-1) (some true)], fun _ => 0,
        (context ++ frame input) ++ reply.word⟩ := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i; fin_cases i <;>
          simp [NativeResponseExecution.inputWorld, rewound, NativeQueryAll.finishFrom,
            queryStart, InputFromTape.config, inCfg, Fin.append_left_nil _ _ rfl]
      · funext i; fin_cases i <;>
          simp [NativeResponseExecution.inputWorld, rewound, NativeQueryAll.finishFrom,
            queryStart, InputFromTape.config, inCfg, Fin.append_left_nil _ _ rfl]
    rw [hc]
    change embed (tapeEmb (1 : Fin 2))
      ((markWork Bool none).runFrom
        ⟨some (markWork Bool none).q₀, ⟨input.length + 1, by omega⟩,
          fun _ => Function.update (fun _ => none) (-1) (some true), fun _ => 0,
          (context ++ frame input) ++ reply.word⟩ 2)
      ![tapeOfList (context ++ frame input), Function.update (fun _ => none) (-1) (some true)]
      (fun _ => 0) = _
    rw [runFrom_markWork]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; fin_cases i <;> simp [embed_tapeEmb]
    · funext i; fin_cases i <;> simp [embed_tapeEmb]
  · funext op; cases op
    simp [NativeSequential.resume, Sequential.start, NativeResponseExecution.inputWorld,
      rewound, NativeQueryAll.finishFrom, InputFromTape.config]

/-- Runtime update and the second query, with actual context/flag restoration. -/
def restoring := continuation.seq cleanup

private theorem cleanup_terminal {P : Type} (env : Environment Unit P)
    (input context : List Bool) (channel : Channel Bool) (memory : Memory Unit P)
    (reply : Reply) (next : P) :
    NativeUnboundedExecution.terminal cleanup env
      (NativeSequential.resume cleanup (finish input context channel memory reply next)) =
      PMF.pure (some (NativeSequential.right (First := RewindState)
        (restored input context memory reply next))) := by
  have he : NativeSequential.resume cleanup (finish input context channel memory reply next) =
      NativeSequential.left
        (MultiTapePTM.ofDeterministic
          ((markWork Bool none).extendTapes (tapeEmb (1 : Fin 2))))
        (NativeResponseExecution.inputWorld
          (NativeSequential.resume (MultiTapePTM.ofDeterministic (rewindInput Bool))
            (NativeQueryAll.finishFrom ()
              (queryStart (context ++ frame input) channel memory) reply next))
          input ⟨input.length + 1, by omega⟩) := rfl
  rw [he, cleanup, NativeSequential.terminal_seq,
    NativeResponseExecution.terminal_inputWorld, rewind_terminal, PMF.pure_map,
    PMF.pure_bind]
  change (NativeUnboundedExecution.terminal _ env _).map _ = _
  rw [erase_terminal, PMF.pure_map]
  rfl

/-- Runtime context update and its query followed by native rewind/flag erasure.
No host transition or separately compiled context continuation performs the restart. -/
theorem terminal_restoring {P : Type} (env : Environment Unit P)
    (input context : List Bool) (channel : Channel Bool) (memory : Memory Unit P)
    (hb : channel.queryBuffer = []) :
    NativeUnboundedExecution.terminal restoring env
      (NativeSequential.left cleanup
        (NativeSequential.left
          ((NativeResponseExecution.prepare 0).seq (NativeQueryAll.machine () 0).inputFromTape)
          (start input context channel memory))) =
      (env ((), context ++ frame input) memory).map fun (reply, next) =>
        some (NativeSequential.right
          (First := Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ NativeQueryAll.Control)
          (NativeSequential.right (First := RewindState)
            (restored input context memory reply next))) := by
  rw [restoring, NativeSequential.terminal_seq, terminal_continuation _ _ _ _ _ hb,
    PMF.bind_map]
  conv_rhs => rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨reply, next⟩ := pair
  change (NativeUnboundedExecution.terminal cleanup env
    (NativeSequential.resume cleanup (finish input context channel memory reply next))).map _ = _
  rw [cleanup_terminal, PMF.pure_map]
  rfl

/-- Full first query, context transport, runtime update, second query and cleanup. -/
def restoringProgram := NativeResponseExecution.machine restoring

/-- The only supplied state is the actual initial runtime word and oracle memory;
all response buffers and flags start blank. -/
@[expose] def restoringEntry {P : Type} (request context : List Bool)
    (memory : Memory Unit P) :=
  NativeResponseExecution.startFrom restoring request memory
    (NativeResponseExecution.Workspace.words ![context, []])

/-- Canonical storage produced by the retained-context entry, stated against the
actual program's initial control for consumers that prepend native input loading. -/
theorem restoringEntry_tapes {P : Type} (input context : List Bool)
    (memory : Memory Unit P) :
    (restoringEntry input context memory).config.tapes =
      wordsCfg input (some restoringProgram.initial)
        (Function.update (fun _ => []) 0 context) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i; fin_cases i <;>
      simp [restoringEntry, NativeResponseExecution.startFrom,
        NativeResponseExecution.Workspace.words, wordsCfg, Fin.append, Fin.addCases]
  · funext i; fin_cases i <;> rfl

/-- Whole stopped law of the complete concrete two-response/cleanup native program. -/
theorem terminal_restoringProgram {P : Type} (env : Environment Unit P)
    (request context : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal restoringProgram env
        (restoringEntry request context memory) =
      (env ((), request) memory).bind fun (first, next) =>
        let recorded := memory.record ((), request) first next
        (env ((), context ++ frame first.word) recorded).map fun (second, last) =>
          some (NativeResponseExecution.resultWorld request
            (NativeSequential.right
              (First := Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ NativeQueryAll.Control)
              (NativeSequential.right (First := RewindState)
                (restored first.word context recorded second last)))) := by
  rw [restoringProgram, restoringEntry, NativeResponseExecution.terminal_from]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨first, next⟩ := pair
  have hh : NativeResponseExecution.localStartFrom restoring request memory first next
      (NativeResponseExecution.Workspace.words ![context, []]) =
      NativeSequential.left cleanup
        (NativeResponseExecution.localStartFrom continuation request memory first next
          (NativeResponseExecution.Workspace.words ![context, []])) := rfl
  change (NativeUnboundedExecution.terminal restoring env
    (NativeResponseExecution.localStartFrom restoring request memory first next
      (NativeResponseExecution.Workspace.words ![context, []]))).map _ = _
  rw [hh, handoff, terminal_restoring _ _ _ _ _ rfl, PMF.map_comp]
  rfl

private theorem observe_restored {P : Type} (request context : List Bool)
    (memory : Memory Unit P) (first : Reply) (next : P) (second : Reply) (last : P) :
    observe (NativeResponseExecution.resultWorld request
      (NativeSequential.right
        (First := Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ NativeQueryAll.Control)
        (NativeSequential.right (First := RewindState)
          (restored first.word context (memory.record ((), request) first next) second last)))) =
      (⟨(context ++ frame first.word) ++ second.word,
        tapeOfList (context ++ frame first.word), 0, fun _ => none,
        (memory.record ((), request) first next).record
          ((), context ++ frame first.word) second last⟩ : Observation P) := by
  simp [observe, NativeResponseExecution.resultWorld, NativeSequential.right, Sequential.right,
    InputFromTape.config, inCfg, restored, Fin.append, Fin.addCases, Cfg.mapState]

/-- Actual runtime context readback with a blank reusable inner flag and both inner
heads returned to zero. The first-response buffer and outer flag are still retained;
this milestone does not assert a complete repeated selector restart. -/
theorem restoring_program_observation {P : Type} (env : Environment Unit P)
    (request context : List Bool) (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal restoringProgram env
      (restoringEntry request context memory)).map (Option.map observe) =
      (env ((), request) memory).bind fun (first, next) =>
        let recorded := memory.record ((), request) first next
        (env ((), context ++ frame first.word) recorded).map fun (second, last) =>
          some (⟨(context ++ frame first.word) ++ second.word,
            tapeOfList (context ++ frame first.word), 0, fun _ => none,
            recorded.record ((), context ++ frame first.word) second last⟩ : Observation P) := by
  rw [terminal_restoringProgram, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨first, next⟩ := pair
  rw [PMF.map_comp]
  apply congrArg (fun f : Reply × P → Option (Observation P) =>
    (env ((), context ++ frame first.word) (memory.record ((), request) first next)).map f)
  funext pair
  obtain ⟨second, last⟩ := pair
  exact congrArg some (observe_restored request context memory first next second last)

end Cslib.Probability.NativeRuntimeContext
