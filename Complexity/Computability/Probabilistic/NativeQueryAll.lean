/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeOutputBuffer
public import Complexity.Computability.Probabilistic.NativeSequential
public import Complexity.Probability.PMF.StoppedProcess.Boundary
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import Mathlib.Tactic

/-!
# Actual native reading of an entire unbounded oracle reply

The finite-control binary machine writes its input request, submits it once, and
copies the actual answer until its blank boundary. Work tapes and other channels
are untouched. The reader has no input-only instruction clock: its local running
time depends on the actual finite response length. The exact unbounded terminal
law preserves the full oracle memory, correlations, invoices and external duration.

This is the full-reply primitive required by the source selection-only PTMs of
[Wang2027], model PDF pp. 4--6 and Theorem 5 p. 12. It does not certify the report
parser or compile the complete adaptive retention program.

## Main definitions

* `machine`: finite-control full-reply reader.
* `start`, `finish`: its actual initial and final native worlds.

## Main results

* `terminal_query`: exact native full-reply/shared-memory law, without a response bound.
* `clocked_ne_query`: a long reply obstructs full-output query realization at a fixed clock.
-/

public section
namespace Cslib.Probability.NativeQueryAll
open Turing Turing.MultiTapeMachine NativeOpenExecution

/-- The request scan and the full answer scan. -/
inductive Control where
  | write
  | copy
  deriving DecidableEq

instance : Finite Control :=
  Finite.of_injective (fun | .write => false | .copy => true)
    (fun a b h => by cases a <;> cases b <;> simp_all)

/-- Write the input request once, query once, and copy until the actual blank
answer cell. Local fair coins are ignored; no response prefix is imposed. -/
@[expose] def machine {Operation : Type} [DecidableEq Operation] (op : Operation) (k : ℕ) :
    MultiTapePTM k Bool Control Operation where
  initial := .write
  tr state symbol _ answer _ := match state with
    | .write => match symbol with
      | some bit => .step
        { inputTape := 1, workTapes := fun _ => (none, 0), output := none, state := some .write }
        (Function.update (fun _ => none) op (some bit)) (fun _ => 0)
      | none => .query op .copy
    | .copy => match answer op with
      | some bit => .step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := some bit, state := some .copy }
        (fun _ => none) (Function.update (fun _ => 0) op 1)
      | none => .step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
        (fun _ => none) (fun _ => 0)

/-- Start the real native reader with the request on its input tape, preserving
arbitrary already accumulated oracle state and resources. -/
@[expose] def start {Operation Private : Type} [DecidableEq Operation]
    (op : Operation) (k : ℕ) (request : List Bool) (memory : Memory Operation Private) :
    World k Control Operation Private request :=
  ⟨(machine op k).initialConfig request, memory⟩

noncomputable section
variable {Operation Private : Type} [DecidableEq Operation] {k : ℕ} {input : List Bool}
variable (op : Operation) (env : Environment Operation Private)

private def point (base : World k Control Operation Private input)
    (control : Option Control) (index : ℕ) (hi : index ≤ input.length)
    (out : List Bool) (channels : Operation → Channel Bool) :
    World k Control Operation Private input :=
  ⟨{ base.config with
      tapes := { base.config.tapes with
        state := control
        inputPos := ⟨index + 1, by omega⟩
        output := out }
      channels := channels }, base.memory⟩

private def copyPoint (base : World k Control Operation Private input)
    (answer out : List Bool) (position : ℕ) : World k Control Operation Private input :=
  point base (some .copy) input.length le_rfl out
    (Function.update base.config.channels op ⟨[], answer, position⟩)

private def donePoint (base : World k Control Operation Private input)
    (answer out : List Bool) : World k Control Operation Private input :=
  point base none input.length le_rfl out
    (Function.update base.config.channels op ⟨[], answer, answer.length⟩)

private theorem unfold_terminal (world : World k Control Operation Private input) :
    NativeUnboundedExecution.terminal (machine op k) env world =
      (step (machine op k) env world).bind
        (NativeUnboundedExecution.terminal (machine op k) env) :=
  StoppedProcess.terminal_step _ _ _ _

private theorem copy_step (base : World k Control Operation Private input)
    (pre rest out : List Bool) (bit : Bool) :
    step (machine op k) env (copyPoint op base (pre ++ bit :: rest) out pre.length) =
      PMF.pure (copyPoint op base (pre ++ bit :: rest) (out ++ [bit]) (pre.length + 1)) := by
  have hs : (copyPoint op base (pre ++ bit :: rest) out pre.length).config.answerSymbols op =
      some bit := by
    simp [copyPoint, point, Config.answerSymbols, Channel.answerSymbol]
  have hstate : (copyPoint op base (pre ++ bit :: rest) out pre.length).config.tapes.state =
      some .copy := rfl
  simp only [NativeOpenExecution.step, hstate, machine, hs]
  simp only [PMF.bind_const]
  congr 1
  congr 1
  apply Config.ext
  · ext <;> simp [copyPoint, point, Config.step, Action.apply]
  · funext other
    by_cases he : other = op
    · subst other
      simp [copyPoint, point, Config.step, Nat.cast_add]
    · simp [copyPoint, point, Config.step, he]

private theorem copy_stop (base : World k Control Operation Private input)
    (answer out : List Bool) :
    step (machine op k) env (copyPoint op base answer out answer.length) =
      PMF.pure (donePoint op base answer out) := by
  have hs : (copyPoint op base answer out answer.length).config.answerSymbols op = none := by
    simp [copyPoint, point, Config.answerSymbols, Channel.answerSymbol]
  have hstate : (copyPoint op base answer out answer.length).config.tapes.state =
      some .copy := rfl
  simp only [NativeOpenExecution.step, hstate, machine, hs]
  simp only [PMF.bind_const]
  congr 1
  congr 1
  apply Config.ext
  · ext <;> simp [copyPoint, point, Config.step, Action.apply]
  · funext other
    by_cases he : other = op
    · subst other
      simp [copyPoint, point, Config.step]
    · simp [copyPoint, point, Config.step, he]

private theorem copy_terminal (base : World k Control Operation Private input)
    (rest : List Bool) : ∀ pre out,
    NativeUnboundedExecution.terminal (machine op k) env
        (copyPoint op base (pre ++ rest) out pre.length) =
      PMF.pure (some (donePoint op base (pre ++ rest) (out ++ rest))) := by
  induction rest with
  | nil =>
    intro pre out
    rw [List.append_nil, unfold_terminal, copy_stop, PMF.pure_bind]
    simpa only [NativeUnboundedExecution.terminal, List.append_nil] using
      StoppedProcess.terminal_halted (NativeOpenExecution.step (machine op k) env)
        NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
        (donePoint op base pre out) rfl
  | cons bit rest ih =>
    intro pre out
    rw [unfold_terminal, copy_step, PMF.pure_bind]
    have he : pre ++ bit :: rest = (pre ++ [bit]) ++ rest := by simp
    rw [he]
    simpa only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] using ih (pre ++ [bit]) (out ++ [bit])

private def writePoint (base : World k Control Operation Private input) (pre : List Bool)
    (hp : pre.length ≤ input.length) : World k Control Operation Private input :=
  point base (some .write) pre.length hp base.config.tapes.output
    (Function.update base.config.channels op
      { base.config.channels op with queryBuffer := pre })

private theorem write_step (base : World k Control Operation Private input)
    (pre rest : List Bool) (bit : Bool) (h : input = pre ++ bit :: rest) :
    step (machine op k) env
        (writePoint op base pre (by rw [h]; simp)) =
      PMF.pure (writePoint op base (pre ++ [bit]) (by rw [h]; simp)) := by
  have hsym : (writePoint op base pre (by rw [h]; simp)).config.tapes.inputSymbol =
      some bit := by
    rw [inputSymbolInner pre.length (by simp [writePoint, point, Nat.add_comm]) (by rw [h]; simp)]
    simp [h]
  have hstate : (writePoint op base pre (by rw [h]; simp)).config.tapes.state =
      some .write := rfl
  simp only [NativeOpenExecution.step, hstate, machine, hsym]
  simp only [PMF.bind_const]
  congr 1
  congr 1
  apply Config.ext
  · have hp : pre.length < input.length := by rw [h]; simp
    have hm : moveInputPos (⟨pre.length + 1, by omega⟩ : Fin (input.length + 2)) 1 =
        ⟨pre.length + 1 + 1, by omega⟩ := by
      exact moveInputPos_pos_of_ne_right
        (⟨pre.length + 1, by omega⟩ : Fin (input.length + 2)) (by
          change pre.length + 1 ≠ input.length + 1
          omega)
    ext <;> simp [writePoint, point, Config.step, Action.apply, hm]
  · funext other
    by_cases he : other = op
    · subst other
      simp [writePoint, point, Config.step]
    · simp [writePoint, point, Config.step, he]

private def replyDone (base : World k Control Operation Private input)
    (reply : Reply) (privateState : Private) : World k Control Operation Private input :=
  { donePoint op base reply.word (base.config.tapes.output ++ reply.word) with
    memory := base.memory.record (op, input) reply privateState }

private theorem write_submit (base : World k Control Operation Private input) :
    step (machine op k) env (writePoint op base input le_rfl) =
      (env (op, input) base.memory).map fun (reply, privateState) =>
        copyPoint op { base with memory := base.memory.record (op, input) reply privateState }
          reply.word base.config.tapes.output 0 := by
  have hs : (writePoint op base input le_rfl).config.tapes.state = some .write := rfl
  have hsym : (writePoint op base input le_rfl).config.tapes.inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr rfl)
  simp only [NativeOpenExecution.step, hs, machine, hsym, PMF.bind_const]
  have hq : ((writePoint op base input le_rfl).config.channels op).queryBuffer = input := by
    simp [writePoint, point]
  rw [hq]
  change (env (op, input) base.memory).map _ = _
  congr 1
  funext pair
  obtain ⟨reply, privateState⟩ := pair
  congr 1
  apply Config.ext
  · rfl
  · simp [Config.receive, writePoint, point, Function.update_idem]

private theorem write_terminal (base : World k Control Operation Private input)
    (rest : List Bool) : ∀ pre (h : input = pre ++ rest),
    NativeUnboundedExecution.terminal (machine op k) env
        (writePoint op base pre (by rw [h]; simp)) =
      (env (op, input) base.memory).map fun (reply, privateState) =>
        some (replyDone op base reply privateState) := by
  induction rest with
  | nil =>
    intro pre h
    have he : pre = input := by simpa using h.symm
    subst pre
    rw [unfold_terminal, write_submit, PMF.bind_map]
    change ((env (op, input) base.memory).bind fun (reply, privateState) =>
      NativeUnboundedExecution.terminal (machine op k) env
        (copyPoint op { base with memory := base.memory.record (op, input) reply privateState }
          reply.word base.config.tapes.output 0)) = _
    have hc (reply : Reply) (privateState : Private) :
        NativeUnboundedExecution.terminal (machine op k) env
          (copyPoint op { base with memory := base.memory.record (op, input) reply privateState }
            reply.word base.config.tapes.output 0) =
        PMF.pure (some (replyDone op base reply privateState)) :=
      copy_terminal op env _ reply.word [] base.config.tapes.output
    simp only [hc]
    rfl
  | cons bit rest ih =>
    intro pre h
    rw [unfold_terminal, write_step op env base pre rest bit h, PMF.pure_bind]
    exact ih (pre ++ [bit]) (by simpa using h)

/-- Final native world of a reader phase, retaining previous work tapes, output
prefix and all other channels. Exactly one actual oracle event is appended. -/
@[expose] def finishFrom (base : World k Control Operation Private input)
    (reply : Reply) (privateState : Private) : World k Control Operation Private input :=
  ⟨{ base.config with
      tapes := { base.config.tapes with
        state := none
        inputPos := ⟨input.length + 1, by omega⟩
        output := base.config.tapes.output ++ reply.word }
      channels := Function.update base.config.channels op
        ⟨[], reply.word, reply.word.length⟩ },
    base.memory.record (op, input) reply privateState⟩

/-- The finished world from the actual initial native configuration. -/
@[expose] def finish (request : List Bool) (memory : Memory Operation Private)
    (reply : Reply) (privateState : Private) : World k Control Operation Private request :=
  finishFrom op (start op k request memory) reply privateState

/-- Full-reply reading as a phase on retained native work tapes and channels. The
only starting conditions are the real input cursor/control and an empty selected
query buffer; there is no conclusion or clock/representation contract. -/
theorem terminal_from (world : World k Control Operation Private input)
    (hs : world.config.tapes.state = some .write) (hp : world.config.tapes.inputPos.val = 1)
    (hb : (world.config.channels op).queryBuffer = []) :
    NativeUnboundedExecution.terminal (machine op k) env world =
      (env (op, input) world.memory).map fun (reply, privateState) =>
        some (finishFrom op world reply privateState) := by
  have he : writePoint op world [] (by simp) = world := by
    unfold writePoint point
    conv_rhs => rw [show world = ⟨world.config, world.memory⟩ from rfl]
    congr 1
    apply Config.ext
    · ext <;> simp [hs, hp]
    · funext other
      by_cases ho : other = op
      · subst other
        simp only [Function.update_self]
        exact Channel.ext hb.symm rfl rfl
      · simp [ho]
  calc
    _ = NativeUnboundedExecution.terminal (machine op k) env
        (writePoint op world [] (by simp)) := congrArg _ he.symm
    _ = _ := write_terminal op env world input [] (by simp)

/-- Exact actual native law of a full unbounded response. Each reply is copied to
its own actual boundary, with no common clock, finite-alphabet approximation or
termination/representation premise. The full shared oracle memory is retained. -/
theorem terminal_query (request : List Bool) (memory : Memory Operation Private) :
    NativeUnboundedExecution.terminal (machine op k) env (start op k request memory) =
      (env (op, request) memory).map fun (reply, privateState) =>
        some (finish op request memory reply privateState) := by
  exact terminal_from op env _ rfl rfl rfl

/-- The original full raw query's joint result is exactly the native reader's
readback, including its actual memory/event/resource update. -/
theorem query_readback (request : List Bool) (memory : Memory Operation Private) :
    (NativeUnboundedExecution.terminal (machine op k) env (start op k request memory)).map
        (Option.map fun w => (w.config.tapes.output, w.memory)) =
      ((handler env (op, request)).run memory).map some := by
  rw [terminal_query, PMF.map_comp]
  simp only [handler, StateT.run, PMF.map_comp]
  rfl

/-- The buffered reader's actual initial machine configuration has a blank work
buffer. No intermediate response is placed on the tape by a semantic adapter. -/
theorem buffered_start (request : List Bool) (memory : Memory Operation Private) :
    (⟨(machine op k).outputToTape.initialConfig request, memory⟩ :
      World (k + 1) Control Operation Private request) =
        NativeOutputBuffer.world (start op k request memory) := by
  rw [MultiTapeMachine.initialConfig_outputToTape]
  rfl

/-- Native full-reply reading with ordinary output redirected to a real readable
work buffer. Its length can depend arbitrarily on the sampled reply. -/
theorem terminal_buffered (request : List Bool) (memory : Memory Operation Private) :
    NativeUnboundedExecution.terminal (machine op k).outputToTape env
        (NativeOutputBuffer.world (start op k request memory)) =
      (env (op, request) memory).map fun (reply, privateState) =>
        some (NativeOutputBuffer.world (finish op request memory reply privateState)) := by
  rw [NativeOutputBuffer.terminal_buffer, terminal_query, PMF.map_comp]
  rfl

/-- Compose the actual reader with any actual native continuation on the retained
world. No uniform phase clock or assumed source-to-program representation occurs;
the continuation may issue further correlated queries or silently diverge. -/
theorem terminal_then {Next : Type} (second : MultiTapePTM k Bool Next Operation)
    (world : World k Control Operation Private input)
    (hs : world.config.tapes.state = some .write) (hp : world.config.tapes.inputPos.val = 1)
    (hb : (world.config.channels op).queryBuffer = []) :
    NativeUnboundedExecution.terminal ((machine op k).seq second) env
        (NativeSequential.left second world) =
      (env (op, input) world.memory).bind fun (reply, privateState) =>
        (NativeUnboundedExecution.terminal second env
          (NativeSequential.resume second (finishFrom op world reply privateState))).map
            (Option.map NativeSequential.right) := by
  rw [NativeSequential.terminal_seq, terminal_from op env world hs hp hb, PMF.bind_map]
  rfl

/-- A single actual native program reads the full reply into a work tape and
hands that tape, all prior channels and the shared memory to arbitrary native code.
The continuation must perform any rewind/framing/parser operations itself. -/
theorem terminal_buffered_then {Next : Type}
    (second : MultiTapePTM (k + 1) Bool Next Operation)
    (request : List Bool) (memory : Memory Operation Private) :
    NativeUnboundedExecution.terminal ((machine op k).outputToTape.seq second) env
        (NativeSequential.left second
          (NativeOutputBuffer.world (start op k request memory))) =
      (env (op, request) memory).bind fun (reply, privateState) =>
        (NativeUnboundedExecution.terminal second env (NativeSequential.resume second
          (NativeOutputBuffer.world (finish op request memory reply privateState)))).map
            (Option.map NativeSequential.right) := by
  rw [NativeSequential.terminal_seq, terminal_buffered, PMF.bind_map]
  rfl

/-- Full reply copying changes source resource meters only by the actual once-issued
reply charge/duration, including cancellations. Local scanning is not charged. -/
theorem finish_resources (world : World k Control Operation Private input)
    (reply : Reply) (privateState : Private) :
    tokenBill (finishFrom op world reply privateState).memory.events =
        reply.tokens + tokenBill world.memory.events ∧
      elapsed (finishFrom op world reply privateState).memory.events =
        reply.duration + elapsed world.memory.events := by
  simp [finishFrom, Memory.record, tokenBill, elapsed]

/-- One actually supported long response prevents *any* native machine from
emitting the full raw query result with its exact joint output/memory law within
this fixed instruction clock. The source handler records the same resources.
A reply can still be installed atomically on the answer channel; copying that
word to ordinary output is the obligation obstructed here.
It does not prohibit response-dependent unbounded native execution. -/
theorem clocked_ne_query {Controls : Type} (competitor : MultiTapePTM k Bool Controls Operation)
    (input request : List Bool) (memory : Memory Operation Private) (fuel : ℕ)
    (reply : Reply) (privateState : Private)
    (hs : (reply, privateState) ∈ (env (op, request) memory).support)
    (hl : fuel < reply.word.length) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
      (competitor.runOracle fuel input)).run memory) ≠ handler env (op, request) memory := by
  intro he
  have hm : (reply.word, memory.record (op, request) reply privateState) ∈
      (handler env (op, request) memory).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(reply, privateState), hs, rfl⟩
  rw [← he] at hm
  exact (Nat.not_lt_of_ge (competitor.length_output_runOracle_le
    (handler env) fuel input reply.word memory _ hm)) hl


end
end Cslib.Probability.NativeQueryAll
