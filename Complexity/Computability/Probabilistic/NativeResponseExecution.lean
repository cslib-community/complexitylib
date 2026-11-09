/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeQueryAll
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual response-dependent native reply processing

The real full-reply buffer is rewound and marked by native instructions, and a
native continuation reads it through the existing virtual-input compiler.
The retained-storage entry preserves arbitrary ordinary tapes and head positions;
the blank-storage entry is a specialization. There is no common reply-length clock
and no supplied prepared-input premise.
The complete adaptive scheduler/restart loop remains a separate obligation.
This is an implementation connection for [Wang2027], Theorem 5, PDF p. 12 and
Appendix A.5 p. 16; local instructions are excluded from the external deadline.

## Main definitions

* `machine`: full query, actual buffer preparation and virtual-input continuation.
* `Workspace`, `startFrom`, `localStartFrom`: actual retained ordinary storage.
* `startWithChannels`: entry on actual previous answer channels.

## Main results

* `terminal_from`: retained-storage whole-configuration law, including divergence.
* `terminal_from_channels`: the same law with a retained, empty-query-buffer channel.
* `terminal_machine`: the original blank-storage specialization.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeResponseExecution
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution
open scoped ENNReal

/-- A proved finite local execution clock yields its exact unbounded stopped law.
The clock may depend on an already received response; it is not a uniform clock
for an oracle query. -/
theorem terminal_of_clock {k : ℕ} {S P : Type} {input : List Bool}
    (m : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (start final : World k S Unit P input) (t : ℕ)
    (he : execute m env t start = PMF.pure final)
    (hh : NativeUnboundedExecution.halted final) :
    NativeUnboundedExecution.terminal m env start = PMF.pure (some final) := by
  have hm : 1 ≤ NativeUnboundedExecution.terminal m env start (some final) := by
    change 1 ≤ ⨆ fuel, StoppedProcess.stopped (NativeOpenExecution.step m env)
      NativeUnboundedExecution.halted fuel start final
    apply le_iSup_of_le t
    simp only [StoppedProcess.stopped, hh, ite_true, ← execute_eq_stateLaw, he,
      PMF.pure_apply, le_refl]
  have hp := le_antisymm (PMF.coe_le_one _ _) hm
  have hs := (PMF.apply_eq_one_iff _ _).mp hp
  ext result
  by_cases hz : result = some final
  · subst result
    simp [hp, PMF.pure_apply]
  · have hzero : NativeUnboundedExecution.terminal m env start result = 0 :=
      (PMF.apply_eq_zero_iff _ _).mpr (by rw [hs]; simpa using hz)
    simp [hzero, PMF.pure_apply, hz]

private def reserve {k : ℕ} {S P : Type} {input : List Bool}
    (w : World k S Unit P input) : World (k + 1) S Unit P input :=
  ⟨w.config.embed Fin.castSuccEmb (fun _ _ => none) (fun _ => 0), w.memory⟩

private theorem execute_reserve {k : ℕ} {S P : Type} {input : List Bool}
    (m : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (w : World k S Unit P input) (t : ℕ) :
    execute (m.extendTapes Fin.castSuccEmb) env t (reserve w) =
      (execute m env t w).map reserve := by
  simp only [execute, reserve, MultiTapePTM.runConfigFrom_embed,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
  rfl

private theorem terminal_reserve {k : ℕ} {S P : Type} {input : List Bool}
    (m : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (w : World k S Unit P input) :
    NativeUnboundedExecution.terminal (m.extendTapes Fin.castSuccEmb) env (reserve w) =
      (NativeUnboundedExecution.terminal m env w).map (Option.map reserve) := by
  symm
  apply StoppedProcess.terminal_map (NativeOpenExecution.step m env) NativeUnboundedExecution.halted
    (NativeUnboundedExecution.step_halted _ _)
    (NativeOpenExecution.step (m.extendTapes Fin.castSuccEmb) env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    reserve _ _ w
  · intro next
    rw [← execute_one, ← execute_one]
    exact (execute_reserve m env next 1).symm
  · intro next
    rfl

/-- Embed a native world on a real marked virtual-input buffer. -/
@[expose] def inputWorld {k : ℕ} {S P : Type} {word : List Bool}
    (w : World k S Unit P word) (outer : List Bool) (pos : Fin (outer.length + 2)) :
    World (k + 2) S Unit P outer :=
  ⟨InputFromTape.config true w.config outer pos, w.memory⟩

private theorem execute_virtual {k : ℕ} {S P : Type} {word : List Bool}
    (m : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (w : World k S Unit P word) (outer : List Bool) (pos : Fin (outer.length + 2)) (t : ℕ) :
    execute m.inputFromTape env t (inputWorld w outer pos) =
      (execute m env t w).map (fun v => inputWorld v outer pos) := by
  simp only [execute, inputWorld, MultiTapePTM.runConfigFrom_inputFromTape,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
  rfl

/-- Exact unbounded law of the actual virtual-input compiler, including divergence. -/
theorem terminal_inputWorld {k : ℕ} {S P : Type} {word : List Bool}
    (m : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (w : World k S Unit P word) (outer : List Bool) (pos : Fin (outer.length + 2)) :
    NativeUnboundedExecution.terminal m.inputFromTape env (inputWorld w outer pos) =
      (NativeUnboundedExecution.terminal m env w).map
        (Option.map fun v => inputWorld v outer pos) := by
  symm
  apply StoppedProcess.terminal_map (NativeOpenExecution.step m env) NativeUnboundedExecution.halted
    (NativeUnboundedExecution.step_halted _ _) (NativeOpenExecution.step m.inputFromTape env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (fun v => inputWorld v outer pos) _ _ w
  · intro next
    rw [← execute_one, ← execute_one]
    exact (execute_virtual m env next outer pos 1).symm
  · intro next
    rfl

/-- The actual full-reader code reserves the flag tape needed by the continuation.
Its reply buffer is produced by native output instructions, starting blank. -/
def reader (k : ℕ) : MultiTapePTM (k + 2) Bool NativeQueryAll.Control Unit :=
  ((NativeQueryAll.machine () k).outputToTape).extendTapes Fin.castSuccEmb

/-- The actual mark/rewind phase, run after the complete response has arrived. -/
@[expose] def prepare (k : ℕ) :
    MultiTapePTM (k + 2) Bool (MarkWorkState ⊕ RewindWorkState) Unit :=
  MultiTapePTM.ofDeterministic (prepareInput k true)

/-- One actual native program: issue the query, copy the whole reply, prepare its
real work buffer, and execute the supplied actual native continuation on it.
No correctness/termination contract on that continuation is required. -/
def machine {k : ℕ} {S : Type} (continuation : MultiTapePTM k Bool S Unit) :
    MultiTapePTM (k + 2) Bool
      (NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ S) Unit :=
  (reader k).seq ((prepare k).seq continuation.inputFromTape)

/-- Ordinary native storage retained across a full response handoff. No size bound,
canonical encoding or zero-head assumption is imposed. -/
structure Workspace (k : ℕ) where
  /-- Actual two-sided work tapes. -/
  tapes : Fin k → ℤ → Option Bool
  /-- Actual work-tape head positions. -/
  positions : Fin k → ℤ

/-- Runtime words stored at head position zero, including an arbitrary encoded context. -/
@[expose] def Workspace.words {k : ℕ} (words : Fin k → List Bool) : Workspace k :=
  ⟨fun i => tapeOfList (words i), fun _ => 0⟩

private def queryStart {k : ℕ} {P : Type} (request : List Bool)
    (memory : Memory Unit P) (workspace : Workspace k) :
    World k NativeQueryAll.Control Unit P request :=
  ⟨{ (NativeQueryAll.machine () k).initialConfig request with
    tapes := { ((NativeQueryAll.machine () k).initialConfig request).tapes with
      workTapes := workspace.tapes
      workTapePos := workspace.positions } }, memory⟩

/-- Enter the actual response pipeline with retained ordinary storage and fresh
reply/flag buffers. These extra buffers are blank, not supplied responses. -/
@[expose] def startFrom {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (request : List Bool)
    (memory : Memory Unit P) (workspace : Workspace k) :
    World (k + 2) (NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ S)
      Unit P request :=
  ⟨{ (machine continuation).initialConfig request with
    tapes := { ((machine continuation).initialConfig request).tapes with
      workTapes := Fin.append workspace.tapes ![fun _ => none, fun _ => none]
      workTapePos := Fin.append workspace.positions ![0, 0] } }, memory⟩

private def received {k : ℕ} {P : Type} (request : List Bool)
    (memory : Memory Unit P) (reply : Reply) (next : P) (workspace : Workspace k) :
    World (k + 2) NativeQueryAll.Control Unit P request :=
  reserve (NativeOutputBuffer.world
    (NativeQueryAll.finishFrom () (queryStart request memory workspace) reply next))

/-- The source configuration of the actual continuation. All ordinary tapes and
heads survive; only its immutable virtual input is the newly received word. -/
@[expose] def localStartFrom {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (request : List Bool)
    (memory : Memory Unit P) (reply : Reply) (next : P) (workspace : Workspace k) :
    World k S Unit P reply.word :=
  ⟨{ continuation.initialConfig reply.word with
    tapes := { (continuation.initialConfig reply.word).tapes with
      workTapes := workspace.tapes
      workTapePos := workspace.positions }
    channels := (NativeQueryAll.finish (k := k) () request memory reply next).config.channels },
    memory.record ((), request) reply next⟩

/-- Runtime storage is preserved exactly at the continuation handoff, including
nonzero heads and noncanonical or unbounded two-sided tape contents. -/
theorem localStartFrom_workspace {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (request : List Bool)
    (memory : Memory Unit P) (reply : Reply) (next : P) (workspace : Workspace k) :
    (localStartFrom continuation request memory reply next workspace).config.tapes.workTapes =
        workspace.tapes ∧
      (localStartFrom continuation request memory reply next workspace).config.tapes.workTapePos =
        workspace.positions := ⟨rfl, rfl⟩

/-- The blank-workspace specialization of the continuation handoff. -/
@[expose] def localStart {k : ℕ} {S P : Type} (continuation : MultiTapePTM k Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P) :
    World k S Unit P reply.word :=
  ⟨{ continuation.initialConfig reply.word with
    channels := (NativeQueryAll.finish (k := k) () request memory reply next).config.channels },
    memory.record ((), request) reply next⟩

private def ready {k : ℕ} {S P : Type} (continuation : MultiTapePTM k Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P)
    (workspace : Workspace k) :
    World (k + 2) S Unit P request :=
  inputWorld (localStartFrom continuation request memory reply next workspace) request
    ⟨request.length + 1, by omega⟩

private def readerStart {k : ℕ} {P : Type} (request : List Bool)
    (memory : Memory Unit P) (workspace : Workspace k) :
    World (k + 2) NativeQueryAll.Control Unit P request :=
  reserve (NativeOutputBuffer.world (queryStart request memory workspace))

private def buffer (k : ℕ) (request word : List Bool) (workspace : Workspace k) :
    Cfg (k + 2) Bool NativeQueryAll.Control request :=
  ⟨none, ⟨request.length + 1, by omega⟩,
    Fin.append workspace.tapes ![tapeOfList word, fun _ => none],
    Fin.append workspace.positions ![(word.length : ℤ), 0], []⟩

private theorem left_index {k : ℕ} (i : Fin k) :
    i.castAdd 2 = i.castSucc.castSucc := rfl
private theorem buffer_index (k : ℕ) :
    Fin.natAdd k (0 : Fin 2) = (Fin.last k).castSucc := by ext; simp
private theorem flag_index (k : ℕ) :
    Fin.natAdd k (1 : Fin 2) = Fin.last (k + 1) := by ext; simp

private theorem append_two {α : Type} {k : ℕ} (f : Fin k → α) (a b : α) :
    Fin.append f ![a, b] = Fin.lastCases b (Fin.lastCases a f) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left, left_index]
    simp
  · rw [Fin.append_right]
    fin_cases i
    · change a = Fin.lastCases (motive := fun _ : Fin (k + 2) => α) b
        (fun j : Fin (k + 1) => Fin.lastCases (motive := fun _ : Fin (k + 1) => α) a f j)
        (Fin.natAdd k (0 : Fin 2))
      rw [buffer_index k]
      simp
    · change b = Fin.lastCases (motive := fun _ : Fin (k + 2) => α) b
        (fun j : Fin (k + 1) => Fin.lastCases (motive := fun _ : Fin (k + 1) => α) a f j)
        (Fin.natAdd k (1 : Fin 2))
      rw [flag_index k]
      simp

private theorem append_constant {α : Type} {k : ℕ} (f : Fin k → α) (a : α) :
    Fin.append f (fun _ : Fin 2 => a) = Fin.lastCases a (Fin.lastCases a f) := by
  have he : (fun _ : Fin 2 => a) = ![a, a] := by funext i; fin_cases i <;> rfl
  rw [he, append_two]

private theorem append_repeat {α : Type} {k : ℕ} (a : α) :
    Fin.append (fun _ : Fin k => a) ![a, a] = fun _ => a := by
  have he : ![a, a] = (fun _ : Fin 2 => a) := by funext i; fin_cases i <;> rfl
  rw [he]
  exact Fin.append_castAdd_natAdd (f := fun _ : Fin (k + 2) => a)

attribute [local simp] append_two append_constant left_index buffer_index flag_index

private theorem received_tapes {k : ℕ} {P : Type} (request : List Bool)
    (memory : Memory Unit P) (reply : Reply) (next : P) (workspace : Workspace k) :
    (received (k := k) request memory reply next workspace).config.tapes =
      buffer k request reply.word workspace := by
  simp only [received, reserve, Config.embed, NativeOutputBuffer.world,
    OutputToTape.config, embed_castSucc]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    cases i using (Fin.addCases (m := k) (n := 2)) with
    | left i =>
      simp [NativeQueryAll.finishFrom, queryStart, MultiTapeMachine.initialConfig,
        Cfg.init, outCfg, buffer]
    | right i => fin_cases i <;>
        simp [NativeQueryAll.finishFrom, queryStart, MultiTapeMachine.initialConfig, Cfg.init,
          outCfg, buffer]
  · funext i
    cases i using (Fin.addCases (m := k) (n := 2)) with
    | left i =>
      simp [NativeQueryAll.finishFrom, queryStart, MultiTapeMachine.initialConfig,
        Cfg.init, outCfg, buffer]
    | right i => fin_cases i <;>
        simp [NativeQueryAll.finishFrom, queryStart, MultiTapeMachine.initialConfig, Cfg.init,
          outCfg, buffer]

private theorem prepare_run {k : ℕ} {S P : Type} (continuation : MultiTapePTM k Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P)
    (workspace : Workspace k) :
    (prepareInput k true).runFrom
      (NativeSequential.resume (prepare k)
        (received (k := k) request memory reply next workspace)).config.tapes
        (reply.word.length + 4) =
      { (ready continuation request memory reply next workspace).config.tapes with
        state := (none : Option (MarkWorkState ⊕ RewindWorkState)) } := by
  have he := runFrom_prepareInput true
    (received (k := k) request memory reply next workspace).config.tapes reply.word
    (by rw [received_tapes]; simp [buffer])
    (by rw [received_tapes]; simp [buffer])
    (by rw [received_tapes]; simp [buffer])
  change (prepareInput k true).runFrom
    ((received (k := k) request memory reply next workspace).config.tapes.withState
      (some (prepareInput k true).q₀)) (reply.word.length + 4) = _
  rw [he, received_tapes]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    cases i using (Fin.addCases (m := k) (n := 2)) with
    | left i =>
      have hlast := Fin.castSucc_ne_last i.castSucc
      simp [ready, localStartFrom, inputWorld, InputFromTape.config, inCfg, buffer,
        MultiTapeMachine.initialConfig, Cfg.init,
        hlast]
    | right i => fin_cases i <;> simp [ready, localStartFrom, inputWorld, InputFromTape.config,
        inCfg, buffer, MultiTapeMachine.initialConfig, Cfg.init]
  · funext i
    cases i using (Fin.addCases (m := k) (n := 2)) with
    | left i =>
      have hbuffer : i.castSucc.castSucc ≠ (Fin.last k).castSucc := by
        intro h
        exact Fin.castSucc_ne_last i (Fin.ext (congrArg (fun j : Fin (k + 2) => j.val) h))
      simp [ready, localStartFrom, inputWorld, InputFromTape.config, inCfg, buffer,
        MultiTapeMachine.initialConfig, Cfg.init,
        hbuffer]
    | right i => fin_cases i <;> simp [ready, localStartFrom, inputWorld, InputFromTape.config,
        inCfg, buffer, MultiTapeMachine.initialConfig, Cfg.init, Fin.ext_iff]

private def prepared {k : ℕ} {S P : Type} (continuation : MultiTapePTM k Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P)
    (workspace : Workspace k) :
    World (k + 2) (MarkWorkState ⊕ RewindWorkState) Unit P request :=
  ⟨{ (ready continuation request memory reply next workspace).config with
    tapes := { (ready continuation request memory reply next
      workspace).config.tapes with state := none } },
    (ready continuation request memory reply next workspace).memory⟩

private theorem prepare_terminal {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P)
    (workspace : Workspace k) :
    NativeUnboundedExecution.terminal (prepare k) env
      (NativeSequential.resume (prepare k)
        (received (k := k) request memory reply next workspace)) =
        PMF.pure (some (prepared continuation request memory reply next workspace)) := by
  apply terminal_of_clock (prepare k) env _
    (prepared continuation request memory reply next workspace)
    (reply.word.length + 4) ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic (prepareInput k true)).runOracleConfigFrom
      (reply.word.length + 4)
      (NativeSequential.resume (prepare k)
        (received (k := k) request memory reply next workspace)).config)).run
        (NativeSequential.resume (prepare k)
          (received (k := k) request memory reply next workspace)).memory).map
          (fun p => (⟨p.1, p.2⟩ : World (k + 2) _ Unit P request)) = _
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map,
    prepare_run continuation]
  rfl

/-- Embed the actual continuation result back into the combined native program.
All continuation work tapes, answer channels and oracle memory are preserved. -/
@[expose] def resultWorld {k : ℕ} {S P : Type} {word : List Bool}
    (request : List Bool) (final : World k S Unit P word) :
    World (k + 2) (NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ S) Unit P
      request :=
  NativeSequential.right (First := NativeQueryAll.Control)
    (NativeSequential.right (First := MarkWorkState ⊕ RewindWorkState)
      (⟨InputFromTape.config true final.config request ⟨request.length + 1, by omega⟩,
        final.memory⟩))

private theorem after_reader {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P)
    (workspace : Workspace k) :
    NativeUnboundedExecution.terminal ((prepare k).seq continuation.inputFromTape) env
      (NativeSequential.left continuation.inputFromTape
        (NativeSequential.resume (prepare k)
          (received (k := k) request memory reply next workspace))) =
      (NativeUnboundedExecution.terminal continuation env
        (localStartFrom continuation request memory reply next workspace)).map
          (Option.map fun final => NativeSequential.right
            (First := MarkWorkState ⊕ RewindWorkState)
            (⟨InputFromTape.config true final.config request ⟨request.length + 1, by omega⟩,
              final.memory⟩)) := by
  rw [NativeSequential.terminal_seq, prepare_terminal continuation, PMF.pure_bind]
  have he : NativeSequential.resume continuation.inputFromTape
      (prepared continuation request memory reply next workspace) =
      ready continuation request memory reply next workspace := rfl
  change (NativeUnboundedExecution.terminal continuation.inputFromTape env
    (NativeSequential.resume continuation.inputFromTape
      (prepared continuation request memory reply next workspace))).map _ = _
  rw [he, ready, terminal_inputWorld, PMF.map_comp]
  congr 1
  funext value
  cases value <;> rfl

/-- Actual entry with retained answer channels; only its query buffer must be empty. -/
@[expose] def startWithChannels {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (request : List Bool)
    (memory : Memory Unit P) (workspace : Workspace k) (channels : Unit → Channel Bool) :
    World (k + 2) (NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ S)
      Unit P request :=
  ⟨{ (startFrom continuation request memory workspace).config with channels := channels }, memory⟩

private theorem reader_terminal_channels {k : ℕ} {P : Type} (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) (workspace : Workspace k)
    (channels : Unit → Channel Bool) (hb : (channels ()).queryBuffer = []) :
    NativeUnboundedExecution.terminal (reader k) env
      (reserve (NativeOutputBuffer.world
        (⟨{ (queryStart request memory workspace).config with channels := channels }, memory⟩ :
          World k NativeQueryAll.Control Unit P request))) =
      (env ((), request) memory).map fun (reply, next) =>
        some (received (k := k) request memory reply next workspace) := by
  rw [reader, terminal_reserve, NativeOutputBuffer.terminal_buffer,
    NativeQueryAll.terminal_from () env _ rfl rfl hb, PMF.map_comp, PMF.map_comp]
  congr 1

/-- The actual retained-storage response pipeline accepts previous answer channels.
The first query overwrites its answer only after forming the full new request;
no channel-reset operation, independence assumption or restart contract is supplied. -/
theorem terminal_from_channels {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) (workspace : Workspace k)
    (channels : Unit → Channel Bool) (hb : (channels ()).queryBuffer = []) :
    NativeUnboundedExecution.terminal (machine continuation) env
      (startWithChannels continuation request memory workspace channels) =
        (env ((), request) memory).bind fun (reply, next) =>
          (NativeUnboundedExecution.terminal continuation env
            (localStartFrom continuation request memory reply next workspace)).map
              (Option.map (resultWorld request)) := by
  let base := (⟨{ (queryStart request memory workspace).config with channels := channels },
    memory⟩ : World k NativeQueryAll.Control Unit P request)
  let readerEntry := reserve (NativeOutputBuffer.world base)
  have he : ((startWithChannels continuation request memory workspace channels) :
      World (k + 2) _ Unit P request) =
      NativeSequential.left ((prepare k).seq continuation.inputFromTape)
        readerEntry := by
    simp only [startWithChannels, startFrom, readerEntry, base, queryStart,
      NativeOutputBuffer.world, reserve,
      Config.embed, OutputToTape.config, embed_castSucc, NativeSequential.left,
      Sequential.left, machine, MultiTapeMachine.initialConfig, Cfg.init, outCfg, append_two,
      Cfg.mapState, tapeOfList_nil]
    rfl
  rw [he, machine, NativeSequential.terminal_seq,
    reader_terminal_channels env request memory workspace channels hb, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro pair hp
  obtain ⟨reply, next⟩ := pair
  change (NativeUnboundedExecution.terminal ((prepare k).seq continuation.inputFromTape) env
    (NativeSequential.resume ((prepare k).seq continuation.inputFromTape)
      (received (k := k) request memory reply next workspace))).map _ = _
  have hr : NativeSequential.resume ((prepare k).seq continuation.inputFromTape)
      (received (k := k) request memory reply next workspace) =
      NativeSequential.left continuation.inputFromTape
        (NativeSequential.resume (prepare k)
          (received (k := k) request memory reply next workspace)) := rfl
  rw [hr, after_reader, PMF.map_comp]
  change _ = (NativeUnboundedExecution.terminal continuation env
    (localStartFrom continuation request memory reply next workspace)).map
      (Option.map (resultWorld request))
  congr 1
  funext value
  cases value <;> rfl

/-- The original fresh-channel entry is a specialization of retained-channel execution. -/
theorem terminal_from {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) (workspace : Workspace k) :
    NativeUnboundedExecution.terminal (machine continuation) env
      (startFrom continuation request memory workspace) =
        (env ((), request) memory).bind fun (reply, next) =>
          (NativeUnboundedExecution.terminal continuation env
            (localStartFrom continuation request memory reply next workspace)).map
              (Option.map (resultWorld request)) := by
  exact terminal_from_channels continuation env request memory workspace
    (fun _ => ⟨[], [], 0⟩) rfl

/-- Existing blank-workspace entry is the special case of retained-context transport. -/
theorem terminal_machine {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (machine continuation) env
      ⟨(machine continuation).initialConfig request, memory⟩ =
        (env ((), request) memory).bind fun (reply, next) =>
          (NativeUnboundedExecution.terminal continuation env
            (localStart continuation request memory reply next)).map
              (Option.map (resultWorld request)) := by
  simpa only [startFrom, localStartFrom, localStart, machine, reader,
    MultiTapeMachine.initialConfig, Cfg.init, append_repeat] using
    terminal_from continuation env request memory ⟨fun _ _ => none, fun _ => 0⟩

end Cslib.Probability.NativeResponseExecution
