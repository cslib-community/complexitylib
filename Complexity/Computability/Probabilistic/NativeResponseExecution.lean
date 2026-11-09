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
There is no common reply-length clock and no supplied prepared-input premise.
The complete adaptive scheduler/restart loop remains a separate obligation.
This is an implementation connection for [Wang2027], Theorem 5, PDF p. 12 and
Appendix A.5 p. 16; local instructions are excluded from the external deadline.

## Main definitions

* `machine`: full query, actual buffer preparation and virtual-input continuation.

## Main results

* `terminal_machine`: exact whole-configuration unbounded law, including divergence.
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

private def virtual {k : ℕ} {S P : Type} {word : List Bool}
    (w : World k S Unit P word) (outer : List Bool) (pos : Fin (outer.length + 2)) :
    World (k + 2) S Unit P outer :=
  ⟨InputFromTape.config true w.config outer pos, w.memory⟩

private theorem execute_virtual {k : ℕ} {S P : Type} {word : List Bool}
    (m : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (w : World k S Unit P word) (outer : List Bool) (pos : Fin (outer.length + 2)) (t : ℕ) :
    execute m.inputFromTape env t (virtual w outer pos) =
      (execute m env t w).map (fun v => virtual v outer pos) := by
  simp only [execute, virtual, MultiTapePTM.runConfigFrom_inputFromTape,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
  rfl

private theorem terminal_virtual {k : ℕ} {S P : Type} {word : List Bool}
    (m : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (w : World k S Unit P word) (outer : List Bool) (pos : Fin (outer.length + 2)) :
    NativeUnboundedExecution.terminal m.inputFromTape env (virtual w outer pos) =
      (NativeUnboundedExecution.terminal m env w).map
        (Option.map fun v => virtual v outer pos) := by
  symm
  apply StoppedProcess.terminal_map (NativeOpenExecution.step m env) NativeUnboundedExecution.halted
    (NativeUnboundedExecution.step_halted _ _) (NativeOpenExecution.step m.inputFromTape env)
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)
    (fun v => virtual v outer pos) _ _ w
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
def prepare (k : ℕ) :
    MultiTapePTM (k + 2) Bool (MarkWorkState ⊕ RewindWorkState) Unit :=
  MultiTapePTM.ofDeterministic (prepareInput k true)

/-- One actual native program: issue the query, copy the whole reply, prepare its
real work buffer, and execute the supplied actual native continuation on it.
No correctness/termination contract on that continuation is required. -/
def machine {k : ℕ} {S : Type} (continuation : MultiTapePTM k Bool S Unit) :
    MultiTapePTM (k + 2) Bool
      (NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ S) Unit :=
  (reader k).seq ((prepare k).seq continuation.inputFromTape)

private def received {k : ℕ} {P : Type} (request : List Bool)
    (memory : Memory Unit P) (reply : Reply) (next : P) :
    World (k + 2) NativeQueryAll.Control Unit P request :=
  reserve (NativeOutputBuffer.world (NativeQueryAll.finish (k := k) () request memory reply next))

/-- The continuation's source configuration, with the actual received channel and
recorded oracle state. The main theorem derives this handoff from instructions. -/
@[expose] def localStart {k : ℕ} {S P : Type} (continuation : MultiTapePTM k Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P) :
    World k S Unit P reply.word :=
  ⟨{ continuation.initialConfig reply.word with
    channels := (NativeQueryAll.finish (k := k) () request memory reply next).config.channels },
    memory.record ((), request) reply next⟩

private def ready {k : ℕ} {S P : Type} (continuation : MultiTapePTM k Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P) :
    World (k + 2) S Unit P request :=
  virtual (localStart continuation request memory reply next) request
    ⟨request.length + 1, by omega⟩

private theorem reader_initial {k : ℕ} {P : Type} (request : List Bool)
    (memory : Memory Unit P) :
    (⟨(reader k).initialConfig request, memory⟩ :
      World (k + 2) NativeQueryAll.Control Unit P request) =
      reserve (NativeOutputBuffer.world (NativeQueryAll.start () k request memory)) := by
  have he := congrArg (fun w : World (k + 1) NativeQueryAll.Control Unit P request =>
    reserve w) (NativeQueryAll.buffered_start () request memory)
  change _ = _ at he
  rw [reader, MultiTapeMachine.initialConfig_extendTapes]
  exact he

private theorem reader_terminal {k : ℕ} {P : Type} (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (reader k) env
      ⟨(reader k).initialConfig request, memory⟩ =
      (env ((), request) memory).map fun (reply, next) =>
        some (received (k := k) request memory reply next) := by
  rw [reader_initial, reader, terminal_reserve, NativeOutputBuffer.terminal_buffer,
    NativeQueryAll.terminal_query, PMF.map_comp, PMF.map_comp]
  rfl

private def buffer (k : ℕ) (request word : List Bool) :
    Cfg (k + 2) Bool NativeQueryAll.Control request :=
  ⟨none, ⟨request.length + 1, by omega⟩,
    Fin.append (fun _ : Fin k => fun _ => none) ![tapeOfList word, fun _ => none],
    Fin.append (fun _ : Fin k => (0 : ℤ)) ![(word.length : ℤ), 0], []⟩

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

attribute [local simp] append_two left_index buffer_index flag_index

private theorem received_tapes {k : ℕ} {P : Type} (request : List Bool)
    (memory : Memory Unit P) (reply : Reply) (next : P) :
    (received (k := k) request memory reply next).config.tapes = buffer k request reply.word := by
  simp only [received, reserve, Config.embed, NativeOutputBuffer.world,
    OutputToTape.config, embed_castSucc]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    cases i using (Fin.addCases (m := k) (n := 2)) with
    | left i => simp [NativeQueryAll.finish, NativeQueryAll.finishFrom,
        NativeQueryAll.start, MultiTapeMachine.initialConfig, Cfg.init, outCfg, buffer]
    | right i => fin_cases i <;>
        simp [NativeQueryAll.finish, NativeQueryAll.finishFrom,
          NativeQueryAll.start, MultiTapeMachine.initialConfig, Cfg.init, outCfg, buffer]
  · funext i
    cases i using (Fin.addCases (m := k) (n := 2)) with
    | left i => simp [NativeQueryAll.finish, NativeQueryAll.finishFrom,
        NativeQueryAll.start, MultiTapeMachine.initialConfig, Cfg.init, outCfg, buffer]
    | right i => fin_cases i <;>
        simp [NativeQueryAll.finish, NativeQueryAll.finishFrom,
          NativeQueryAll.start, MultiTapeMachine.initialConfig, Cfg.init, outCfg, buffer]

private theorem prepare_run {k : ℕ} {S P : Type} (continuation : MultiTapePTM k Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P) :
    (prepareInput k true).runFrom
      (NativeSequential.resume (prepare k)
        (received (k := k) request memory reply next)).config.tapes
        (reply.word.length + 4) =
      { (ready continuation request memory reply next).config.tapes with
        state := (none : Option (MarkWorkState ⊕ RewindWorkState)) } := by
  have hz : Fin.append (fun _ : Fin k => (0 : ℤ)) (fun _ : Fin 2 => (0 : ℤ)) =
      (fun _ => 0) := by
    funext i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]
  have he := runFrom_prepareInput true
    (received (k := k) request memory reply next).config.tapes reply.word
    (by rw [received_tapes]; simp [buffer])
    (by rw [received_tapes]; simp [buffer])
    (by rw [received_tapes]; simp [buffer])
  change (prepareInput k true).runFrom
    ((received (k := k) request memory reply next).config.tapes.withState
      (some (prepareInput k true).q₀)) (reply.word.length + 4) = _
  rw [he, received_tapes]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    cases i using (Fin.addCases (m := k) (n := 2)) with
    | left i =>
      have hlast := Fin.castSucc_ne_last i.castSucc
      simp [ready, localStart, virtual, InputFromTape.config, inCfg, buffer,
        MultiTapeMachine.initialConfig, Cfg.init,
        hlast]
    | right i => fin_cases i <;> simp [ready, localStart, virtual, InputFromTape.config,
        inCfg, buffer, MultiTapeMachine.initialConfig, Cfg.init]
  · funext i
    cases i using (Fin.addCases (m := k) (n := 2)) with
    | left i =>
      have hbuffer : i.castSucc.castSucc ≠ (Fin.last k).castSucc := by
        intro h
        exact Fin.castSucc_ne_last i (Fin.ext (congrArg (fun j : Fin (k + 2) => j.val) h))
      simp [ready, localStart, virtual, InputFromTape.config, inCfg, buffer,
        MultiTapeMachine.initialConfig, Cfg.init, hz,
        hbuffer]
    | right i => fin_cases i <;> simp [ready, localStart, virtual, InputFromTape.config,
        inCfg, buffer, MultiTapeMachine.initialConfig, Cfg.init, hz, Fin.ext_iff]

private def prepared {k : ℕ} {S P : Type} (continuation : MultiTapePTM k Bool S Unit)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P) :
    World (k + 2) (MarkWorkState ⊕ RewindWorkState) Unit P request :=
  ⟨{ (ready continuation request memory reply next).config with
    tapes := { (ready continuation request memory reply next).config.tapes with state := none } },
    (ready continuation request memory reply next).memory⟩

private theorem prepare_terminal {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P) :
    NativeUnboundedExecution.terminal (prepare k) env
      (NativeSequential.resume (prepare k) (received (k := k) request memory reply next)) =
        PMF.pure (some (prepared continuation request memory reply next)) := by
  apply terminal_of_clock (prepare k) env _ (prepared continuation request memory reply next)
    (reply.word.length + 4) ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic (prepareInput k true)).runOracleConfigFrom
      (reply.word.length + 4)
      (NativeSequential.resume (prepare k)
        (received (k := k) request memory reply next)).config)).run
        (NativeSequential.resume (prepare k)
          (received (k := k) request memory reply next)).memory).map
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
    (request : List Bool) (memory : Memory Unit P) (reply : Reply) (next : P) :
    NativeUnboundedExecution.terminal ((prepare k).seq continuation.inputFromTape) env
      (NativeSequential.left continuation.inputFromTape
        (NativeSequential.resume (prepare k) (received (k := k) request memory reply next))) =
      (NativeUnboundedExecution.terminal continuation env
        (localStart continuation request memory reply next)).map
          (Option.map fun final => NativeSequential.right
            (First := MarkWorkState ⊕ RewindWorkState)
            (⟨InputFromTape.config true final.config request ⟨request.length + 1, by omega⟩,
        final.memory⟩)) := by
  rw [NativeSequential.terminal_seq, prepare_terminal continuation, PMF.pure_bind]
  have he : NativeSequential.resume continuation.inputFromTape
      (prepared continuation request memory reply next) =
      ready continuation request memory reply next := rfl
  change (NativeUnboundedExecution.terminal continuation.inputFromTape env
    (NativeSequential.resume continuation.inputFromTape
      (prepared continuation request memory reply next))).map _ = _
  rw [he, ready, terminal_virtual, PMF.map_comp]
  congr 1
  funext value
  cases value <;> rfl

/-- Exact full-configuration law of one actual native query followed by actual
reply processing, including arbitrary divergent continuation mass. The buffer,
marker and cursor are produced by the program itself; clocks may depend on the
received word. No prepared-input, termination or representation contract occurs. -/
theorem terminal_machine {k : ℕ} {S P : Type}
    (continuation : MultiTapePTM k Bool S Unit) (env : Environment Unit P)
    (request : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (machine continuation) env
      ⟨(machine continuation).initialConfig request, memory⟩ =
        (env ((), request) memory).bind fun (reply, next) =>
          (NativeUnboundedExecution.terminal continuation env
            (localStart continuation request memory reply next)).map
              (Option.map (resultWorld request)) := by
  have he : (⟨(machine continuation).initialConfig request, memory⟩ :
      World (k + 2) _ Unit P request) =
      NativeSequential.left ((prepare k).seq continuation.inputFromTape)
        ⟨(reader k).initialConfig request, memory⟩ := rfl
  rw [he, machine, NativeSequential.terminal_seq, reader_terminal, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro pair hp
  obtain ⟨reply, next⟩ := pair
  change (NativeUnboundedExecution.terminal ((prepare k).seq continuation.inputFromTape) env
    (NativeSequential.resume ((prepare k).seq continuation.inputFromTape)
      (received (k := k) request memory reply next))).map _ = _
  have hr : NativeSequential.resume ((prepare k).seq continuation.inputFromTape)
      (received (k := k) request memory reply next) =
      NativeSequential.left continuation.inputFromTape
        (NativeSequential.resume (prepare k) (received (k := k) request memory reply next)) := rfl
  rw [hr, after_reader, PMF.map_comp]
  change _ = (NativeUnboundedExecution.terminal continuation env
    (localStart continuation request memory reply next)).map (Option.map (resultWorld request))
  congr 1
  funext value
  cases value <;> rfl

end Cslib.Probability.NativeResponseExecution
