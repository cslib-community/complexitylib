/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeContextLoader
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# A native stop guard before open execution

A computed stop bit and framed output occupy the beginning of context tape zero.
The native guard emits the stored output without an oracle call when stopping;
otherwise it enters the actual consumer on unchanged tapes. Stopped laws are
proved from the transition table, preserving arbitrary consumer divergence and
shared oracle memory and arbitrary live answer channels. The channel-general laws
also support post-response dispatch; this reader is not a complete
source-admitted adaptive selector for [Wang2027], Theorem 5 p. 12/App. A.5 p. 16.

## Main definitions

* `packet`: the runtime stop flag, framed output and retained context.
* `machine`: finite native control that checks the flag before entering a consumer.

## Main results

* `terminal_stop`, `terminal_go`: exact unbounded native laws for both branches.
* `terminal_stop_channels`, `terminal_go_channels`: dispatch retaining live answer channels.
* `runtime_observation`: the joint law with the existing correlated two-query carrier.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeStopGuard
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

/-- A stop bit, a self-delimiting output word and the retained runtime payload. -/
@[expose] def packet (stop : Bool) (output payload : List Bool) : List Bool :=
  stop :: (frame output ++ payload)

/-- The three guard modes check the bit, read a frame tag, and emit its payload bit.
Other states execute the actual native consumer. -/
@[expose] def machine {S : Type} (consumer : MultiTapePTM 4 Bool S Unit) :
    MultiTapePTM 4 Bool (Fin 3 ⊕ S) Unit where
  initial := .inl 0
  tr state input work answer bit := match state with
    | .inr q => MultiTapeMachine.Action.mapState Sum.inr
        (consumer.tr q input work answer bit)
    | .inl mode =>
      if mode = 0 then
        match work 0 with
        | some false => .step
            ⟨0, fun _ => (none, 0), none, some (.inr consumer.initial)⟩
            (fun _ => none) (fun _ => 0)
        | some true => .step
            ⟨0, fun i => (none, if i = 0 then 1 else 0), none, some (.inl 1)⟩
            (fun _ => none) (fun _ => 0)
        | none => .step ⟨0, fun _ => (none, 0), none, none⟩
            (fun _ => none) (fun _ => 0)
      else if mode = 1 then
        match work 0 with
        | some true => .step
            ⟨0, fun i => (none, if i = 0 then 1 else 0), none, some (.inl 2)⟩
            (fun _ => none) (fun _ => 0)
        | _ => .step
            ⟨0, fun i => (none, if i = 0 then 1 else 0), none, none⟩
            (fun _ => none) (fun _ => 0)
      else match work 0 with
        | some value => .step
            ⟨0, fun i => (none, if i = 0 then 1 else 0), some value, some (.inl 1)⟩
            (fun _ => none) (fun _ => 0)
        | none => .step ⟨0, fun _ => (none, 0), none, none⟩
            (fun _ => none) (fun _ => 0)

private theorem terminal_run {S P : Type} {input : List Bool}
    (consumer : MultiTapePTM 4 Bool S Unit) (env : Environment Unit P)
    (world : World 4 S Unit P input) :
    NativeUnboundedExecution.terminal (machine consumer) env
      (NativeSequential.right (First := Fin 3) world) =
      (NativeUnboundedExecution.terminal consumer env world).map
        (Option.map (NativeSequential.right (First := Fin 3))) := by
  exact NativeSequential.terminal_mapControl consumer (machine consumer) Sum.inr
    (fun _ _ _ _ _ => rfl) env world

private def point {S P : Type} (_consumer : MultiTapePTM 4 Bool S Unit)
    (input word : List Bool) (memory : Memory Unit P) (state : Option (Fin 3 ⊕ S))
    (head : ℕ) (out : List Bool)
    (channels : Unit → Channel Bool := fun _ => ⟨[], [], 0⟩) : World 4 (Fin 3 ⊕ S) Unit P input :=
  ⟨⟨⟨state, 1, ![tapeOfList word, fun _ => none, fun _ => none, fun _ => none],
    ![(head : ℤ), 0, 0, 0], out⟩, channels⟩, memory⟩

private theorem tag_step {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input pre rest payload out : List Bool)
    (memory : Memory Unit P) (bit : Bool) (channels : Unit → Channel Bool) :
    NativeOpenExecution.step (machine consumer) env
      (point (channels := channels) consumer input (pre ++ true :: bit :: (frame rest ++ payload))
        memory
        (some (.inl 1)) pre.length out) =
      PMF.pure (point (channels := channels) consumer
        input (pre ++ true :: bit :: (frame rest ++ payload))
        memory
        (some (.inl 2)) (pre.length + 1) out) := by
  have hs : (point (channels := channels) consumer
        input (pre ++ true :: bit :: (frame rest ++ payload))
        memory
      (some (.inl 1)) pre.length out).config.tapes.workTapeSymbols 0 = some true := by
    simp [point, Cfg.workTapeSymbols]
  simp only [point] at hs
  simp only [NativeOpenExecution.step, point, machine]
  simp only [hs, show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, PMF.bind_const]
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World 4 (Fin 3 ⊕ S) Unit P input))
  apply Config.ext
  · refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [Config.step, Action.apply]
    · funext i; fin_cases i <;> simp [Config.step, Action.apply]
    · simp [Config.step, Action.apply]
  · simp [Config.step]

private theorem value_step {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input pre rest payload out : List Bool)
    (memory : Memory Unit P) (bit : Bool) (channels : Unit → Channel Bool) :
    NativeOpenExecution.step (machine consumer) env
      (point (channels := channels) consumer input (pre ++ true :: bit :: (frame rest ++ payload))
        memory
        (some (.inl 2)) (pre.length + 1) out) =
      PMF.pure (point (channels := channels) consumer
        input (pre ++ true :: bit :: (frame rest ++ payload))
        memory
        (some (.inl 1)) (pre.length + 2) (out ++ [bit])) := by
  have hs : (point (channels := channels) consumer
        input (pre ++ true :: bit :: (frame rest ++ payload))
        memory
      (some (.inl 2)) (pre.length + 1) out).config.tapes.workTapeSymbols 0 = some bit := by
    have hx : tapeOfList (pre ++ true :: bit :: (frame rest ++ payload))
        ((pre.length + 1 : ℕ) : ℤ) = some bit := by
      rw [tapeOfList_ofNat]
      simp
    simpa [point, Cfg.workTapeSymbols] using hx
  simp only [point] at hs
  simp only [NativeOpenExecution.step, point, machine]
  simp only [hs, show (2 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, PMF.bind_const]
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World 4 (Fin 3 ⊕ S) Unit P input))
  apply Config.ext
  · refine Cfg.ext rfl ?_ rfl ?_ rfl
    · simp [Config.step, Action.apply]
    · funext i; fin_cases i <;> simp [Config.step, Action.apply]; omega
  · simp [Config.step]

private theorem tag_end {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input pre payload out : List Bool)
    (memory : Memory Unit P) (channels : Unit → Channel Bool) :
    NativeOpenExecution.step (machine consumer) env
      (point (channels := channels) consumer input (pre ++ false :: payload)
        memory (some (.inl 1)) pre.length out) =
      PMF.pure (point (channels := channels) consumer input (pre ++ false :: payload) memory none
        (pre.length + 1) out) := by
  have hs : (point (channels := channels) consumer input (pre ++ false :: payload) memory
      (some (.inl 1)) pre.length out).config.tapes.workTapeSymbols 0 = some false := by
    simp [point, Cfg.workTapeSymbols]
  simp only [point] at hs
  simp only [NativeOpenExecution.step, point, machine]
  simp only [hs, show (1 : Fin 3) ≠ 0 from by decide, ↓reduceIte, PMF.bind_const]
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World 4 (Fin 3 ⊕ S) Unit P input))
  apply Config.ext
  · refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [Config.step, Action.apply]
    · funext i; fin_cases i <;> simp [Config.step, Action.apply]
    · simp [Config.step, Action.apply]
  · simp [Config.step]

private theorem frame_terminal {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input rest payload : List Bool) (memory : Memory Unit P)
    (channels : Unit → Channel Bool) :
    ∀ pre out,
    NativeUnboundedExecution.terminal (machine consumer) env
      (point (channels := channels) consumer input (pre ++ frame rest ++ payload) memory
        (some (.inl 1))
        pre.length out) =
      PMF.pure (some (point (channels := channels) consumer input
        (pre ++ frame rest ++ payload) memory none
        (pre.length + 2 * rest.length + 1) (out ++ rest))) := by
  induction rest with
  | nil =>
    intro pre out
    simp only [frame_nil, List.append_assoc, List.singleton_append, List.append_nil,
      List.length_nil, Nat.mul_zero, add_zero]
    rw [NativeUnboundedExecution.terminal, StoppedProcess.terminal_step, tag_end,
      PMF.pure_bind]
    exact StoppedProcess.terminal_halted _ _ (NativeUnboundedExecution.step_halted _ _) _ rfl
  | cons bit rest ih =>
    intro pre out
    simp only [frame_cons, List.append_assoc, List.cons_append]
    rw [NativeUnboundedExecution.terminal, StoppedProcess.terminal_step,
      tag_step, PMF.pure_bind, StoppedProcess.terminal_step, value_step, PMF.pure_bind]
    have hw : pre ++ true :: bit :: (frame rest ++ payload) =
        (pre ++ [true, bit]) ++ frame rest ++ payload := by simp [List.append_assoc]
    rw [hw]
    have hl : pre.length + 2 = (pre ++ [true, bit]).length := by simp
    rw [hl]
    change NativeUnboundedExecution.terminal (machine consumer) env _ = _
    rw [ih]
    have hp : (pre ++ [true, bit]).length + 2 * rest.length + 1 =
        pre.length + 2 * (bit :: rest).length + 1 := by simp; omega
    rw [hp]
    simp [List.append_assoc]

/-- Actual stopped world: the output is emitted from its frame on the work tape,
and the complete runtime payload and previous oracle memory remain intact. -/
@[expose] def stopped {S P : Type} (_consumer : MultiTapePTM 4 Bool S Unit)
    (input output payload : List Bool) (memory : Memory Unit P)
    (channels : Unit → Channel Bool := fun _ => ⟨[], [], 0⟩) :
    World 4 (Fin 3 ⊕ S) Unit P input :=
  ⟨⟨⟨none, 1,
    ![tapeOfList (packet true output payload), fun _ => none, fun _ => none, fun _ => none],
    ![(1 + 2 * output.length + 1 : ℕ), 0, 0, 0], output⟩, channels⟩, memory⟩

private theorem initial_point {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (input word : List Bool) (memory : Memory Unit P) :
    NativeContextLoader.loadedStart (machine consumer) input word memory =
      point consumer input word memory (some (.inl 0)) 0 [] := by
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World 4 (Fin 3 ⊕ S) Unit P input))
  apply Config.ext
  · refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; fin_cases i <;> simp [wordsCfg]
    · funext i; fin_cases i <;> rfl
  · rfl

private theorem check_stop {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input output payload : List Bool)
    (memory : Memory Unit P) (channels : Unit → Channel Bool) :
    NativeOpenExecution.step (machine consumer) env
      (point (channels := channels) consumer input (packet true output payload)
        memory (some (.inl 0)) 0 []) =
      PMF.pure (point (channels := channels) consumer input (packet true output payload)
        memory (some (.inl 1)) 1 []) := by
  have hs : (point (channels := channels) consumer input (packet true output payload) memory
      (some (.inl 0)) 0 []).config.tapes.workTapeSymbols 0 = some true := by
    simp [point, packet, Cfg.workTapeSymbols, tapeOfList_zero]
  simp only [point] at hs
  simp only [NativeOpenExecution.step, point, machine, hs, ↓reduceIte, PMF.bind_const]
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World 4 (Fin 3 ⊕ S) Unit P input))
  apply Config.ext
  · refine Cfg.ext rfl ?_ rfl ?_ rfl
    · simp [Config.step, Action.apply]
    · funext i; fin_cases i <;> simp [Config.step, Action.apply]
  · simp [Config.step]

/-- The true guard halts without executing any consumer instruction or sampling
any oracle response. The actual framed output is emitted and earlier bills persist. -/
theorem terminal_stop {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input output payload : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (machine consumer) env
      (NativeContextLoader.loadedStart (machine consumer) input
        (packet true output payload) memory) =
      PMF.pure (some (stopped consumer input output payload memory)) := by
  rw [initial_point, NativeUnboundedExecution.terminal, StoppedProcess.terminal_step,
    check_stop, PMF.pure_bind]
  change NativeUnboundedExecution.terminal (machine consumer) env _ = _
  exact frame_terminal consumer env input output payload memory (fun _ => ⟨[], [], 0⟩) [true] []

/-- The executed stop reader also preserves arbitrary live answer channels.
It can therefore run immediately after an actual response, without resetting the oracle. -/
theorem terminal_stop_channels {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input output payload : List Bool) (memory : Memory Unit P)
    (channels : Unit → Channel Bool) :
    NativeUnboundedExecution.terminal (machine consumer) env
      ⟨{ (NativeContextLoader.loadedStart (machine consumer) input
        (packet true output payload) memory).config with channels := channels }, memory⟩ =
      PMF.pure (some (stopped consumer input output payload memory channels)) := by
  have hi : (⟨{ (NativeContextLoader.loadedStart (machine consumer) input
      (packet true output payload) memory).config with channels := channels }, memory⟩ :
      World 4 (Fin 3 ⊕ S) Unit P input) =
      point (channels := channels) consumer input (packet true output payload) memory
        (some (.inl 0)) 0 [] := by
    rw [initial_point]
    rfl
  rw [hi, NativeUnboundedExecution.terminal, StoppedProcess.terminal_step,
    check_stop, PMF.pure_bind]
  change NativeUnboundedExecution.terminal (machine consumer) env _ = _
  exact frame_terminal consumer env input output payload memory channels [true] []

private theorem check_go {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input output payload : List Bool) (memory : Memory Unit P)
    (channels : Unit → Channel Bool) :
    NativeOpenExecution.step (machine consumer) env
      (point (channels := channels) consumer input (packet false output payload) memory
        (some (.inl 0)) 0 []) =
      PMF.pure (NativeSequential.right (First := Fin 3)
        (⟨{ (NativeContextLoader.loadedStart consumer input
          (packet false output payload) memory).config with channels := channels }, memory⟩)) := by
  have hs : (point (channels := channels) consumer input (packet false output payload) memory
      (some (.inl 0)) 0 []).config.tapes.workTapeSymbols 0 = some false := by
    simp [point, packet, Cfg.workTapeSymbols, tapeOfList_zero]
  simp only [point] at hs
  simp only [NativeOpenExecution.step, point, machine, hs, ↓reduceIte, PMF.bind_const]
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World 4 (Fin 3 ⊕ S) Unit P input))
  apply Config.ext
  · refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · simp [NativeContextLoader.loadedStart, Sequential.right,
        Cfg.mapState, Config.step, Action.apply, wordsCfg]
    · funext i; fin_cases i <;>
        simp [NativeContextLoader.loadedStart, Sequential.right,
          Cfg.mapState, Config.step, Action.apply, wordsCfg]
    · funext i; fin_cases i <;>
        simp [NativeContextLoader.loadedStart, Sequential.right,
          Cfg.mapState, Config.step, Action.apply, wordsCfg]
  · simp [Config.step, Sequential.right]

/-- The false guard dispatches to actual consumer code on unchanged native storage.
Its unbounded response-dependent execution, divergence and resource law are retained. -/
theorem terminal_go {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input output payload : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (machine consumer) env
      (NativeContextLoader.loadedStart (machine consumer) input
        (packet false output payload) memory) =
      (NativeUnboundedExecution.terminal consumer env
        (NativeContextLoader.loadedStart consumer input (packet false output payload) memory)).map
        (Option.map (NativeSequential.right (First := Fin 3))) := by
  rw [initial_point, NativeUnboundedExecution.terminal, StoppedProcess.terminal_step,
    check_go, PMF.pure_bind]
  exact terminal_run consumer env _

/-- The guard composed with the concrete runtime carrier. True means no oracle
call and exact stored-mask output; false preserves the same two-query joint law.
Only initial stopping is enforced here, not stopping between those two queries. -/
theorem runtime_observation {P : Type} (env : Environment Unit P)
    (input output payload : List Bool) (stop : Bool) (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal (machine NativeRuntimeContext.restoringProgram) env
      (NativeContextLoader.loadedStart (machine NativeRuntimeContext.restoringProgram)
        input (packet stop output payload) memory)).map (Option.map NativeRuntimeContext.observe) =
      if stop then
        PMF.pure (some (⟨output, tapeOfList (packet true output payload),
          (1 + 2 * output.length + 1 : ℕ), fun _ => none, memory⟩ :
            NativeRuntimeContext.Observation P))
      else
        (env ((), input) memory).bind fun (first, next) =>
          let recorded := memory.record ((), input) first next
          let context := packet false output payload ++ frame first.word
          (env ((), context) recorded).map fun (second, last) =>
            some (⟨context ++ second.word, tapeOfList context, 0, fun _ => none,
              recorded.record ((), context) second last⟩ : NativeRuntimeContext.Observation P) := by
  cases stop with
  | false =>
    rw [terminal_go, PMF.map_comp, NativeContextLoader.loaded_runtime]
    have he : (Option.map NativeRuntimeContext.observe ∘
        Option.map (NativeSequential.right (First := Fin 3))) =
        Option.map (NativeRuntimeContext.observe (S :=
          NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕
            (NativeRuntimeContext.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕
              NativeQueryAll.Control) ⊕ RewindState ⊕ MarkWorkState)
          (P := P) (input := input)) := by
      funext value
      cases value <;> rfl
    rw [he, NativeRuntimeContext.restoring_program_observation]
    rfl
  | true =>
    rw [terminal_stop, PMF.pure_map]
    rfl

/-- Live dispatch preserves actual response channels as well as ordinary storage.
The consumer may query again using the same shared hidden oracle state. -/
theorem terminal_go_channels {S P : Type} (consumer : MultiTapePTM 4 Bool S Unit)
    (env : Environment Unit P) (input output payload : List Bool) (memory : Memory Unit P)
    (channels : Unit → Channel Bool) :
    NativeUnboundedExecution.terminal (machine consumer) env
      ⟨{ (NativeContextLoader.loadedStart (machine consumer) input
        (packet false output payload) memory).config with channels := channels }, memory⟩ =
      (NativeUnboundedExecution.terminal consumer env
        ⟨{ (NativeContextLoader.loadedStart consumer input
          (packet false output payload) memory).config with channels := channels }, memory⟩).map
          (Option.map (NativeSequential.right (First := Fin 3))) := by
  have hi : (⟨{ (NativeContextLoader.loadedStart (machine consumer) input
      (packet false output payload) memory).config with channels := channels }, memory⟩ :
      World 4 (Fin 3 ⊕ S) Unit P input) =
      point (channels := channels) consumer input (packet false output payload) memory
        (some (.inl 0)) 0 [] := by
    rw [initial_point]
    rfl
  rw [hi, NativeUnboundedExecution.terminal, StoppedProcess.terminal_step,
    check_go, PMF.pure_bind]
  exact terminal_run consumer env _

end Cslib.Probability.NativeStopGuard
