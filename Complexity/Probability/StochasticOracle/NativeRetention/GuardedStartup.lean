/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.NativeRetention.FinalizedResponse
public import Complexity.Computability.Probabilistic.NativeGuardedContext
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Guarded original-input conversion to runtime control

The original rational instance and startup allowances determine a fresh runtime
state, with empty authenticated history. Native code checks its computed guard
before entering the actual runtime updater on a prepared virtual input.
The newly computed post-response guard is also executed for final emission.
A live response branch still terminates silently; this is not repeated feedback
or a source-admitted selector.
Reservations are not measured physical deadlines [Wang2027], model pp. 4--6.

## Main definitions

* `Input`: original startup data and a reservation allowance, without prepared State.
* `state`: the fresh semantic runtime State computed from that original input.

## Main results

* `exists_guarded_phase`: one actual blank-tape native program executes the initial
  guard, converts the live original input and runs one full query/update/dispatch phase.
  The updated guard is executed for final emission; repeated feedback is not proved.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.GuardedStartup
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

/-- Original instance/startup data plus an integral reservation allowance. -/
structure Input where
  /-- Original rational incidence/price data and turn/opportunity/private-word metadata. -/
  startup : InitialContext.Startup
  /-- Remaining reserved latency units, not observed real time. -/
  allotments : ℕ
  deriving DecidableEq

/-- The original input contains no prepared runtime context or execution witness. -/
@[expose] def encoding : Input ↪ List Bool :=
  ⟨fun data => encPair InitialContext.encoding encUnary (data.startup, data.allotments), by
    intro a b h
    have he := (encPair InitialContext.encoding encUnary).injective h
    cases a; cases b; cases he; rfl⟩

/-- Uniform conversion computes a fresh state; old proposal lists do not become history. -/
@[expose] def state (input : Input) : RuntimeControl.State :=
  RuntimeControl.initial input.startup input.allotments

private theorem fields : ComputableInPolyTime
    (fun data : Input => (data.startup, data.allotments)) encoding
    (encPair InitialContext.encoding encUnary) := .of_eq fun _ => rfl

private theorem computable_state : ComputableInPolyTime state encoding RuntimeControl.encoding := by
  have hf := InitialContext.fields.comp fields.fst'
  have hh : ComputableInPolyTime (fun _ : Input => ([] : List (List Bool)))
      encoding (encList encBits) := .const []
  have hw : ComputableInPolyTime
      (fun p : NativeRetention.Input × ℕ × List (List Bool) =>
        Packets.Work.mk p.1 p.2.1 p.2.2)
      (encPair encInput (encPair encUnary (encList encBits))) Packets.encWork :=
    .of_eq fun _ => rfl
  have hwork := hw.comp (hf.fst'.prod (hf.snd'.snd'.fst'.prod hh))
  have hp : ComputableInPolyTime
      (fun p : Packets.Work × List (List Bool) × List Bool × ℕ × ℕ × ℕ =>
        RuntimeControl.State.mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (encPair Packets.encWork (encPair (encList encBits)
        (encPair encBits (encPair encUnary (encPair encUnary encUnary)))))
      RuntimeControl.encoding := .of_eq fun _ => rfl
  have hout := hp.comp (hwork.prod (hh.prod (hf.snd'.snd'.snd'.prod
    (hf.snd'.fst'.prod (hf.snd'.snd'.fst'.prod fields.snd')))))
  exact hout

private theorem computable_word : ComputableInPolyTime
    (fun input => frame (RuntimeControl.encoding (state input))) encoding encBits := by
  have he : ComputableInPolyTime (fun s : RuntimeControl.State => RuntimeControl.encoding s)
      RuntimeControl.encoding encBits := .of_eq fun _ => rfl
  exact ComputableInPolyTime.frame.comp (he.comp computable_state)

private theorem computable_guard : ComputableInPolyTime
    (fun input => RuntimeControl.packet (state input)) encoding encBits :=
  RuntimeControl.computable_packet.comp computable_state

private def virtualTapes (width : ℕ) : Fin (width + 2) ↪ Fin (4 + width) :=
  ⟨fun i => ⟨if i.val < width then 4 + i.val else if i.val = width then 0 else 1, by
    split_ifs <;> omega⟩, by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    split_ifs at hv <;> omega⟩

private theorem virtual_ordinary (width : ℕ) (i : Fin width) :
    virtualTapes width (i.castAdd 2) = Fin.natAdd 4 i := by
  apply Fin.ext
  change (if i.val < width then 4 + i.val else if i.val = width then 0 else 1) = 4 + i.val
  simp [i.isLt]

private theorem virtual_input (width : ℕ) :
    virtualTapes width (Fin.natAdd width 0) = 0 := by
  apply Fin.ext
  change (if width < width then 4 + width else if width = width then 0 else 1) = 0
  simp

private theorem virtual_flag (width : ℕ) :
    virtualTapes width (Fin.natAdd width 1) = 1 := by
  apply Fin.ext
  change (if width + 1 < width then 4 + (width + 1)
    else if width + 1 = width then 0 else 1) = 1 % (4 + width)
  simp [Nat.mod_eq_of_lt (show 1 < 4 + width by omega)]

private def marked {width : ℕ} {P : Type} (input word : List Bool)
    (memory : Memory Unit P) : World (4 + width) MarkWorkState Unit P input :=
  ⟨⟨⟨none, 1, Function.update
    (Function.update (fun _ => fun _ => none) 0 (tapeOfList word)) 1
      (Function.update (fun _ => none) (-1) (some true)), fun _ => 0, []⟩,
    fun _ => ⟨[], [], 0⟩⟩, memory⟩

private def marker (width : ℕ) : MultiTapePTM (4 + width) Bool MarkWorkState Unit :=
  MultiTapePTM.ofDeterministic
    ((markWork Bool (some true)).extendTapes (tapeEmb (1 : Fin (4 + width))))

private theorem marker_terminal {width : ℕ} {P : Type} (env : Environment Unit P)
    (input word : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (marker width) env
      (NativeContextLoader.loadedStart (marker width) input word memory) =
      PMF.pure (some (marked (width := width) input word memory)) := by
  have h10 : (1 : Fin (4 + width)) ≠ 0 := Fin.ne_of_val_ne (by
    change 1 % (4 + width) ≠ 0
    rw [Nat.mod_eq_of_lt (show 1 < 4 + width by omega)]
    omega)
  apply NativeResponseExecution.terminal_of_clock _ env _
    (marked (width := width) input word memory) 2 ?_ rfl
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((marker width).runOracleConfigFrom 2
      (NativeContextLoader.loadedStart (marker width) input word memory).config)).run
        memory).map _ = _
  unfold marker
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  congr 1
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World (4 + width) MarkWorkState Unit P input))
  apply Config.ext
  · rw [runFrom_tapeEmb]
    have hc : oneTapeCfg (1 : Fin (4 + width))
        (NativeContextLoader.loadedStart (marker width) input word memory).config.tapes =
        (⟨some (markWork Bool (some true)).q₀, 1, fun _ => fun _ => none, fun _ => 0, []⟩ :
          Cfg 1 Bool MarkWorkState input) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i; fin_cases i
        simp [oneTapeCfg, NativeContextLoader.loadedStart, wordsCfg, h10]
      · funext i; fin_cases i
        simp [oneTapeCfg, NativeContextLoader.loadedStart, wordsCfg, h10]
    simp only [marker] at hc
    rw [hc, runFrom_markWork]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      by_cases hi : i = 1
      · subst i; simp [embed_tapeEmb]
      · by_cases hz : i = 0
        · subst i
          simp [embed_tapeEmb, NativeContextLoader.loadedStart, wordsCfg, h10.symm]
        · simp [embed_tapeEmb, hi, NativeContextLoader.loadedStart, wordsCfg, hz]
    · funext i
      simp [embed_tapeEmb, NativeContextLoader.loadedStart, wordsCfg]
  · rfl

private def virtualEntry {width : ℕ} {S P : Type}
    (program : MultiTapePTM width Bool S Unit) (input word : List Bool)
    (memory : Memory Unit P) : World (4 + width) S Unit P input :=
  NativeSequential.embedStorage (virtualTapes width)
    (NativeResponseExecution.inputWorld ⟨program.initialConfig word, memory⟩ input 1)

private theorem marker_resume {width : ℕ} {S P : Type}
    (program : MultiTapePTM width Bool S Unit) (input word : List Bool)
    (memory : Memory Unit P) :
    NativeSequential.resume (program.inputFromTape.extendTapes (virtualTapes width))
      (marked (width := width) input word memory) = virtualEntry program input word memory := by
  have h10 : (1 : Fin (4 + width)) ≠ 0 := Fin.ne_of_val_ne (by
    change 1 % (4 + width) ≠ 0
    rw [Nat.mod_eq_of_lt (show 1 < 4 + width by omega)]
    omega)
  apply congrArg (fun cfg => (⟨cfg, memory⟩ : World (4 + width) S Unit P input))
  apply Config.ext
  · apply Cfg.ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i ∈ Set.range (virtualTapes width)
      · obtain ⟨j, rfl⟩ := hi
        simp only [Sequential.start, marked, Cfg.withState, Config.embed, embed_workTapes_embed]
        cases j using Fin.addCases with
        | left j =>
          rw [virtual_ordinary]
          have hn0 : Fin.natAdd 4 j ≠ 0 := by
            intro h; have hv := congrArg Fin.val h
            change 4 + j.val = 0 at hv
            omega
          have hn1 : Fin.natAdd 4 j ≠ 1 := by
            intro h; have hv := congrArg Fin.val h
            change 4 + j.val = 1 % (4 + width) at hv
            have hm : 1 % (4 + width) = 1 := Nat.mod_eq_of_lt (by omega)
            omega
          simp [hn0, hn1, NativeResponseExecution.inputWorld, InputFromTape.config,
            inCfg, MultiTapeMachine.initialConfig, Cfg.init]
        | right j =>
          fin_cases j
          · simp [virtual_input, NativeResponseExecution.inputWorld,
              InputFromTape.config, inCfg, MultiTapeMachine.initialConfig, Cfg.init, h10.symm]
          · simp [virtual_flag, NativeResponseExecution.inputWorld,
              InputFromTape.config, inCfg, MultiTapeMachine.initialConfig, Cfg.init]
      · have hn0 : i ≠ 0 := by
          intro h; apply hi
          exact ⟨Fin.natAdd width 0, (virtual_input width).trans h.symm⟩
        have hn1 : i ≠ 1 := by
          intro h; apply hi
          exact ⟨Fin.natAdd width 1, (virtual_flag width).trans h.symm⟩
        simp [Sequential.start, marked, Cfg.withState, Config.embed, MultiTapeTM.embed,
          partialInv_eq_none _ hi, hn0, hn1]
    · funext i
      simp only [Sequential.start, marked, Cfg.withState, Config.embed, MultiTapeTM.embed]
      cases partialInv (virtualTapes width) i with
      | none => rfl
      | some j =>
        cases j using Fin.addCases with
        | left j => simp [NativeResponseExecution.inputWorld, InputFromTape.config, inCfg,
            MultiTapeMachine.initialConfig, Cfg.init]
        | right j => fin_cases j <;>
            simp [NativeResponseExecution.inputWorld, InputFromTape.config, inCfg,
              MultiTapeMachine.initialConfig, Cfg.init]
    · rfl
  · rfl

private theorem body_terminal {width : ℕ} [NeZero width] {S P : Type}
    (program : MultiTapePTM width Bool S Unit) (env : Environment Unit P)
    (input word : List Bool) (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal
      ((marker width).seq (program.inputFromTape.extendTapes (virtualTapes width))) env
      (NativeSequential.left (program.inputFromTape.extendTapes (virtualTapes width))
        (NativeContextLoader.loadedStart (marker width) input word memory))).map
      (Option.map (NativeReplyContext.observe (Fin.natAdd 4 (0 : Fin width)))) =
      (NativeUnboundedExecution.terminal program env
        ⟨program.initialConfig word, memory⟩).map
          (Option.map (NativeReplyContext.observe 0)) := by
  rw [NativeSequential.terminal_seq, marker_terminal, PMF.pure_bind]
  dsimp only
  rw [marker_resume, virtualEntry, NativeSequential.terminal_embedStorage,
    NativeResponseExecution.terminal_inputWorld, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  apply congrArg (fun f =>
    (NativeUnboundedExecution.terminal program env ⟨program.initialConfig word, memory⟩).map f)
  funext result
  cases result with
  | none => rfl
  | some world =>
    simp only [Function.comp_apply, Option.map_some]
    congr 1
    change NativeReplyContext.observe (Fin.natAdd 4 (0 : Fin width))
      (NativeSequential.embedStorage (virtualTapes width)
        (NativeResponseExecution.inputWorld world input 1)) = NativeReplyContext.observe 0 world
    rw [show Fin.natAdd 4 (0 : Fin width) =
      virtualTapes width ((0 : Fin width).castAdd 2) from (virtual_ordinary width 0).symm,
      NativeReplyContext.observe_embedStorage,
      NativeReplyContext.observe_inputWorld]

private theorem input_program :
    ∃ (k : ℕ) (_ : 0 < k) (S : Type) (_ : Finite S)
      (program : MultiTapePTM (4 + k) Bool S Unit),
      ∀ (P : Type) (env : Environment Unit P) (data : Input) (memory : Memory Unit P),
        (NativeUnboundedExecution.terminal program env
          ⟨program.initialConfig (encoding data), memory⟩).map
          (Option.map (NativeReplyContext.observe ⟨4, by omega⟩)) =
          (env ((), frame (RuntimeControl.encoding (state data))) memory).map
            fun (reply, next) => some
              (⟨tapeOfList (RuntimeControl.process (state data, reply.word)),
                if RuntimeControl.stopped (RuntimeControl.afterReply (state data) reply.word) then
                  RuntimeControl.result (RuntimeControl.afterReply (state data) reply.word) else [],
                memory.record ((), frame (RuntimeControl.encoding (state data))) reply next⟩ :
                  NativeReplyContext.Observation P) := by
  obtain ⟨k, S, hS, phase, hp⟩ := FinalizedResponse.exists_native_phase
  let width := (3 + k) + 2
  let body := (marker width).seq (phase.inputFromTape.extendTapes (virtualTapes width))
  obtain ⟨scratch, R, hR, loader, hl⟩ :=
    NativeContextLoader.exists_load_then encoding
      (fun data => frame (RuntimeControl.encoding (state data))) computable_word (4 + width)
  let program := (MultiTapePTM.ofDeterministic loader).seq
    (body.extendTapes (Fin.castAddEmb scratch))
  have hresult : ∃ (T : Type) (_ : Finite T)
      (code : MultiTapePTM ((4 + width) + scratch) Bool T Unit),
      ∀ (P : Type) (env : Environment Unit P) (data : Input) (memory : Memory Unit P),
        (NativeUnboundedExecution.terminal code env
          ⟨code.initialConfig (encoding data), memory⟩).map
          (Option.map (NativeReplyContext.observe ⟨4, by dsimp [width]; omega⟩)) =
          (env ((), frame (RuntimeControl.encoding (state data))) memory).map
            fun (reply, next) => some
              (⟨tapeOfList (RuntimeControl.process (state data, reply.word)),
                if RuntimeControl.stopped (RuntimeControl.afterReply (state data) reply.word) then
                  RuntimeControl.result (RuntimeControl.afterReply (state data) reply.word) else [],
                memory.record ((), frame (RuntimeControl.encoding (state data))) reply next⟩ :
                  NativeReplyContext.Observation P) := by
    refine ⟨_, inferInstance, program, ?_⟩
    intro P env data memory
    rw [hl, PMF.map_comp]
    trans (NativeUnboundedExecution.terminal body env
      (NativeContextLoader.loadedStart body (encoding data)
        (frame (RuntimeControl.encoding (state data))) memory)).map
          (Option.map (NativeReplyContext.observe (Fin.natAdd 4 (0 : Fin width))))
    · apply congrArg (fun f =>
        (NativeUnboundedExecution.terminal body env
          (NativeContextLoader.loadedStart body (encoding data)
            (frame (RuntimeControl.encoding (state data))) memory)).map f)
      funext result
      cases result with
      | none => rfl
      | some world =>
        change some (NativeReplyContext.observe
          ((Fin.natAdd 4 (0 : Fin width)).castAdd scratch)
          (NativeSequential.embedStorage (Fin.castAddEmb scratch) world)) = _
        exact congrArg some (NativeReplyContext.observe_embedStorage
          (Fin.natAdd 4 (0 : Fin width)) (Fin.castAddEmb scratch) world)
    · have he : NativeContextLoader.loadedStart body (encoding data)
          (frame (RuntimeControl.encoding (state data))) memory =
        NativeSequential.left (phase.inputFromTape.extendTapes (virtualTapes width))
          (NativeContextLoader.loadedStart (marker width) (encoding data)
            (frame (RuntimeControl.encoding (state data))) memory) := rfl
      rw [he, body_terminal, hp]
      rfl
  obtain ⟨T, hT, code, hcode⟩ := hresult
  let e : Fin ((4 + width) + scratch) ↪ Fin (4 + (width + scratch)) :=
    Fin.castLEEmb (by omega)
  let finalCode := code.extendTapes e
  refine ⟨width + scratch, by dsimp [width]; omega, T, hT, finalCode, ?_⟩
  intro P env data memory
  have hi : (⟨finalCode.initialConfig (encoding data), memory⟩ : World _ T Unit P _) =
      NativeSequential.embedStorage e ⟨code.initialConfig (encoding data), memory⟩ := by
    apply congrArg (fun cfg => (⟨cfg, memory⟩ : World _ T Unit P (encoding data)))
    apply Config.ext
    · apply Cfg.ext
      · rfl
      · simp [Config.embed, MultiTapeTM.embed,
          MultiTapeMachine.initialConfig, Cfg.init]
      · funext i
        simp only [Config.embed,
          MultiTapeMachine.initialConfig, Cfg.init, MultiTapeTM.embed]
        cases partialInv e i <;> rfl
      · funext i
        simp only [Config.embed,
          MultiTapeMachine.initialConfig, Cfg.init, MultiTapeTM.embed]
        cases partialInv e i <;> rfl
      · simp [Config.embed, MultiTapeTM.embed,
          MultiTapeMachine.initialConfig, Cfg.init]
    · rfl
  rw [hi, NativeSequential.terminal_embedStorage, PMF.map_comp]
  trans (NativeUnboundedExecution.terminal code env
    ⟨code.initialConfig (encoding data), memory⟩).map
      (Option.map (NativeReplyContext.observe ⟨4, by dsimp [width]; omega⟩))
  · congr 1
    funext result
    cases result with
    | none => rfl
    | some world =>
      exact congrArg some (NativeReplyContext.observe_embedStorage
        (⟨4, by dsimp [width]; omega⟩ : Fin ((4 + width) + scratch)) e world)
  · exact hcode P env data memory

private theorem clear_then {k : ℕ} {S P : Type}
    (program : MultiTapePTM (4 + k) Bool S Unit) (env : Environment Unit P)
    (input word : List Bool) (memory : Memory Unit P) (i : Fin (4 + k)) :
    let clear := MultiTapePTM.ofDeterministic (Oracle := Unit)
      ((clearWork Bool).extendTapes (tapeEmb (0 : Fin (4 + k))))
    (NativeUnboundedExecution.terminal (clear.seq program) env
      (NativeContextLoader.loadedStart (clear.seq program) input word memory)).map
        (Option.map (NativeReplyContext.observe i)) =
      (NativeUnboundedExecution.terminal program env ⟨program.initialConfig input, memory⟩).map
        (Option.map (NativeReplyContext.observe i)) := by
  let code := (clearWork Bool).extendTapes (tapeEmb (0 : Fin (4 + k)))
  have hc := (transformsTapes_clearWork_tapeEmb (0 : Fin (4 + k)) word).imp
    (P' := fun inp ws => inp = input ∧ ws = Function.update (fun _ => []) 0 word)
    (Q' := fun _ _ ws' emitted => ws' = (fun _ => []) ∧ emitted = [])
    (fun _ ws h => by rw [h.2]; simp)
    (fun _ ws ws' emitted h hh => by
      refine ⟨?_, hh.2⟩
      rw [hh.1, h.2]
      funext j
      by_cases hj : j = 0 <;> simp [hj]) le_rfl le_rfl
  have ht := NativeReplyContext.terminal_transform code env input
    (Function.update (fun _ => []) 0 word) (fun _ => [])
    (fun _ => ⟨[], [], 0⟩) memory _ _ hc
  dsimp only
  have hi : NativeContextLoader.loadedStart
      ((MultiTapePTM.ofDeterministic code).seq program) input word memory =
      NativeSequential.left program
        (NativeReplyContext.wordWorld input (some code.q₀)
          (Function.update (fun _ => []) 0 word) (fun _ => ⟨[], [], 0⟩) memory) := rfl
  rw [hi, NativeSequential.terminal_seq, ht, PMF.pure_bind]
  dsimp only
  have he : NativeSequential.resume program
      (NativeReplyContext.wordWorld input (S := Unit ⊕ RewindWorkState) none
        (fun _ : Fin (4 + k) => []) (fun _ => ⟨[], [], 0⟩) memory) =
      (⟨program.initialConfig input, memory⟩ : World (4 + k) S Unit P input) := by
    apply congrArg (fun cfg => (⟨cfg, memory⟩ : World (4 + k) S Unit P input))
    apply Config.ext
    · apply Cfg.ext
      · simp [Sequential.start, NativeReplyContext.wordWorld,
          wordsCfg, MultiTapeMachine.initialConfig, Cfg.init, Cfg.withState]
      · rfl
      · funext j
        simp [Sequential.start, NativeReplyContext.wordWorld,
          wordsCfg, MultiTapeMachine.initialConfig, Cfg.init, Cfg.withState]
      · rfl
      · rfl
    · rfl
  rw [he, PMF.map_comp]
  congr 1
  funext result
  cases result <;> rfl

/-- One actual native program starts on original instance/startup input with blank
work tapes. Its computed initial guard runs before any query, and only the live
branch converts to the runtime-State ABI, executes the uniform updater and reads
the actual new guard for final emission.
An updated live flag enters a silent terminal continuation; this is not feedback. -/
theorem exists_guarded_phase :
    ∃ (width : ℕ) (S : Type) (_ : Finite S)
      (program : MultiTapePTM width Bool S Unit) (context : Fin width),
      ∀ (P : Type) (env : Environment Unit P) (data : Input) (memory : Memory Unit P),
        (NativeUnboundedExecution.terminal program env
          ⟨program.initialConfig (encoding data), memory⟩).map
          (Option.map (NativeReplyContext.observe context)) =
        if RuntimeControl.stopped (state data) then
          PMF.pure (some (⟨fun _ => none, RuntimeControl.result (state data), memory⟩ :
            NativeReplyContext.Observation P))
        else (env ((), frame (RuntimeControl.encoding (state data))) memory).map
          fun (reply, next) => some
            (⟨tapeOfList (RuntimeControl.process (state data, reply.word)),
                if RuntimeControl.stopped (RuntimeControl.afterReply (state data) reply.word) then
                  RuntimeControl.result (RuntimeControl.afterReply (state data) reply.word) else [],
              memory.record ((), frame (RuntimeControl.encoding (state data))) reply next⟩ :
                NativeReplyContext.Observation P) := by
  obtain ⟨k, hk, S, hS, phase, hp⟩ := input_program
  let clear := MultiTapePTM.ofDeterministic (Oracle := Unit)
    ((clearWork Bool).extendTapes (tapeEmb (0 : Fin (4 + k))))
  let consumer := clear.seq phase
  let guarded := NativeGuardedContext.machine consumer
  obtain ⟨scratch, R, hR, loader, hl⟩ :=
    NativeContextLoader.exists_load_then encoding
      (fun data => RuntimeControl.packet (state data)) computable_guard (4 + k)
  let program := (MultiTapePTM.ofDeterministic loader).seq
    (guarded.extendTapes (Fin.castAddEmb scratch))
  refine ⟨_, _, inferInstance, program, (⟨4, by omega⟩ : Fin (4 + k)).castAdd scratch, ?_⟩
  intro P env data memory
  rw [hl, PMF.map_comp]
  trans (NativeUnboundedExecution.terminal guarded env
    (NativeContextLoader.loadedStart guarded (encoding data)
      (RuntimeControl.packet (state data)) memory)).map
      (Option.map (NativeReplyContext.observe (Fin.natAdd 4 (⟨0, hk⟩ : Fin k))))
  · apply congrArg (fun f =>
      (NativeUnboundedExecution.terminal guarded env
        (NativeContextLoader.loadedStart guarded (encoding data)
          (RuntimeControl.packet (state data)) memory)).map f)
    funext result
    cases result with
    | none => rfl
    | some world =>
      change some (NativeReplyContext.observe
        ((Fin.natAdd 4 (⟨0, hk⟩ : Fin k)).castAdd scratch)
        (NativeSequential.embedStorage (Fin.castAddEmb scratch) world)) = _
      exact congrArg some (NativeReplyContext.observe_embedStorage
        (Fin.natAdd 4 (⟨0, hk⟩ : Fin k)) (Fin.castAddEmb scratch) world)
  · cases hs : RuntimeControl.stopped (state data) with
    | true =>
      simpa only [RuntimeControl.packet, hs, ↓reduceIte] using
        (NativeGuardedContext.terminal_stop_extra consumer env (encoding data)
          (RuntimeControl.result (state data)) (frame (RuntimeControl.encoding (state data)))
          memory (⟨0, hk⟩ : Fin k))
    | false =>
      simp only [RuntimeControl.packet, hs]
      rw [NativeGuardedContext.terminal_live, PMF.map_comp]
      trans (NativeUnboundedExecution.terminal consumer env
        (NativeContextLoader.loadedStart consumer (encoding data)
          (NativeStopGuard.packet false (RuntimeControl.result (state data))
            (frame (RuntimeControl.encoding (state data)))) memory)).map
            (Option.map (NativeReplyContext.observe (Fin.natAdd 4 (⟨0, hk⟩ : Fin k))))
      · congr 1
        funext result
        cases result <;> rfl
      · rw [clear_then]
        have hi : Fin.natAdd 4 (⟨0, hk⟩ : Fin k) = (⟨4, by omega⟩ : Fin (4 + k)) :=
          Fin.ext rfl
        rw [hi, hp]
        simp only [Bool.false_eq_true, ↓reduceIte]


end Cslib.Probability.StochasticOracle.NativeRetention.GuardedStartup
