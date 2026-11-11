/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.RuntimeControl
public import CslibFrontier.Computability.Probabilistic.NativeStopGuard
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Executed post-response dispatch of the native runtime controller

The actual full-reader/local-updater is followed by the native guard, on its
computed packet and actual live answer channels. Stopping emits the stored mask;
a live packet enters a silent terminal continuation. This closes post-response
final emission for one transaction, not repeated feedback or source batch admission.
Allotments are reservations, not observed physical deadlines. The source model is
[Wang2027], pp. 4--6, Theorem 5 p. 12/Appendix A.5 p. 16.

## Main results

* `exists_native_phase`: actual query/update/dispatch law, with joint oracle resources.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.FinalizedResponse
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

private def halt : MultiTapePTM 4 Bool Unit Unit where
  initial := ()
  tr _ _ _ _ _ := .step ⟨0, fun _ => (none, 0), none, none⟩
    (fun _ => none) (fun _ => 0)

private theorem halt_terminal {P : Type} (env : Environment Unit P)
    (input word : List Bool) (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal halt env
      (NativeReplyContext.wordWorld input (some ())
        (Function.update (fun _ => []) 0 word) channels memory) =
      PMF.pure (some (NativeReplyContext.wordWorld input (S := Unit) none
        (Function.update (fun _ => []) 0 word) channels memory)) := by
  rw [NativeUnboundedExecution.terminal, StoppedProcess.terminal_step]
  have hs : NativeOpenExecution.step halt env
      (NativeReplyContext.wordWorld input (some ())
        (Function.update (fun _ => []) 0 word) channels memory) =
      PMF.pure (NativeReplyContext.wordWorld input (S := Unit) none
        (Function.update (fun _ => []) 0 word) channels memory) := by
    simp only [NativeOpenExecution.step, NativeReplyContext.wordWorld, wordsCfg,
      halt, PMF.bind_const]
    congr 1
    apply congrArg (fun cfg => (⟨cfg, memory⟩ : World 4 Unit Unit P input))
    apply Config.ext
    · simp [Config.step, Action.apply]
    · simp [Config.step]
  rw [hs, PMF.pure_bind]
  exact StoppedProcess.terminal_halted _ _ (NativeUnboundedExecution.step_halted _ _) _ rfl

private theorem guard_terminal {width : ℕ} [NeZero width] {P : Type}
    (e : Fin 4 ↪ Fin width) (he : e 0 = 0)
    (env : Environment Unit P) (input : List Bool) (state : RuntimeControl.State)
    (channels : Unit → Channel Bool) (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal ((NativeStopGuard.machine halt).extendTapes e) env
      (NativeReplyContext.wordWorld input (some (NativeStopGuard.machine halt).initial)
        (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory)).map
        (Option.map (NativeReplyContext.observe 0)) =
      PMF.pure (some (⟨tapeOfList (RuntimeControl.packet state),
        if RuntimeControl.stopped state then RuntimeControl.result state else [], memory⟩ :
          NativeReplyContext.Observation P)) := by
  rw [← NativeReplyContext.wordWorld_embed_zero e he,
    NativeSequential.terminal_embedStorage, PMF.map_comp]
  trans (NativeUnboundedExecution.terminal (NativeStopGuard.machine halt) env
    (NativeReplyContext.wordWorld input (some (NativeStopGuard.machine halt).initial)
      (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory)).map
      (Option.map (NativeReplyContext.observe 0))
  · congr 1
    funext result
    cases result with
    | none => rfl
    | some world =>
      rw [← he]
      exact congrArg some (NativeReplyContext.observe_embedStorage 0 e world)
  · have hi : NativeReplyContext.wordWorld input (some (NativeStopGuard.machine halt).initial)
        (Function.update (fun _ => []) 0 (RuntimeControl.packet state)) channels memory =
        (⟨{ (NativeContextLoader.loadedStart (NativeStopGuard.machine halt) input
          (RuntimeControl.packet state) memory).config with channels := channels }, memory⟩ :
            World 4 _ Unit P input) := rfl
    rw [hi]
    cases hs : RuntimeControl.stopped state with
    | true =>
      simp only [RuntimeControl.packet, hs, ↓reduceIte]
      rw [NativeStopGuard.terminal_stop_channels, PMF.pure_map]
      simp [NativeReplyContext.observe, NativeStopGuard.stopped]
    | false =>
      simp only [RuntimeControl.packet, hs, Bool.false_eq_true, ↓reduceIte]
      rw [NativeStopGuard.terminal_go_channels, PMF.map_comp]
      have hc : (⟨{ (NativeContextLoader.loadedStart halt input
          (NativeStopGuard.packet false (RuntimeControl.result state)
            (frame (RuntimeControl.encoding state))) memory).config with channels := channels },
          memory⟩ : World 4 Unit Unit P input) =
        NativeReplyContext.wordWorld input (some ())
          (Function.update (fun _ => []) 0
            (NativeStopGuard.packet false (RuntimeControl.result state)
              (frame (RuntimeControl.encoding state)))) channels memory := rfl
      rw [hc, halt_terminal, PMF.pure_map]
      rfl

/-- The same concrete native program handles every runtime State, full report and
hidden correlated source. This entry unconditionally issues one query; the
`GuardedStartup` composition supplies its initial no-query guard. It executes the
new packet before terminating. On a live flag it stops silently, without restarting. -/
theorem exists_native_phase :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (program : MultiTapePTM ((3 + k) + 2) Bool S Unit),
      ∀ (P : Type) (env : Environment Unit P) (state : RuntimeControl.State)
        (memory : Memory Unit P),
        (NativeUnboundedExecution.terminal program env
          ⟨program.initialConfig (frame (RuntimeControl.encoding state)), memory⟩).map
          (Option.map (NativeReplyContext.observe 0)) =
        (env ((), frame (RuntimeControl.encoding state)) memory).map fun (reply, next) =>
          let updated := RuntimeControl.afterReply state reply.word
          some (⟨tapeOfList (RuntimeControl.packet updated),
            if RuntimeControl.stopped updated then RuntimeControl.result updated else [],
            memory.record ((), frame (RuntimeControl.encoding state)) reply next⟩ :
              NativeReplyContext.Observation P) := by
  obtain ⟨k, S, hS, code, hcode⟩ := RuntimeControl.exists_native_processor
  let width := 3 + (k + 4)
  let e : Fin (3 + k) ↪ Fin width := Fin.castLEEmb (by dsimp [width]; omega)
  let g : Fin 4 ↪ Fin width := Fin.castLEEmb (by dsimp [width]; omega)
  let localProgram := (MultiTapePTM.ofDeterministic (Oracle := Unit) code).extendTapes e
  let guard := (NativeStopGuard.machine halt).extendTapes g
  let continuation := localProgram.seq guard
  let program := NativeReplyContext.loadedMachine continuation
  refine ⟨k + 4, _, inferInstance, program, ?_⟩
  intro P env state memory
  rw [NativeReplyContext.terminal_loaded, PMF.map_bind]
  conv_rhs => rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro pair _
  obtain ⟨reply, next⟩ := pair
  dsimp only
  let request := frame (RuntimeControl.encoding state)
  let channels := (NativeQueryAll.finish (k := width) () request memory reply next).config.channels
  let ledger := memory.record ((), request) reply next
  let start : World (3 + k) S Unit P reply.word :=
    NativeReplyContext.wordWorld reply.word (some code.q₀)
    (Function.update (fun _ => []) 0 request) channels ledger
  have hs : NativeResponseExecution.localStartFrom continuation request memory reply next
      (NativeResponseExecution.Workspace.words (Function.update (fun _ => []) 0 request)) =
      NativeSequential.left guard (NativeSequential.embedStorage e start) := by
    rw [NativeReplyContext.wordWorld_embed_zero e (Fin.ext rfl)]
    rfl
  obtain ⟨time, space, hc⟩ := hcode state reply.word
  have hp := NativeReplyContext.terminal_transform code env reply.word
    (Function.update (fun _ => []) 0 request)
    (Function.update (fun _ => []) 0 (RuntimeControl.process (state, reply.word)))
    channels ledger time space hc
  rw [hs, NativeSequential.terminal_seq, NativeSequential.terminal_embedStorage, hp,
    PMF.pure_map, PMF.pure_bind]
  simp only [Option.map_some]
  rw [PMF.map_comp]
  have hr : NativeSequential.resume guard
      (NativeSequential.embedStorage e (NativeReplyContext.wordWorld reply.word (S := S) none
        (Function.update (fun _ => []) 0 (RuntimeControl.process (state, reply.word)))
        channels ledger)) =
      NativeReplyContext.wordWorld reply.word (some guard.initial)
        (Function.update (fun _ => []) 0 (RuntimeControl.process (state, reply.word)))
        channels ledger := by
    rw [NativeReplyContext.wordWorld_embed_zero e (Fin.ext rfl)]
    rfl
  rw [hr, PMF.map_comp]
  trans (NativeUnboundedExecution.terminal guard env
    (NativeReplyContext.wordWorld reply.word (some guard.initial)
      (Function.update (fun _ => []) 0 (RuntimeControl.process (state, reply.word)))
      channels ledger)).map (Option.map (NativeReplyContext.observe 0))
  · congr 1
    funext result
    cases result <;> rfl
  · exact guard_terminal g (Fin.ext rfl) env reply.word
      (RuntimeControl.afterReply state reply.word) channels ledger

end Cslib.Probability.StochasticOracle.NativeRetention.FinalizedResponse
