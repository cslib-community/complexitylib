/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontierTests.NativeBatchSingleton
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Shared native singleton packet-writing program

One finite native program writes the two actual batch-request bits, waits for the
real response, and emits the covering singleton mask. Prefix and finalization
laws quantify over arbitrary source-private types, samplers, memory and reply
words. The original deterministic success client and the enriched latent-source
client share this code and its actual instruction proofs.
-/

public section
noncomputable section
namespace CslibFrontierTests.NativeBatchProgram
open Cslib.Probability Turing NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle ConcurrentBatch NativeBatch
open CslibFrontierTests.NativeBatchSingleton (limits batch)
open scoped NNReal ENNReal

/-- Native code writes both request bits, issues the batch and writes a covering result. -/
@[expose] def machine : MultiTapePTM 0 Bool (Fin 4) Unit where
  initial := 0
  tr c _ _ _ _ := if c = 2 then .query () 3 else .step
    { inputTape := 0, workTapes := Fin.elim0,
      output := if c = 3 then some true else none,
      state := if c = 3 then none else some (c + 1) }
    (fun _ => if c = 3 then none else some (decide (c = 0))) (fun _ => 0)

/-- Concrete native tapes, channel buffers and oracle memory for the instruction proof. -/
@[expose] def world {P : Type} (c : Option (Fin 4)) (word answer output : List Bool)
    (memory : Memory Unit (ServerState 1 P)) : World 0 (Fin 4) Unit (ServerState 1 P) [] :=
  ⟨⟨{ Cfg.init 0 [] with state := c, output := output }, fun _ => ⟨word, answer, 0⟩⟩, memory⟩

private theorem writes {P : Type} (memory : Memory Unit (ServerState 1 P))
    (c : Fin 4) (word : List Bool) (hc : c < 2) (bit : Bool) :
    instruction machine (world (some c) word [] [] memory) bit = .local
      (world (some (c + 1)) (word ++ [decide (c = 0)]) [] [] memory) := by
  have h₂ : c ≠ 2 := by omega
  have h₃ : c ≠ 3 := by omega
  simp only [instruction, world, machine, h₂, h₃, ite_false,
    MultiTapeMachine.Config.step, Action.apply, moveInputPos_zero,
    Option.toList_none, List.append_nil, Option.toList_some, SignType.coe_zero, add_zero]
  congr 4 <;> funext i <;> exact Fin.elim0 i

private theorem seek_write {P : Type} (sample : Sampler 1 P)
    (memory : Memory Unit (ServerState 1 P)) (c : Fin 4) (word : List Bool) (hc : c < 2) :
    seekSourceFrom limits sample machine
        (some (.ready (world (some c) word [] [] memory))) =
      seekSourceFrom limits sample machine (some (.ready
        (world (some (c + 1)) (word ++ [decide (c = 0)]) [] [] memory))) := by
  have hready : sourceSilent limits sample machine
      (.ready (world (some c) word [] [] memory)) = PMF.pure (.pending (.local
        (world (some (c + 1)) (word ++ [decide (c = 0)]) [] [] memory))) := by
    simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
      NativeUnboundedExecution.halted, show
        (world (some c) word [] [] memory).config.tapes.state = some c from rfl,
      reduceCtorEq, ite_false,
      phaseStep, Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def]
    simp only [writes memory c word hc]
    exact PMF.map_const _ _
  simp only [seekSourceFrom]
  rw [StoppedProcess.terminal_step (sourceSilent limits sample machine)
    (sourceBoundary limits) (sourceSilent_absorbs limits sample machine), hready,
    PMF.pure_bind, StoppedProcess.terminal_step (sourceSilent limits sample machine)
      (sourceBoundary limits) (sourceSilent_absorbs limits sample machine)]
  simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, phaseStep, dispatch]

/-- Actual native code writes the complete packet before reaching its admitted query boundary. -/
theorem seek_first {P : Type} (sample : Sampler 1 P)
    (memory : Memory Unit (ServerState 1 P))
    (hadmit : admit limits memory.privateState (encodeBatch batch) = some batch) :
    seekSourceFrom limits sample machine (some (.ready (world (some 0) [] [] [] memory))) =
      PMF.pure (some (.pending (.query
        (world (some 2) (encodeBatch batch) [] [] memory) () 3))) := by
  rw [seek_write sample memory 0 [] (by decide)]
  change seekSourceFrom limits sample machine
    (some (.ready (world (some 1) [true] [] [] memory))) = _
  rw [seek_write sample memory 1 [true] (by decide)]
  let queried := world (some 2) (encodeBatch batch) [] [] memory
  change seekSourceFrom limits sample machine (some (.ready queried)) = _
  have hi (bit : Bool) : instruction machine queried bit = .query queried () 3 := rfl
  have hc : queried.config.tapes.state = some 2 := rfl
  have hr : sourceSilent limits sample machine (.ready queried) =
      PMF.pure (.pending (.query queried () 3)) := by
    simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
      NativeUnboundedExecution.halted, hc, reduceCtorEq, ite_false, phaseStep,
      Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def, hi]
    exact PMF.map_const _ _
  simp only [seekSourceFrom]
  rw [StoppedProcess.terminal_step (sourceSilent limits sample machine)
    (sourceBoundary limits) (sourceSilent_absorbs limits sample machine), hr, PMF.pure_bind]
  apply StoppedProcess.terminal_halted
  simpa [sourceBoundary, queried, world] using congrArg Option.isSome hadmit

/-- Arbitrary actual response words are retained while the program writes its covering output. -/
theorem seek_output {P : Type} (sample : Sampler 1 P)
    (memory : Memory Unit (ServerState 1 P)) (answer : List Bool) :
    seekSourceFrom limits sample machine
      (some (.ready (world (some 3) [] answer [] memory))) =
      PMF.pure (some (.ready (world none [] answer [true] memory))) := by
  let received := world (some 3) [] answer [] memory
  let final := world none [] answer [true] memory
  change seekSourceFrom limits sample machine (some (.ready received)) =
    PMF.pure (some (.ready final))
  have hi (bit : Bool) : instruction machine received bit = .local final := by
    simp only [instruction, received, final, world, machine, Fin.isValue]
    norm_num [MultiTapeMachine.Config.step, Action.apply, Cfg.init]
    constructor <;> funext i <;> exact Fin.elim0 i
  have hc : received.config.tapes.state = some 3 := rfl
  have hr : sourceSilent limits sample machine (.ready received) =
      PMF.pure (.pending (.local final)) := by
    simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
      NativeUnboundedExecution.halted, hc, reduceCtorEq, ite_false, phaseStep,
      Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def, hi]
    exact PMF.map_const _ _
  simp only [seekSourceFrom]
  rw [StoppedProcess.terminal_step (sourceSilent limits sample machine)
    (sourceBoundary limits) (sourceSilent_absorbs limits sample machine), hr, PMF.pure_bind,
    StoppedProcess.terminal_step (sourceSilent limits sample machine)
      (sourceBoundary limits) (sourceSilent_absorbs limits sample machine)]
  have hl : sourceSilent limits sample machine (.pending (.local final)) =
      PMF.pure (.ready final) := by
    simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, phaseStep, dispatch]
  rw [hl, PMF.pure_bind]
  exact StoppedProcess.terminal_halted _ _ _ _ rfl

end CslibFrontierTests.NativeBatchProgram
