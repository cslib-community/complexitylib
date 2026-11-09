/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeStopGuard
public import CslibFrontier.Computability.Probabilistic.NativeReplyContext
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Executed native context guards with additional work tapes

The stopping branch is the proved four-tape frame reader, embedded without changing
its instructions. Only the live branch enters the actual wider consumer. Branch
selection reads the stored flag before any consumer instruction or oracle call.
This supplies actual guarded composition, not a complete adaptive selector.

## Main results

* `terminal_live`: the live branch has the actual consumer law.
* `terminal_stop_extra`: the stopping reader emits its stored frame without
  entering the consumer or changing the shared oracle ledger.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeGuardedContext
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution

/-- Dispatch, execution of the existing stopping reader, or execution of the live consumer. -/
inductive Control (S : Type) where
  | check
  | stop (state : Fin 3 ⊕ Unit)
  | run (state : S)
  deriving DecidableEq

instance {S : Type} [Finite S] : Finite (Control S) :=
  Finite.of_injective (fun state : Control S =>
    (match state with
      | .check => none
      | .stop q => some (.inl q)
      | .run q => some (.inr q) : Option ((Fin 3 ⊕ Unit) ⊕ S))) (by
        intro a b h; cases a <;> cases b <;> simp_all)

private def halt : MultiTapePTM 4 Bool Unit Unit where
  initial := ()
  tr _ _ _ _ _ := .step ⟨0, fun _ => (none, 0), none, none⟩
    (fun _ => none) (fun _ => 0)

private def stopper := NativeStopGuard.machine halt

/-- One native dispatch instruction selects the existing guard or the wider
consumer. No scheduler, successful result or native representation law is supplied. -/
def machine {k : ℕ} {S : Type} (consumer : MultiTapePTM (4 + k) Bool S Unit) :
    MultiTapePTM (4 + k) Bool (Control S) Unit where
  initial := .check
  tr state input work answer bit := match state with
    | .check => .step
        ⟨0, fun _ => (none, 0), none,
          some (if work 0 = some false then .run consumer.initial else .stop stopper.initial)⟩
        (fun _ => none) (fun _ => 0)
    | .stop q => Action.mapState Control.stop
        ((stopper.extendTapes (Fin.castAddEmb k)).tr q input work answer bit)
    | .run q => Action.mapState Control.run (consumer.tr q input work answer bit)

private theorem step_live {k : ℕ} {S P : Type}
    (consumer : MultiTapePTM (4 + k) Bool S Unit) (env : Environment Unit P)
    (input output payload : List Bool) (memory : Memory Unit P) :
    NativeOpenExecution.step (machine consumer) env
      (NativeContextLoader.loadedStart (machine consumer) input
        (NativeStopGuard.packet false output payload) memory) =
      PMF.pure (NativeSequential.mapControl Control.run
        (NativeContextLoader.loadedStart consumer input
          (NativeStopGuard.packet false output payload) memory)) := by
  have hs : (NativeContextLoader.loadedStart (machine consumer) input
      (NativeStopGuard.packet false output payload) memory).config.tapes.workTapeSymbols 0 =
      some false := by
    simp [NativeContextLoader.loadedStart, wordsCfg, Cfg.workTapeSymbols,
      NativeStopGuard.packet, tapeOfList_zero]
  simp only [NativeContextLoader.loadedStart, wordsCfg, machine] at hs ⊢
  simp only [NativeOpenExecution.step, hs, ↓reduceIte, PMF.bind_const]
  congr 1

/-- A live flag enters the actual wider consumer on the retained native storage.
Its arbitrary unbounded behavior, divergence and joint resource ledger are preserved. -/
theorem terminal_live {k : ℕ} {S P : Type}
    (consumer : MultiTapePTM (4 + k) Bool S Unit) (env : Environment Unit P)
    (input output payload : List Bool) (memory : Memory Unit P) :
    NativeUnboundedExecution.terminal (machine consumer) env
      (NativeContextLoader.loadedStart (machine consumer) input
        (NativeStopGuard.packet false output payload) memory) =
      (NativeUnboundedExecution.terminal consumer env
        (NativeContextLoader.loadedStart consumer input
          (NativeStopGuard.packet false output payload) memory)).map
        (Option.map (NativeSequential.mapControl Control.run)) := by
  rw [NativeUnboundedExecution.terminal, StoppedProcess.terminal_step,
    step_live, PMF.pure_bind]
  exact NativeSequential.terminal_mapControl consumer (machine consumer) Control.run
    (fun _ _ _ _ _ => rfl) env _

private theorem step_stop {k : ℕ} {S P : Type}
    (consumer : MultiTapePTM (4 + k) Bool S Unit) (env : Environment Unit P)
    (input output payload : List Bool) (memory : Memory Unit P) :
    NativeOpenExecution.step (machine consumer) env
      (NativeContextLoader.loadedStart (machine consumer) input
        (NativeStopGuard.packet true output payload) memory) =
      PMF.pure (NativeSequential.mapControl Control.stop
        (NativeContextLoader.extendWorld k
          (NativeContextLoader.loadedStart stopper input
            (NativeStopGuard.packet true output payload) memory))) := by
  rw [NativeContextLoader.loaded_embed]
  have hs : (NativeContextLoader.loadedStart (machine consumer) input
      (NativeStopGuard.packet true output payload) memory).config.tapes.workTapeSymbols 0 =
      some true := by
    simp [NativeContextLoader.loadedStart, wordsCfg, Cfg.workTapeSymbols,
      NativeStopGuard.packet, tapeOfList_zero]
  simp only [NativeContextLoader.loadedStart, wordsCfg, machine] at hs ⊢
  simp only [NativeOpenExecution.step, hs, PMF.bind_const]
  congr 1

/-- Stopping emits the actual framed mask and makes no oracle call. Every extra
consumer tape remains blank and the entire previous resource ledger is unchanged. -/
theorem terminal_stop_extra {k : ℕ} {S P : Type}
    (consumer : MultiTapePTM (4 + k) Bool S Unit) (env : Environment Unit P)
    (input output payload : List Bool) (memory : Memory Unit P) (i : Fin k) :
    (NativeUnboundedExecution.terminal (machine consumer) env
      (NativeContextLoader.loadedStart (machine consumer) input
        (NativeStopGuard.packet true output payload) memory)).map
        (Option.map (NativeReplyContext.observe (Fin.natAdd 4 i))) =
      PMF.pure (some (⟨fun _ => none, output, memory⟩ : NativeReplyContext.Observation P)) := by
  rw [NativeUnboundedExecution.terminal, StoppedProcess.terminal_step,
    step_stop, PMF.pure_bind]
  change (NativeUnboundedExecution.terminal _ env _).map _ = _
  have hx := NativeSequential.terminal_embedStorage (Fin.castAddEmb k) stopper env
    (NativeContextLoader.loadedStart stopper input
      (NativeStopGuard.packet true output payload) memory)
  change NativeUnboundedExecution.terminal _ _ (NativeContextLoader.extendWorld k _) =
    (NativeUnboundedExecution.terminal _ _ _).map
      (Option.map (NativeContextLoader.extendWorld k)) at hx
  rw [NativeSequential.terminal_mapControl
    (stopper.extendTapes (Fin.castAddEmb k)) (machine consumer) Control.stop
    (fun _ _ _ _ _ => rfl), hx,
    show stopper = NativeStopGuard.machine halt from rfl,
    NativeStopGuard.terminal_stop, PMF.map_comp, PMF.pure_map]
  have hn : Fin.natAdd 4 i ∉ Set.range (Fin.castAddEmb k : Fin 4 ↪ Fin (4 + k)) := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 4 + i.val at hv
    omega
  simp [NativeSequential.mapControl, NativeContextLoader.extendWorld,
    NativeReplyContext.observe, Config.mapState, Cfg.mapState, Config.embed, MultiTapeTM.embed,
    partialInv_eq_none _ hn, NativeStopGuard.stopped]

end Cslib.Probability.NativeGuardedContext
