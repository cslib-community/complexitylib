/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Memory
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Rejected native packets preserve accepted-state transport

An actual pending query submits the malformed empty packet. The guarded protocol
returns its rejection word and appends a zero-charge raw native event, without
changing the accepted source ledger. Native code then commits a halt. Both the
silent step and the unbounded stopping law commute with erasure of a latent Bool
to Unit, even for unrelated source samplers. No accepted response is sampled.
-/

public section
noncomputable section
namespace CslibFrontierTests.NativeBatchMemory
open Cslib.Probability Turing Turing.MultiTapeMachine Turing.MultiTapeTM
open NativeOpenExecution NativeInterface NativeBatch
open Cslib.Probability.StochasticOracle
open Cslib.Probability.StochasticOracle.ConcurrentBatch
open scoped NNReal ENNReal

/-- One available opportunity; malformed packets fail before any source sampling. -/
def limits : Limits 1 := ⟨fun _ => 1, by intro _; norm_num, 1, 1⟩

/-- The named native halt action used by the program and its committed final state. -/
def haltAction : Turing.Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

/-- Submit the existing empty query buffer, then halt after receiving the status word. -/
def machine : MultiTapePTM 0 Bool Bool Unit where
  initial := false
  tr c _ _ _ _ := if c then .step haltAction (fun _ => none) (fun _ => 0)
    else .query () true

/-- Source memory before the rejected transaction. -/
def memory {P : Type} (s : P) : Memory Unit (ServerState 1 P) :=
  ⟨ConcurrentBatch.initial s, []⟩

/-- Actual initial native configuration, whose malformed query buffer is empty. -/
def start {P : Type} (s : P) : World 0 Bool Unit (ServerState 1 P) [] :=
  ⟨machine.initialConfig [], memory s⟩

/-- The actual selected query, before deterministic guarded rejection. -/
def pending {P : Type} (s : P) : Phase 0 Bool Unit (ServerState 1 P) [] :=
  .pending (.query (start s) () true)

/-- Actual native rejection response, with its raw event and unchanged accepted server state. -/
def after {P : Type} (s : P) : World 0 Bool Unit (ServerState 1 P) [] :=
  ⟨(start s).config.receive () true rejection.word,
    (memory s).record ((), []) rejection (memory s).privateState⟩

/-- A committed halt retaining the real rejection event and unchanged accepted ledger. -/
def done {P : Type} (s : P) : World 0 Bool Unit (ServerState 1 P) [] :=
  ⟨(after s).config.step haltAction (fun _ => none) (fun _ => 0), (after s).memory⟩

private theorem malformed {P : Type} (s : P) :
    admit limits (memory s).privateState [] = none := by
  simp [admit, decodeBatch, decodeSlots]

-- This is a real transition-table query, not a supplied abstract selected action.
example {P : Type} (s : P) (bit : Bool) :
    instruction machine (start s) bit = .query (start s) () true := by
  rfl

/-- Rejection adds one actual raw event while leaving every accepted-state field unchanged. -/
theorem raw_rejection {P : Type} (s : P) :
    (after s).memory.events = [⟨(), [], rejection⟩] ∧
      (after s).memory.privateState = ConcurrentBatch.initial s ∧
      (after s).memory.privateState.history = [] ∧
      (after s).memory.privateState.used = ∅ ∧
      (after s).memory.privateState.elapsed = 0 ∧
      tokenBill (after s).memory.events = 0 ∧ elapsed (after s).memory.events = 0 := by
  simp [after, memory, Memory.record, ConcurrentBatch.initial, tokenBill, elapsed, rejection]

private theorem dispatch_rejection {P : Type} (sample : Sampler 1 P) (s : P) :
    dispatch (environment limits sample) (.query (start s) () true) = PMF.pure (after s) := by
  change (serve limits sample [] (memory s).privateState).map _ = _
  rw [serve_rejected limits sample [] _ (malformed s), PMF.pure_map]
  rfl

/-- A pending malformed request is silent at the accepted-batch interface. -/
theorem silent_rejection {P : Type} (sample : Sampler 1 P) (s : P) :
    sourceSilent limits sample machine (pending s) = PMF.pure (.ready (after s)) := by
  have hn : ¬sourceBoundary limits (pending s) := by
    change ¬(admit limits (memory s).privateState []).isSome
    rw [malformed]
    decide
  simp only [sourceSilent, StoppedProcess.beforeBoundary, hn, ite_false]
  change (dispatch (environment limits sample) (.query (start s) () true)).map Phase.ready = _
  rw [dispatch_rejection, PMF.pure_map]

private theorem ready_halt {P : Type} (sample : Sampler 1 P) (s : P) :
    sourceSilent limits sample machine (.ready (after s)) =
      PMF.pure (.pending (.local (done s))) := by
  have hc : (after s).config.tapes.state = some true := rfl
  have hi (bit : Bool) : instruction machine (after s) bit = .local (done s) := by
    rfl
  simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
    NativeUnboundedExecution.halted, hc, reduceCtorEq, ite_false, phaseStep,
    Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def, hi]
  exact PMF.map_const _ _

/-- Actual unbounded selection skips the rejection and reaches the committed halt. -/
theorem seek_halt {P : Type} (sample : Sampler 1 P) (s : P) :
    seekSourceFrom limits sample machine (some (pending s)) =
      PMF.pure (some (.ready (done s))) := by
  simp only [seekSourceFrom]
  rw [StoppedProcess.terminal_step, silent_rejection, PMF.pure_bind,
    StoppedProcess.terminal_step, ready_halt, PMF.pure_bind,
    StoppedProcess.terminal_step]
  have hl : sourceSilent limits sample machine (.pending (.local (done s))) =
      PMF.pure (.ready (done s)) := by
    simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, phaseStep, dispatch]
  rw [hl, PMF.pure_bind]
  exact StoppedProcess.terminal_halted _ _ _ _ rfl

/-- Erase only the latent source bit; raw receipts and all accepted meters stay present. -/
def erase : Memory Unit (ServerState 1 Bool) → Memory Unit (ServerState 1 Unit) :=
  Memory.mapPrivate (ServerState.mapPrivate (fun _ : Bool => ()))

/-- Even unrelated samplers give the transported concrete silent rejection law. -/
example (sample : Sampler 1 Bool) (other : Sampler 1 Unit) (s : Bool) :
    (sourceSilent limits sample machine (pending s)).map (Phase.mapMemory erase) =
      PMF.pure (.ready (after ())) := by
  simp only [erase]
  rw [sourceSilent_mapPrivate limits sample other machine (fun _ : Bool => ())]
  change sourceSilent limits other machine (pending ()) = _
  exact silent_rejection other ()

/-- Complete real stopping laws commute across the latent-state types without sampler coupling. -/
theorem seek_unrelated (sample : Sampler 1 Bool) (other : Sampler 1 Unit) (s : Bool) :
    (seekSourceFrom limits sample machine (some (pending s))).map
      (Option.map (Phase.mapMemory erase)) = PMF.pure (some (.ready (done ()))) := by
  simp only [erase]
  rw [seekSourceFrom_mapPrivate limits sample other machine (fun _ : Bool => ())]
  change seekSourceFrom limits other machine (some (pending ())) = _
  exact seek_halt other ()

/-- The selected signal contains no accepted batch even though its raw memory logs rejection. -/
example (s : Bool) :
    sourceSignal limits (some (.ready (done s))) = some ([], none) ∧
      sourceSignal limits ((some (.ready (done s))).map (Phase.mapMemory erase)) =
        some ([], none) := by
  simp only [erase]
  rw [sourceSignal_mapPrivate limits (fun _ : Bool => ())]
  constructor <;> rfl

end CslibFrontierTests.NativeBatchMemory
