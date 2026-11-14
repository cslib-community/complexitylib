/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Probabilistic.NativeBatch.RecordedObservation
import CslibFrontier.Computability.Probabilistic.NativeResponseExecution
import CslibFrontierTests.NativeBatchSuccess
import Mathlib.Tactic

/-!
# Actual private-coin retention after a real encoded batch

The full native response reader issues the one-opportunity packet, buffers its
actual reply and runs a native continuation. That continuation flips a private
coin after the reply and writes either the singleton mask or the empty mask.
Both outcomes keep the same actual receipt, invoice and physical duration.
The posterior observation law is derived from execution, rather than supplied
as a machine representation assumption. Two epochs finalize one issued call.
-/

noncomputable section
namespace CslibFrontierTests.NativeRecordedRetention
open Cslib Cslib.Probability Turing Turing.MultiTapeMachine Turing.MultiTapeTM
open NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle
open Cslib.Probability.StochasticOracle.ConcurrentBatch
open Cslib.Probability.NativeBatch
open NativeBatchSuccess (limits sample batch receipt)
open scoped ENNReal NNReal

/-- One actual private-coin instruction, executed only after the response handoff. -/
def coin : MultiTapePTM 0 Bool Unit Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    (fun _ => none) (fun _ => 0)

private def action (bit : Bool) : Turing.Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }

private def finish {word : List Bool} (w : World 0 Unit Unit (ServerState 1 Unit) word)
    (bit : Bool) : World 0 Unit Unit (ServerState 1 Unit) word :=
  ⟨w.config.step (action bit) (fun _ => none) (fun _ => 0), w.memory⟩

private theorem terminal_coin {word : List Bool}
    (w : World 0 Unit Unit (ServerState 1 Unit) word)
    (hw : w.config.tapes.state = some ()) :
    NativeUnboundedExecution.terminal coin (environment limits sample) w =
      (PMF.uniformOfFintype Bool).map fun bit => some (finish w bit) := by
  unfold NativeUnboundedExecution.terminal
  rw [StoppedProcess.terminal_step (NativeOpenExecution.step coin (environment limits sample))
    NativeUnboundedExecution.halted (NativeUnboundedExecution.step_halted _ _)]
  have hs : NativeOpenExecution.step coin (environment limits sample) w =
      (PMF.uniformOfFintype Bool).map (finish w) := by
    simp only [NativeOpenExecution.step, hw, coin, PMF.map]
    rfl
  rw [hs, PMF.bind_map]
  apply PMF.bind_congr_on_support
  intro bit _
  exact StoppedProcess.terminal_halted _ _ _ _ rfl

/-- The compiled program writes a genuine query, reads the full reply, then flips the coin. -/
def machine := NativeResponseExecution.machine coin

/-- The runtime input is precisely the real encoded batch, not a supplied response. -/
def start : World 2 (NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ Unit)
    Unit (ServerState 1 Unit) (encodeBatch batch) :=
  ⟨machine.initialConfig (encodeBatch batch), ⟨ConcurrentBatch.initial (), []⟩⟩

private def localWorld := NativeResponseExecution.localStart coin (encodeBatch batch)
  start.memory (replyOf receipt) (commit start.memory.privateState receipt ())

private def done (bit : Bool) :=
  NativeResponseExecution.resultWorld (encodeBatch batch) (finish localWorld bit)

private theorem source_reply :
    environment limits sample ((), encodeBatch batch) start.memory =
      PMF.pure (replyOf receipt, commit start.memory.privateState receipt ()) := by
  have ha : admit limits start.memory.privateState (encodeBatch batch) = some batch := by
    simp [start, admit, decodeBatch_encode, ConcurrentBatch.initial, limits]
  change serve limits sample (encodeBatch batch) start.memory.privateState = _
  rw [serve_accepted limits sample _ _ _ ha]
  have hd : limits.deadline - start.memory.privateState.elapsed = 2 := by
    norm_num [limits, start, ConcurrentBatch.initial]
  simp only [sample, PMF.pure_map, hd]
  rfl

/-- The actual full program's joint native law is the post-response private coin. -/
theorem terminal_law :
    NativeUnboundedExecution.terminal machine (environment limits sample) start =
      (PMF.uniformOfFintype Bool).map fun bit => some (done bit) := by
  change NativeUnboundedExecution.terminal (NativeResponseExecution.machine coin)
    (environment limits sample)
    ⟨(NativeResponseExecution.machine coin).initialConfig (encodeBatch batch), start.memory⟩ = _
  rw [NativeResponseExecution.terminal_machine, source_reply, PMF.pure_bind]
  change (NativeUnboundedExecution.terminal coin (environment limits sample) localWorld).map
    (Option.map (NativeResponseExecution.resultWorld (encodeBatch batch))) = _
  rw [terminal_coin _ rfl, PMF.map_comp]
  rfl

/-- The actual output mask varies while all previously incurred resources are retained. -/
theorem output_resources (bit : Bool) :
    (done bit).config.tapes.output = [bit] ∧
      tokenBill (done bit).memory.events = 2 ∧ elapsed (done bit).memory.events = 1 := by
  cases bit <;>
    norm_num [done, finish, localWorld, NativeResponseExecution.resultWorld,
      NativeResponseExecution.localStart, NativeSequential.right,
      NativeResponseExecution.inputWorld,
      InputFromTape.config, Sequential.right, Config.mapState, Cfg.mapState,
      Config.step, action, Action.apply, coin, start, machine,
      MultiTapeMachine.initialConfig, Cfg.init, Memory.record, tokenBill, elapsed,
      replyOf, receipt, ConcurrentBatch.observe,
      NativeBatchSuccess.path, limits, batch,
      CallTrace.report, CallTrace.response, CallTrace.stop, Exchange.tokens, Exchange.duration,
      active, Finset.sup_const, MultiTapeTM.inCfg]

/-- Both branches receive the same covering singleton; only local retention varies. -/
theorem decoded_retention (bit : Bool) :
    (done bit).memory.privateState.history = [receipt] ∧
      proposals 1 receipt.report = [{0}] ∧
      decodeFamily 1 (done bit).config.tapes.output =
        some (if bit then ({0} : Finset (Fin 1)) else ∅) := by
  refine ⟨rfl, NativeBatchSuccess.receipt_proposals, ?_⟩
  rw [(output_resources bit).1]
  cases bit <;> decide

private def accepted (result : Option (World 2
    (NativeQueryAll.Control ⊕ (MarkWorkState ⊕ RewindWorkState) ⊕ Unit)
    Unit (ServerState 1 Unit) (encodeBatch batch))) : Bool :=
  result.any fun w => (decodeFamily 1 w.config.tapes.output).any fun C =>
    decide (NativeBatchProgress.coverInstance.covered C = NativeBatchProgress.coverInstance.ground)

private theorem accepted_done (bit : Bool) : accepted (some (done bit)) = bit := by
  simp only [accepted, Option.any_some, (decoded_retention bit).2.2]
  cases bit <;> norm_num [PartialCover.Instance.covered, NativeBatchProgress.coverInstance]

/-- Half the actual native outcomes retain the cover, despite certain raw proposal coverage. -/
theorem cover_probability :
    ((NativeUnboundedExecution.terminal machine (environment limits sample) start).map
      accepted) true = 1 / 2 := by
  rw [terminal_law, PMF.map_comp]
  have he : accepted ∘ (fun bit => some (done bit)) = id := by
    funext bit
    exact accepted_done bit
  rw [he, PMF.map_id, PMF.uniformOfFintype_apply]
  norm_num

/-- Actual posterior extraction reproduces the native random output, bill and duration.
The finalization horizon is two although only one source batch is issued. -/
example :
    ((((PMF.seqProcess (fun _ h => RecordedObservation.response limits sample machine start
          (PMF.seqHistory h)) (limits.turns + 1)).map PMF.seqHistory).bind
        (RecordedObservation.output limits sample machine start
          (fun state => state.hidden.map worldOf) (limits.turns + 1))).map
      (Option.map fun w => (w.config.tapes.output, tokenBill w.memory.events,
        elapsed w.memory.events))) =
      (PMF.uniformOfFintype Bool).map (fun bit => some ([bit], (2 : ℝ≥0), (1 : ℝ≥0))) := by
  rw [RecordedObservation.terminal_law limits sample machine start
    (NativeBatch.initial_invariant limits ()), terminal_law, PMF.map_comp]
  apply PMF.map_congr_on_support
  intro bit _
  obtain ⟨ho, hc, ht⟩ := output_resources bit
  simp only [Function.comp_apply, Option.map_some, ho, hc, ht]

end CslibFrontierTests.NativeRecordedRetention
