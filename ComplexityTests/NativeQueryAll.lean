/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Probabilistic.NativeQueryAll
import ComplexityTests.NativeRetentionSelector
import ComplexityTests.NativeBatchMetadata
import Mathlib.Tactic

/-!
# Actual native full concurrent reports, hidden metadata and divergent continuations

The native reader writes the original preformed request, scans the entire real
concurrent packet, and places it on an actual readable work tape. The same source
private state, cancellation bill and duration accompany the word. A countably
supported unbounded invoice law exercises the absence of a common reply bound.
Native sequencing with a silent infinite loop preserves divergent mass honestly.
The complete adaptive parser/retention/scheduler machine is not constructed here.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeMachine NativeOpenExecution
open StochasticOracle StochasticOracle.ConcurrentBatch
open scoped NNReal ENNReal
namespace ComplexityTests.NativeQueryAll
open ComplexityTests.NativeRetentionSelector (first receiptOne limits sample)

/-- Actual source memory before any batch, carrying the hidden persistent bit. -/
def memory (bit : Bool) : Memory Unit (ServerState 3 Bool) := ⟨ConcurrentBatch.initial bit, []⟩

private theorem serve_first (bit : Bool) :
    environment limits sample ((), encodeBatch first) (memory bit) =
      PMF.pure (replyOf (receiptOne bit),
        commit (ConcurrentBatch.initial bit) (receiptOne bit) bit) := by
  have ha : admit limits (ConcurrentBatch.initial bit) (encodeBatch first) = some first := by
    simp [admit, decodeBatch_encode, ConcurrentBatch.initial, limits]
  change serve limits sample (encodeBatch first) (ConcurrentBatch.initial bit) = _
  rw [serve_accepted limits sample _ _ _ ha]
  simp only [sample, ConcurrentBatch.initial, List.isEmpty_nil, Bool.not_true,
    PMF.pure_map, tsub_zero]
  rfl

/-- The actual native terminal state contains the full packet, not just a family
mask or a bounded prefix. Cancellation and all private state are the same sample. -/
theorem native_first (bit : Bool) :
    NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0)
        (environment limits sample) (NativeQueryAll.start () 0 (encodeBatch first) (memory bit)) =
      PMF.pure (some (NativeQueryAll.finish () (encodeBatch first) (memory bit)
        (replyOf (receiptOne bit))
        (commit (ConcurrentBatch.initial bit) (receiptOne bit) bit))) := by
  rw [NativeQueryAll.terminal_query, serve_first, PMF.pure_map]

/-- The existing native output compiler writes every bit onto a real work tape,
with its head at the end, even though the response is not known when code is built. -/
example (bit : Bool) :
    NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0).outputToTape
        (environment limits sample)
        (⟨(NativeQueryAll.machine () 0).outputToTape.initialConfig (encodeBatch first),
          memory bit⟩ : World 1 NativeQueryAll.Control Unit (ServerState 3 Bool)
            (encodeBatch first)) =
      PMF.pure (some (NativeOutputBuffer.world
        (NativeQueryAll.finish () (encodeBatch first) (memory bit)
          (replyOf (receiptOne bit))
          (commit (ConcurrentBatch.initial bit) (receiptOne bit) bit)))) := by
  rw [NativeQueryAll.buffered_start, NativeOutputBuffer.terminal_buffer,
    native_first, PMF.pure_map]
  rfl

/-- Actual buffered contents, successful and canceled slots, and the accumulated
resources all accompany the same native world. No local input is fabricated. -/
example (bit : Bool) : ∃ w ∈
    (NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0).outputToTape
      (environment limits sample)
      (NativeOutputBuffer.world
        (NativeQueryAll.start () 0 (encodeBatch first) (memory bit)))).support,
    ∃ final, w = some final ∧
      final.config.tapes.workTapes 0 = tapeOfList (replyOf (receiptOne bit)).word ∧
      final.memory.privateState = commit (ConcurrentBatch.initial bit) (receiptOne bit) bit ∧
      tokenBill final.memory.events = (receiptOne bit).tokens ∧
      elapsed final.memory.events = (receiptOne bit).duration := by
  rw [NativeQueryAll.terminal_buffered, serve_first, PMF.pure_map]
  refine ⟨_, (PMF.mem_support_pure_iff _ _).mpr rfl, _, rfl, ?_, rfl, ?_, ?_⟩
  · exact MultiTapeTM.outCfg_workTapes_last _
  · simp [NativeOutputBuffer.world, NativeQueryAll.finish, NativeQueryAll.finishFrom,
      memory, NativeQueryAll.start, Memory.record, tokenBill, replyOf]
  · simp [NativeOutputBuffer.world, NativeQueryAll.finish, NativeQueryAll.finishFrom,
      memory, NativeQueryAll.start, Memory.record, elapsed, replyOf]

/-- Every unbounded latent invoice scale still occurs in the actual native
buffered report, under one fixed geometric hidden-state oracle and one reader. -/
example (value : ℕ) : ∃ final,
    some final ∈ (NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0).outputToTape
      (environment ComplexityTests.ConcurrentBatch.limits NativeBatchMetadata.sample)
      (NativeOutputBuffer.world (NativeQueryAll.start () 0
        (encodeBatch ComplexityTests.NativeBatchPolicy.first)
        NativeBatchMetadata.start.memory))).support ∧
    tokenBill final.memory.events = (2 * (value + 1) : ℕ) := by
  obtain ⟨out, ho, ht⟩ := NativeBatchMetadata.unbounded_invoices value
  rw [NativeQueryAll.terminal_buffered]
  refine ⟨_, (PMF.mem_support_map_iff _ _ _).mpr ⟨out, ho, rfl⟩, ?_⟩
  simpa [NativeOutputBuffer.world, NativeQueryAll.finish, NativeQueryAll.finishFrom,
    NativeQueryAll.start, Memory.record, tokenBill, NativeBatchMetadata.start] using ht

/-- A terminating native continuation that leaves the whole copied packet alone. -/
def stop : MultiTapePTM 0 Bool Unit Unit where
  initial := ()
  tr _ _ _ _ _ := .step
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
    (fun _ => none) (fun _ => 0)

private def stopped {Private : Type} {input : List Bool}
    (w : World 0 Unit Unit Private input) : World 0 Unit Unit Private input :=
  { w with config := { w.config with tapes := { w.config.tapes with state := none } } }

private theorem stop_terminal {Private : Type} {input : List Bool}
    (env : Environment Unit Private) (w : World 0 Unit Unit Private input)
    (hs : w.config.tapes.state = some ()) :
    NativeUnboundedExecution.terminal stop env w = PMF.pure (some (stopped w)) := by
  have he : NativeOpenExecution.step stop env w = PMF.pure (stopped w) := by
    simp only [NativeOpenExecution.step, hs, stop, PMF.bind_const]
    congr 1
    congr 1
    apply Config.ext
    · apply Cfg.ext_zero_tapes
      · rfl
      · simp [Config.step, Action.apply]
      · simp [Config.step, Action.apply]
    · funext op
      simp [Config.step]
  change StoppedProcess.terminal _ _ _ w = _
  rw [StoppedProcess.terminal_step, he, PMF.pure_bind]
  exact StoppedProcess.terminal_halted _ _ _ _ rfl

/-- The real two-phase native program terminates with the full original source
packet, same hidden state and exact cancellation bill after the handoff. -/
example (bit : Bool) :
    NativeUnboundedExecution.terminal ((NativeQueryAll.machine () 0).seq stop)
      (environment limits sample)
      (NativeSequential.left stop (NativeQueryAll.start () 0 (encodeBatch first) (memory bit))) =
    PMF.pure (some (NativeSequential.right (stopped (NativeSequential.resume stop
      (NativeQueryAll.finish () (encodeBatch first) (memory bit) (replyOf (receiptOne bit))
        (commit (ConcurrentBatch.initial bit) (receiptOne bit) bit)))))) := by
  rw [NativeQueryAll.terminal_then () _ stop _ rfl rfl rfl]
  change (environment limits sample ((), encodeBatch first) (memory bit)).bind _ = _
  rw [serve_first, PMF.pure_bind]
  dsimp only
  rw [stop_terminal _ _ rfl, PMF.pure_map]
  rfl

open NativeBatchMetadata (spin)

private theorem spin_step {Private : Type} {input : List Bool}
    (env : Environment Unit Private) (w : World 0 Unit Unit Private input)
    (hs : w.config.tapes.state = some ()) : NativeOpenExecution.step spin env w = PMF.pure w := by
  simp only [NativeOpenExecution.step, hs, spin, PMF.bind_const]
  congr 1
  conv_rhs => rw [show w = ⟨w.config, w.memory⟩ from rfl]
  congr 1
  apply Config.ext
  · apply Cfg.ext_zero_tapes
    · simpa [Config.step, Action.apply] using hs.symm
    · simp [Config.step, Action.apply]
    · simp [Config.step, Action.apply]
  · funext op
    simp [Config.step]

private theorem spin_terminal {Private : Type} {input : List Bool}
    (env : Environment Unit Private) (w : World 0 Unit Unit Private input)
    (hs : w.config.tapes.state = some ()) :
    NativeUnboundedExecution.terminal spin env w = PMF.pure none := by
  have hc (n : ℕ) : ObservedProcess.stateLaw (NativeOpenExecution.step spin env) n w =
      PMF.pure w := by
    induction n with
    | zero => rfl
    | succ n ih => rw [ObservedProcess.stateLaw, ih, PMF.pure_bind, spin_step env w hs]
  apply StoppedProcess.option_ext
  intro next
  change (⨆ n, StoppedProcess.stopped (NativeOpenExecution.step spin env)
      NativeUnboundedExecution.halted n w next) = PMF.pure none (some next)
  simp only [StoppedProcess.stopped, hc]
  by_cases he : next = w
  · subst next
    simp [NativeUnboundedExecution.halted, hs]
  · simp [PMF.pure_apply, he]

/-- Actual compiled sequencing retains silent divergence instead of treating it
as a halted failure. This optional terminal law does not assign a zero prefix bill. -/
example (bit : Bool) :
    NativeUnboundedExecution.terminal ((NativeQueryAll.machine () 0).seq spin)
      (environment limits sample)
      (NativeSequential.left spin (NativeQueryAll.start () 0 (encodeBatch first) (memory bit))) =
        PMF.pure none := by
  rw [NativeQueryAll.terminal_then () _ spin _ rfl rfl rfl]
  have hh (reply : Reply) (state : ServerState 3 Bool) :
      NativeUnboundedExecution.terminal spin (environment limits sample)
        (NativeSequential.resume spin (NativeQueryAll.finishFrom ()
          (NativeQueryAll.start () 0 (encodeBatch first) (memory bit)) reply state)) =
      PMF.pure none := spin_terminal _ _ rfl
  simp only [hh, PMF.pure_map, Option.map_none]
  exact PMF.bind_const _ _

/-- Divergence in the first native phase prevents the continuation from running. -/
example (bit : Bool) :
    NativeUnboundedExecution.terminal (spin.seq (NativeQueryAll.machine () 0))
      (environment limits sample)
      (NativeSequential.left (NativeQueryAll.machine () 0)
        (⟨spin.initialConfig (encodeBatch first), memory bit⟩ :
          World 0 Unit Unit (ServerState 3 Bool) (encodeBatch first))) = PMF.pure none := by
  rw [NativeSequential.terminal_seq, spin_terminal _ _ rfl, PMF.pure_bind]

/-- Empty response packets and empty requests are actual terminating native
transactions, rather than divergence or an implicit successful empty cover. -/
example {Private : Type} (state : Private) :
    NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0)
      (fun _ _ => PMF.pure (⟨[], 7, 3⟩, state))
      (NativeQueryAll.start () 0 [] (⟨state, []⟩ : Memory Unit Private)) =
    PMF.pure (some (NativeQueryAll.finish () [] (⟨state, []⟩ : Memory Unit Private)
      ⟨[], 7, 3⟩ state)) := by
  rw [NativeQueryAll.terminal_query, PMF.pure_map]

end ComplexityTests.NativeQueryAll
