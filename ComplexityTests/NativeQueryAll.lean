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

private def metadataReceipt (value : ℕ) : Exchange 3 :=
  observe ComplexityTests.ConcurrentBatch.limits 8 ComplexityTests.NativeBatchPolicy.first
    (NativeBatchMetadata.metadataPaths value)

private theorem metadata_report (value : ℕ) : (metadataReceipt value).report =
    ![some (some [true], value + 1), some (some [true], value + 1), none] := by
  funext i
  fin_cases i <;> norm_num [metadataReceipt, observe, NativeBatchMetadata.metadataPaths,
    ComplexityTests.NativeBatchPolicy.first, ComplexityTests.ConcurrentBatch.limits,
    CallTrace.report, CallTrace.response, CallTrace.stop]

private theorem metadata_word_length (value : ℕ) :
    Nat.size (value + 1) ≤ (replyOf (metadataReceipt value)).word.length := by
  change Nat.size (value + 1) ≤ (encodeReport (metadataReceipt value).report).length
  rw [metadata_report]
  simp only [encodeReport, encodeSlots, Matrix.cons_val_zero, Option.map_some, encodeCall,
    List.length_cons, List.length_append, Kolmogorov.length_selfDelimitingCode]
  simp [← Nat.size_eq_bits_len]
  omega

private theorem metadata_supported (value : ℕ) :
    (replyOf (metadataReceipt value),
      commit NativeBatchMetadata.start.memory.privateState (metadataReceipt value) value) ∈
      (environment ComplexityTests.ConcurrentBatch.limits NativeBatchMetadata.sample
        ((), encodeBatch ComplexityTests.NativeBatchPolicy.first)
        NativeBatchMetadata.start.memory).support := by
  have ha : admit ComplexityTests.ConcurrentBatch.limits
      NativeBatchMetadata.start.memory.privateState
      (encodeBatch ComplexityTests.NativeBatchPolicy.first) =
        some ComplexityTests.NativeBatchPolicy.first := by
    simp [admit, decodeBatch_encode, NativeBatchMetadata.start,
      ConcurrentBatch.initial, ComplexityTests.ConcurrentBatch.limits]
  change _ ∈ (serve _ _ _ _).support
  rw [serve_accepted _ _ _ _ _ ha]
  simp only [NativeBatchMetadata.sample, NativeBatchMetadata.start,
    ConcurrentBatch.initial, ite_true, PMF.map_comp]
  refine (PMF.mem_support_map_iff _ _ _).mpr
    ⟨value, NativeBatchMetadata.metadata_support value, ?_⟩
  simp only [Function.comp_apply, tsub_zero]
  rfl

/-- A single fixed actual guarded source has positively supported concurrent
invoice packets beyond every proposed output-copying clock. This does not deny
that a query instruction installs the complete word on its answer channel. -/
theorem source_unbounded_reply (fuel : ℕ) :
    ∃ reply privateState,
      (reply, privateState) ∈
        (environment ComplexityTests.ConcurrentBatch.limits NativeBatchMetadata.sample
          ((), encodeBatch ComplexityTests.NativeBatchPolicy.first)
          NativeBatchMetadata.start.memory).support ∧ fuel < reply.word.length := by
  refine ⟨_, _, metadata_supported (2 ^ fuel), ?_⟩
  have hs := Nat.size_le_size (Nat.le_add_right (2 ^ fuel) 1)
  rw [Nat.size_pow] at hs
  have hl := metadata_word_length (2 ^ fuel)
  omega

/-- Unbounded invoice packets still contain the actual full-cover proposals;
the obstruction does not come from invalid masks or a vacuous success model. -/
example (value : ℕ) :
    NativeRetention.Packets.families 3 1 (replyOf (metadataReceipt value)).word = [[0], [0]] := by
  change NativeRetention.Packets.families 3 1 (encodeReport (metadataReceipt value).report) = _
  rw [NativeRetention.Packets.families_report, metadata_report]
  norm_num [proposals, decodeFamily, NativeRetention.sourceIndices, List.ofFn_succ]
  decide

/-- On explicit nonempty rational incidence/certificate data, those same raw
packets really compute a completed retained cover, rather than only valid masks. -/
example (value : ℕ) : NativeRetention.Packets.decision
    ⟨⟨[[0]], [1], [1], 1, []⟩, 3, [(replyOf (metadataReceipt value)).word]⟩ = (true, [true]) := by
  have hf : NativeRetention.Packets.families 3 1 (replyOf (metadataReceipt value)).word =
      [[0], [0]] := by
    change NativeRetention.Packets.families 3 1 (encodeReport (metadataReceipt value).report) = _
    rw [NativeRetention.Packets.families_report, metadata_report]
    norm_num [proposals, decodeFamily, NativeRetention.sourceIndices, List.ofFn_succ]
    decide
  simp only [NativeRetention.Packets.decision, NativeRetention.Packets.assemble,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil, hf]
  norm_num [NativeRetention.complete, NativeRetention.output, NativeRetention.retain,
    NativeRetention.step, NativeRetention.certified, NativeRetention.newly,
    NativeRetention.covered, NativeRetention.normalize, NativeRetention.population,
    NativeRetention.ground, NativeRetention.cost, NativeRetention.price, List.range_succ]

/-- The existing actual unbounded native reader realizes supported reports beyond
each proposed finite clock, together with their original oracle memory. -/
example (fuel : ℕ) : ∃ final,
    some final ∈ (NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0)
      (environment ComplexityTests.ConcurrentBatch.limits NativeBatchMetadata.sample)
      (NativeQueryAll.start () 0 (encodeBatch ComplexityTests.NativeBatchPolicy.first)
        NativeBatchMetadata.start.memory)).support ∧ fuel < final.config.tapes.output.length := by
  obtain ⟨reply, privateState, hs, hl⟩ := source_unbounded_reply fuel
  rw [NativeQueryAll.terminal_query]
  exact ⟨_, (PMF.mem_support_map_iff _ _ _).mpr ⟨(reply, privateState), hs, rfl⟩, hl⟩

/-- No native competitor emits this exact *joint source word/memory law* at a fixed clock,
even though the existing actual full-reply reader terminates with that law in the
unbounded semantics. This is the concrete obstruction to the clocked loop route. -/
example {tapes : ℕ} {Controls : Type} (competitor : MultiTapePTM tapes Bool Controls Unit)
    (fuel : ℕ) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (handler (environment ComplexityTests.ConcurrentBatch.limits NativeBatchMetadata.sample)))
      (competitor.runOracle fuel (encodeBatch ComplexityTests.NativeBatchPolicy.first))).run
      NativeBatchMetadata.start.memory) ≠
        handler (environment ComplexityTests.ConcurrentBatch.limits NativeBatchMetadata.sample)
          ((), encodeBatch ComplexityTests.NativeBatchPolicy.first)
          NativeBatchMetadata.start.memory := by
  obtain ⟨reply, privateState, hs, hl⟩ := source_unbounded_reply fuel
  exact NativeQueryAll.clocked_ne_query () _ competitor _ _ _ fuel reply privateState hs hl

/-- The full reader phase cannot supply the `ComputesTidily` premise required by
existing tidy composition and iteration, at any input-only instruction clock. -/
example {tapes : ℕ} {Controls : Type} (competitor : MultiTapePTM tapes Bool Controls Unit)
    (input : Word) (fuel : ℕ) :
    ¬ competitor.ComputesTidily input fuel
      (ProbOracleComp.query (spec := fun _ : Unit × Word => Word)
        ((), encodeBatch ComplexityTests.NativeBatchPolicy.first)) := by
  exact NativeQueryAll.not_computesTidily_query () competitor input _ fuel

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
