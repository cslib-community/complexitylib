/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.ResponseExecution
import CslibFrontierTests.NativeQueryAll
import Mathlib.Tactic

/-!
# Actual full-response buffering, native retention and source-mask output

One constructed native program works for both hidden source bits. It issues the
real concurrent batch, copies the complete report, marks/rewinds its real buffer,
processes the raw receipt and emits the actual selected source mask. The canceled
companion remains billed. This checks a fixed-context one-query program, not the
still-missing uniform adaptive restart/scheduler loop.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution
open StochasticOracle NativeRetention ConcurrentBatch
open CslibFrontierTests.NativeRetentionSelector (first receiptOne limits sample partialWord)
namespace CslibFrontierTests.NativeRetentionResponse

/-- Both source candidates cover the nonempty original ground. The native result
must choose the actually proposed candidate, which depends on the hidden bit. -/
private def context : Packets.Work := ⟨⟨[[0], [0]], [1,1], [1], 1, [[99]]⟩, 3, []⟩

private theorem processed (bit : Bool) :
    ResponseExecution.afterReply context (replyOf (receiptOne bit)).word = partialWord bit := by
  have hf : Packets.families 3 2 (replyOf (receiptOne bit)).word =
      [if bit then [0] else [1]] := by
    change Packets.families 3 2 (encodeReport (receiptOne bit).report) = _
    rw [Packets.families_report]
    cases bit <;> norm_num [proposals, receiptOne, observe,
      NativeRetentionSelector.paths, NativeRetentionSelector.first, limits,
      CallTrace.report, CallTrace.response, NativeRetentionSelector.partialWord, decodeFamily,
      List.ofFn_succ, Finset.mem_filter, List.filterMap_cons, List.filterMap_nil,
      sourceIndices] <;> decide
  simp only [ResponseExecution.afterReply, Packets.assemble, context,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil, hf]
  cases bit <;> norm_num [NativeRetentionSelector.partialWord, complete, output, retain,
    NativeRetention.step, certified, newly,
    covered, NativeRetention.normalize, population, ground, cost, price, List.range_succ]

/-- The full native query/processor is constructed, not assumed. Its output and
all source memory, cancellation invoices and maximum latency come from the same
actual response. There is one code witness for both hidden branches. -/
example : ∃ (k : ℕ) (S : Type) (_ : Finite S) (continuation : MultiTapePTM k Bool S Unit),
    ∀ bit : Bool,
    (NativeUnboundedExecution.terminal (NativeResponseExecution.machine continuation)
      (environment limits sample)
      ⟨(NativeResponseExecution.machine continuation).initialConfig (encodeBatch first),
        NativeQueryAll.memory bit⟩).map
          (Option.map fun final => (final.config.tapes.output, final.memory)) =
      PMF.pure (some (partialWord bit,
        (NativeQueryAll.memory bit).record ((), encodeBatch first) (replyOf (receiptOne bit))
          (commit (ConcurrentBatch.initial bit) (receiptOne bit) bit))) := by
  obtain ⟨k, S, hS, continuation, hc⟩ := ResponseExecution.exists_query_retention context
  refine ⟨k, S, hS, continuation, ?_⟩
  intro bit
  rw [hc]
  have ha : admit limits (ConcurrentBatch.initial bit) (encodeBatch first) = some first := by
    simp [admit, decodeBatch_encode, ConcurrentBatch.initial, limits]
  change (serve limits sample (encodeBatch first) (ConcurrentBatch.initial bit)).map _ = _
  rw [serve_accepted limits sample _ _ _ ha]
  simp only [sample, ConcurrentBatch.initial, List.isEmpty_nil, Bool.not_true,
    PMF.pure_map, tsub_zero]
  change PMF.pure (some (ResponseExecution.afterReply context (replyOf (receiptOne bit)).word,
    _)) = _
  rw [processed]
  rfl

private def oneContext : Packets.Work := ⟨⟨[[0]], [1], [1], 1, []⟩, 3, []⟩

private def metadataReceipt (value : ℕ) : Exchange 3 :=
  observe CslibFrontierTests.ConcurrentBatch.limits 8 CslibFrontierTests.NativeBatchPolicy.first
    (NativeBatchMetadata.metadataPaths value)

private theorem processed_metadata (value : ℕ) :
    ResponseExecution.afterReply oneContext (replyOf (metadataReceipt value)).word = [true] := by
  have hr : (metadataReceipt value).report =
      ![some (some [true], value + 1), some (some [true], value + 1), none] := by
    funext i
    fin_cases i <;> norm_num [metadataReceipt, observe, NativeBatchMetadata.metadataPaths,
      CslibFrontierTests.NativeBatchPolicy.first, CslibFrontierTests.ConcurrentBatch.limits,
      CallTrace.report, CallTrace.response, CallTrace.stop]
  have hf : Packets.families 3 1 (replyOf (metadataReceipt value)).word = [[0], [0]] := by
    change Packets.families 3 1 (encodeReport (metadataReceipt value).report) = _
    rw [Packets.families_report, hr]
    norm_num [proposals, decodeFamily, sourceIndices, List.ofFn_succ]
    decide
  simp only [ResponseExecution.afterReply, Packets.assemble, oneContext,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil, hf]
  norm_num [complete, output, retain, NativeRetention.step, certified, newly,
    covered, NativeRetention.normalize, population, ground, cost, price, List.range_succ]

/-- One fixed actual native program handles the fixed source's unbounded geometric
invoices and emits a genuine cover with probability one. Full invoices/hidden state
stay jointly distributed exactly as sampled; no copying clock or truncation is used. -/
example : ∃ (k : ℕ) (S : Type) (_ : Finite S) (continuation : MultiTapePTM k Bool S Unit),
    (NativeUnboundedExecution.terminal (NativeResponseExecution.machine continuation)
      (environment CslibFrontierTests.ConcurrentBatch.limits NativeBatchMetadata.sample)
      ⟨(NativeResponseExecution.machine continuation).initialConfig
        (encodeBatch CslibFrontierTests.NativeBatchPolicy.first),
          NativeBatchMetadata.start.memory⟩).map
        (Option.map fun final => (final.config.tapes.output, final.memory)) =
      NativeBatchMetadata.metadata.map fun value => some ([true],
        NativeBatchMetadata.start.memory.record
          ((), encodeBatch CslibFrontierTests.NativeBatchPolicy.first)
          (replyOf (metadataReceipt value))
          (commit NativeBatchMetadata.start.memory.privateState
            (metadataReceipt value) value)) := by
  obtain ⟨k, S, hS, continuation, hc⟩ := ResponseExecution.exists_query_retention oneContext
  refine ⟨k, S, hS, continuation, ?_⟩
  rw [hc]
  have ha : admit CslibFrontierTests.ConcurrentBatch.limits
      NativeBatchMetadata.start.memory.privateState
      (encodeBatch CslibFrontierTests.NativeBatchPolicy.first) =
      some CslibFrontierTests.NativeBatchPolicy.first := by
    simp [admit, decodeBatch_encode, NativeBatchMetadata.start, ConcurrentBatch.initial,
      CslibFrontierTests.ConcurrentBatch.limits]
  change (serve _ _ _ _).map _ = _
  rw [serve_accepted _ _ _ _ _ ha]
  simp only [NativeBatchMetadata.sample, NativeBatchMetadata.start, ConcurrentBatch.initial,
    ite_true, PMF.map_comp, tsub_zero]
  apply congrArg (fun f : ℕ → Option (Word × Memory Unit (ServerState 3 ℕ)) =>
    NativeBatchMetadata.metadata.map f)
  funext value
  change some (ResponseExecution.afterReply oneContext (replyOf (metadataReceipt value)).word,
    _) = _
  rw [processed_metadata]
  rfl

/-- The actual combined code is also consumed by the existing whole-policy
selected-epoch transfer. Its representation equality is a proved native theorem,
not an assumption supplied with the continuation or source. -/
example {k : ℕ} {S : Type} (continuation : MultiTapePTM k Bool S Unit) (bit : Bool) :
    (NativeBatch.Trace.law limits sample (NativeResponseExecution.machine continuation)
      (limits.turns + 1)
      ⟨(NativeResponseExecution.machine continuation).initialConfig (encodeBatch first),
        NativeQueryAll.memory bit⟩).map
          (fun state => state.hidden.map NativeInterface.worldOf) =
      NativeUnboundedExecution.terminal (NativeResponseExecution.machine continuation)
        (environment limits sample)
        ⟨(NativeResponseExecution.machine continuation).initialConfig (encodeBatch first),
          NativeQueryAll.memory bit⟩ :=
  NativeBatch.Trace.law_native_terminal limits sample _ _ (NativeBatch.initial_invariant limits bit)

/-- The raw decoder does not turn rejection into a fabricated successful family. -/
example : ResponseExecution.afterReply context rejection.word = [] := by
  norm_num [ResponseExecution.afterReply, Packets.assemble, Packets.families_rejected,
    context, complete, output, retain, covered, ground, population, List.range_succ]

/-- Empty ground is computed correctly by the local continuation. The wrapper
still issues its one query; it is not the upper selector's pre-query stopping loop. -/
example : ResponseExecution.afterReply ⟨⟨[], [], [], 1, [[99]]⟩, 3, []⟩ [] = [] := by
  norm_num [ResponseExecution.afterReply, Packets.assemble, complete, output,
    ground, population, covered, retain]

end CslibFrontierTests.NativeRetentionResponse
