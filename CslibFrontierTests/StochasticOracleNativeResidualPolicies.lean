/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualOptimum
import CslibFrontier.Computability.Probabilistic.NativeQueryAll
import CslibFrontierTests.StochasticOracleResidualCover
import Mathlib.Tactic

/-!
# Concrete residual oracle and actual clockless native policy tables

Five six-point X3C blocks include overlapping unused triples. The actual native
reader receives the fully encoded source batch as its original input and copies
the complete correlated near-cover report. Its bill is two and oracle duration
one. The same unbounded machine instantiates the derived policy/readback and
nonreuse/behavioral-admission theorems. Wrong subinstance bytes are canceled and billed.
No native optimum or successful-cover conclusion is assumed.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleNativeResidualPolicies
open Cslib.Probability StochasticOracle NativeRetention ResidualCover
open NativeResidualOracle ConcurrentBatch NativeOpenExecution Turing
open Cslib.Optimization.OneConstraint
open scoped NNReal ENNReal

private abbrev blocks := StochasticOracleResidualCover.blocks
private abbrev parameters := StochasticOracleResidualCover.parameters
private def points : Fin (Fintype.card (Point blocks)) ≃ Point blocks :=
  (Fintype.equivFin _).symm
private def candidates : Fin (Fintype.card (Candidate blocks)) ≃ Candidate blocks :=
  (Fintype.equivFin _).symm
private def invoice (i : Fin 6) : ℕ := if i = 0 then 2 else 1
private def limits : Limits 6 := ⟨fun _ => 1, by intro _; norm_num, 2, 2⟩

private def nearBatch : ConcurrentBatch.Batch 6 :=
  ⟨fun i => if i = 0 then some (query blocks points candidates 0) else none,
    ⟨0, by simp [active]⟩⟩

private theorem near_active : active nearBatch.slots = {0} := by
  ext i
  by_cases hi : i = 0 <;> simp [active, nearBatch, hi]

private theorem near_calls : calls nearBatch = {none} := by
  rw [calls, near_active, Finset.map_singleton]
  rfl

private def sampler : Sampler 6 Unit := sample blocks points candidates parameters invoice
private def receipt (j : Fin 5) : Exchange 6 :=
  observe limits 2 nearBatch (paths blocks points candidates invoice nearBatch (some j))

private theorem served :
    serve limits sampler (encodeBatch nearBatch) (ConcurrentBatch.initial ()) =
      parameters.missing.toPMF.map (fun j =>
        (replyOf (receipt j), commit (ConcurrentBatch.initial ()) (receipt j) ())) := by
  have ha : admit limits (ConcurrentBatch.initial ()) (encodeBatch nearBatch) = some nearBatch := by
    simp [admit, decodeBatch_encode, ConcurrentBatch.initial, limits]
  rw [serve_accepted _ _ _ _ _ ha]
  simp [sampler, sample, near_calls, reply, Distribution.toPMF_map,
    PMF.map_comp, Function.comp_def, receipt, limits, ConcurrentBatch.initial]

private theorem resources (j : Fin 5) : (receipt j).tokens = 2 ∧ (receipt j).duration = 1 := by
  have h := NativeResidualReplies.observed_resources blocks candidates limits 2 nearBatch
    (families blocks points candidates nearBatch (some j)) invoice (fun _ => rfl) (by norm_num)
  have hpaths : paths blocks points candidates invoice nearBatch (some j) =
      (fun i => NativeResidualReplies.path blocks candidates
        (families blocks points candidates nearBatch (some j) i) (invoice i)) := rfl
  rw [receipt, hpaths]
  simpa only [near_active, Finset.sum_singleton, invoice, ite_true] using h

-- Each missing component has positive probability in the actual joint sampler.
example (j : Fin 5) :
    (paths blocks points candidates invoice nearBatch (some j), ()) ∈
      (sampler (ConcurrentBatch.initial ()) nearBatch).support := by
  change _ ∈ ((reply parameters (calls nearBatch)).toPMF.map _).support
  rw [near_calls]
  simp only [reply, Finset.mem_singleton, ite_true, Distribution.toPMF_map, PMF.map_comp]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨j, ?_, rfl⟩
  intro hz
  have h := parameters.missing.toPMF_real j
  rw [hz, ENNReal.toReal_zero] at h
  norm_num [parameters, StochasticOracleResidualCover.parameters] at h

private def request : Word := encodeBatch nearBatch
private def memory : Memory Unit (ServerState 6 Unit) := ⟨ConcurrentBatch.initial (), []⟩
private def start := NativeQueryAll.start () 0 request memory

-- Actual complete native output and memory, retaining the random missing block;
-- the original input contains the source query, not a preinstalled reply/context.
example :
    (NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0)
      (environment limits sampler) start).map
        (Option.map fun world => (world.config.tapes.output, world.memory)) =
      parameters.missing.toPMF.map (fun j => some ((replyOf (receipt j)).word,
        memory.record ((), request) (replyOf (receipt j))
          (commit (ConcurrentBatch.initial ()) (receipt j) ()))) := by
  rw [start, NativeQueryAll.query_readback]
  change ((serve limits sampler request (ConcurrentBatch.initial ())).map
    (fun (reply, state) => (reply.word, memory.record ((), request) reply state))).map some = _
  rw [request, served, PMF.map_comp, PMF.map_comp]
  rfl

-- The source-matching positive bill and physical latency are derived for this
-- same actual machine and correlated source, without a resource contract.
example :
    (NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0)
      (environment limits sampler) start).map (Option.map fun world =>
        (tokenBill world.memory.events, elapsed world.memory.events)) =
      PMF.pure (some ((2 : ℝ≥0), (1 : ℝ≥0))) := by
  rw [start, NativeQueryAll.terminal_query]
  change ((serve limits sampler request (ConcurrentBatch.initial ())).map _).map _ = _
  rw [request, served, PMF.map_comp, PMF.map_comp]
  have h (j : Fin 5) :
      (tokenBill (NativeQueryAll.finish (k := 0) () (encodeBatch nearBatch) memory
        (replyOf (receipt j))
        (commit (ConcurrentBatch.initial ()) (receipt j) ())).memory.events,
       elapsed (NativeQueryAll.finish (k := 0) () (encodeBatch nearBatch) memory
        (replyOf (receipt j))
        (commit (ConcurrentBatch.initial ()) (receipt j) ())).memory.events) = (2, 1) := by
    obtain ⟨hb, ht⟩ := resources j
    simp [NativeQueryAll.finish, NativeQueryAll.finishFrom, NativeQueryAll.start, memory,
      Memory.record, tokenBill, elapsed, replyOf, hb, ht]
  simp only [Function.comp_def, Option.map_some, h]
  exact PMF.map_const _ _

-- The same native reader has constructed posterior tables and exact stopped
-- output readback, rather than an assumed machine-to-policy representation.
example :
    ((NativeResidualPolicies.policy blocks points candidates parameters limits
      (fun _ _ _ => PMF.pure invoice)
      (NativeQueryAll.machine () 0) start).run parameters).toPMF.map
        (fun (_, _, _, _, C) => C) =
      (NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0)
        (environment limits sampler) start).map
          (NativeResidualPolicies.terminalOutput blocks candidates) := by
  simpa only [NativeResidualConditionalInvoice.sample_const,
    NativeResidualInvoice.sample_pure, sampler, limits] using
    NativeResidualPolicies.terminal_law blocks points candidates parameters limits
      (fun _ _ _ => PMF.pure invoice)
    _ start (NativeBatch.initial_invariant limits ()) rfl

example :
    (NativeResidualPolicies.selectionPolicy blocks points candidates parameters limits
      (fun _ _ _ => PMF.pure invoice)
      (NativeQueryAll.machine () 0) start).Admissible parameters := by
  exact NativeResidualPolicies.selection_admissible blocks points candidates parameters limits
    (fun _ _ _ => PMF.pure invoice)
    _ start (NativeBatch.initial_invariant limits ()) rfl

-- The universal construction also applies to the exact named adaptive upper
-- program from original binary WSC input, with blank initial source memory.
private def adaptiveInput : Word := NativeResidualSelector.startupEncoding
  (NativeResidualEncoding.source blocks points candidates, 5)
private def adaptiveStart :
    World NativeResidualSelector.controller.tapes NativeResidualSelector.controller.Controls
      Unit (ServerState 6 Unit) adaptiveInput :=
  ⟨NativeResidualSelector.controller.program.initialConfig adaptiveInput, memory⟩

example :
    (NativeResidualPolicies.selectionPolicy blocks points candidates parameters limits
      (fun _ _ _ => PMF.pure invoice)
      NativeResidualSelector.controller.program adaptiveStart).Admissible parameters := by
  exact NativeResidualPolicies.selection_admissible blocks points candidates parameters limits
    (fun _ _ _ => PMF.pure invoice) _ adaptiveStart (NativeBatch.initial_invariant limits ()) rfl

-- An incorrect source subinstance is canceled, even for the near-cover role.
-- The extra suffix is actual invalid bytes, not a false semantic-parser premise.
private def wrongBatch : ConcurrentBatch.Batch 6 :=
  ⟨fun i => if i = 0 then some (query blocks points candidates 0 ++ [false]) else none,
    ⟨0, by simp [active]⟩⟩

private theorem wrong_near (j : Fin 5) :
    families blocks points candidates wrongBatch (some j) 0 = none := by
  apply wrong_query
  simp only [wrongBatch, ite_true, ne_eq, Option.some.injEq]
  intro h
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_singleton] at hlen
  omega

example (j : Fin 5) :
    (observe limits 2 wrongBatch
      (paths blocks points candidates invoice wrongBatch (some j))).report 0 =
      some (none, 2) := by
  have hpaths : paths blocks points candidates invoice wrongBatch (some j) =
      (fun i => NativeResidualReplies.path blocks candidates
        (families blocks points candidates wrongBatch (some j) i) (invoice i)) := rfl
  rw [hpaths, NativeResidualReplies.observe_report blocks candidates limits 2 wrongBatch
    _ invoice (fun _ => rfl) (by norm_num)]
  have hs : wrongBatch.slots 0 = some (query blocks points candidates 0 ++ [false]) := rfl
  simp [NativeResidualReplies.report, NativeResidualReplies.answersFor,
    hs, wrong_near, invoice]

private theorem prices : ∀ i, (invoice i : ℝ) =
    (finSuccEquiv 5 i).elim parameters.nearCost parameters.specialistCost := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num [invoice, finSuccEquiv, parameters, StochasticOracleResidualCover.parameters]
  · have he : finSuccEquiv 5 j.succ = some j := by
      exact finSuccEquiv_succ j
    rw [he]
    norm_num [invoice, parameters, StochasticOracleResidualCover.parameters]

-- Positive, source-matching invoices instantiate the comparison with the same
-- actual correlated reader. These are no longer unrelated analytic price fields.
example : ENNReal.ofReal ((NativeResidualPolicies.policy blocks points candidates parameters
    limits (fun _ _ _ => PMF.pure invoice) (NativeQueryAll.machine () 0) start).cost parameters) ≤
    NativeBatch.Quantitative.expected limits sampler (NativeQueryAll.machine () 0)
      NativeBatch.Trace.charge 3 start := by
  simpa only [NativeResidualConditionalInvoice.sample_const,
    NativeResidualInvoice.sample_pure, sampler, limits] using
    NativeResidualPolicies.policy_cost_le_native blocks points candidates parameters
      limits (fun _ _ _ => PMF.pure invoice) _ start (NativeResidualConditionalInvoice.hasMean_const
        (NativeResidualInvoice.hasMean_pure parameters invoice prices))

example : batchCost parameters (calls nearBatch) = 2 ∧
    NativeResidualOracle.invoiceCost invoice (calls nearBatch) = 2 := by
  rw [near_calls]
  norm_num [batchCost, parameters, StochasticOracleResidualCover.parameters,
    NativeResidualOracle.invoiceCost, finSuccEquiv, invoice]

-- The numerical lower bound is universal over actual native competitors, not a
-- pre-assumed behavioral policy. Sure success is exactly the source's competitor
-- requirement. This does not assert that the reader above is a cover solver.
example {k : ℕ} {Control : Type} {input : List Bool}
    (machine : MultiTapePTM k Bool Control Unit)
    (world : World k Control Unit (ServerState 6 Unit) input)
    (hi : NativeBatch.Invariant limits world.memory)
    (hzero : world.memory.privateState.history = [])
    (hadmit : NativeUnboundedExecution.SelectionOnly machine (environment limits sampler)
      (NativeBatch.candidateParser (n := 6) (Fintype.card (Candidate blocks)))
      (decodeFamily (Fintype.card (Candidate blocks)))
      (NativeResidualPolicies.optimalAccept blocks candidates (by norm_num)) world)
    (hsuccess : ((NativeUnboundedExecution.terminal machine
      (environment limits sampler) world).map
      (fun result => decide (optimalOutput (T := blocks) (by norm_num)
        (NativeResidualPolicies.terminalOutput blocks candidates result) = 1))) true = 1) :
    3 ≤ NativeBatch.Quantitative.expected limits sampler machine
      NativeBatch.Trace.charge 3 world := by
  have h := NativeResidualPolicies.native_two_lower blocks points candidates parameters limits
    (fun _ _ _ => PMF.pure invoice) machine world hi hzero rfl (by norm_num)
    (NativeResidualConditionalInvoice.hasMean_const
      (NativeResidualInvoice.hasMean_pure parameters invoice prices))
    (by simpa only [NativeResidualConditionalInvoice.sample_const,
      NativeResidualInvoice.sample_pure, sampler, limits] using hadmit)
    (by simpa only [NativeResidualConditionalInvoice.sample_const,
      NativeResidualInvoice.sample_pure, sampler, limits] using hsuccess)
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean] at h
  simpa only [NativeResidualConditionalInvoice.sample_const,
    NativeResidualInvoice.sample_pure, sampler, limits, parameters,
    StochasticOracleResidualCover.parameters, Nat.reduceAdd] using h

private def optimumInput : GuardedStartup.Input :=
  ⟨⟨SourceEncoding.toNative (NativeResidualEncoding.source blocks points candidates),
    2, 6, []⟩, 2⟩

private def optimumCandidates : Fin optimumInput.startup.system.rows.length ≃ Candidate blocks :=
  candidates

private theorem optimum_valid : Valid optimumInput.startup.system :=
  SourceEncoding.valid_toNative _
    (NativeResidualEncoding.source_valid blocks points candidates (by norm_num))

-- The existing Theorem 5 native OPT, with all finite-control admitted competitors,
-- specializes to a strictly positive numerical lower bound on this residual input.
example : 3 ≤ BatchOptimum.optimum limits
    (sample blocks points optimumCandidates parameters invoice)
      optimumInput () optimum_valid 1 := by
  have h := NativeResidualOptimum.two_lower blocks points optimumInput optimumCandidates
    parameters limits invoice (by norm_num) optimum_valid rfl rfl prices
  norm_num [parameters, StochasticOracleResidualCover.parameters, Distribution.mean] at h
  exact h

-- Native certification is optimality for the actual decoded input. Its weight-one
-- cover is constructed, without being supplied to a competitor in the startup data.
example : NativeResidualPolicies.optimalAccept blocks optimumCandidates (by norm_num)
    (NativeResidualReplies.family blocks optimumCandidates
      (payload blocks Finset.univ)) = true := by
  have h := primal_optimum blocks (by norm_num)
  simp [NativeResidualPolicies.optimalAccept, optimalOutput, NativeResidualReplies.family,
    Finset.map_eq_image, Finset.image_image, Function.comp_def, h.1, h.2.1]

-- The comparison survives literal deadline cancellation: visible proposals are
-- deleted, while the issued near-cover invoice is still present.
example (j : Fin 5) :
    (observe limits 0 nearBatch
      (paths blocks points candidates invoice nearBatch (some j))).tokens = 2 ∧
    proposals (Fintype.card (Candidate blocks))
      (observe limits 0 nearBatch
        (paths blocks points candidates invoice nearBatch (some j))).report = [] := by
  constructor
  · rw [observe_tokens, near_active, Finset.sum_singleton]
    rfl
  · simp [proposals, observe, paths, NativeResidualReplies.path,
      CallTrace.report, CallTrace.response, families, nearBatch, limits,
      answer, finSuccEquiv, List.ofFn_succ, List.ofFn_zero]

end CslibFrontierTests.StochasticOracleNativeResidualPolicies
