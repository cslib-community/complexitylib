/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualPolicies
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
open scoped NNReal

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
    ((NativeResidualPolicies.policy blocks points candidates parameters limits invoice
      (NativeQueryAll.machine () 0) start).run parameters).toPMF.map
        (fun (_, _, _, _, C) => C) =
      (NativeUnboundedExecution.terminal (NativeQueryAll.machine () 0)
        (environment limits sampler) start).map
          (NativeResidualPolicies.terminalOutput blocks candidates) := by
  exact NativeResidualPolicies.terminal_law blocks points candidates parameters limits invoice
    _ start (NativeBatch.initial_invariant limits ()) rfl

example :
    (NativeResidualPolicies.selectionPolicy blocks points candidates parameters limits invoice
      (NativeQueryAll.machine () 0) start).Admissible parameters := by
  exact NativeResidualPolicies.selection_admissible blocks points candidates parameters limits
    invoice
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
    (NativeResidualPolicies.selectionPolicy blocks points candidates parameters limits invoice
      NativeResidualSelector.controller.program adaptiveStart).Admissible parameters := by
  exact NativeResidualPolicies.selection_admissible blocks points candidates parameters limits
    invoice _ adaptiveStart (NativeBatch.initial_invariant limits ()) rfl

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

end CslibFrontierTests.StochasticOracleNativeResidualPolicies
