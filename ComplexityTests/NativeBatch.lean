/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import ComplexityTests.ConcurrentBatch
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake
import Mathlib.Tactic

/-!
# Actual native packet construction and general concurrent batch transfer

The existing packet-writing PTM unframes a real nonempty two-call batch, submits
it on the native word channel and stops after copying a zero-length reply prefix.
Its complete actual oracle memory retains the correlated batch report and both
resource meters. This exercises actual code, not an assumed preloaded query.
-/

noncomputable section
open Cslib Cslib.Probability Turing Turing.MultiTapeTM NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle.ConcurrentBatch
open Cslib.Optimization.OneConstraint
open scoped NNReal
namespace ComplexityTests.NativeBatch
open ComplexityTests.ConcurrentBatch

/-- Actual encoded input consumed by the native packet-writing machine. -/
def input : List Bool := encPair encBits encUnary (encodeBatch first, 0)

/-- The actual native PTM which writes and submits the whole two-call packet. -/
def machine := MultiTapePTM.queryTakePTM ()

/-- Ordinary native starting tapes and empty protocol memory. -/
def start : World 0 (MultiTapePTM.QueryTakeState ⊕ RewindState) Unit (ServerState 3 Bool) input :=
  ⟨machine.initialConfig input, ⟨initial false, []⟩⟩

/-- Exact oracle memory after that real encoded two-call packet, with the same
latent bit, report, summed cancellation bill and concurrent duration. -/
def answeredMemory (u : Bool) : Memory Unit (ServerState 3 Bool) :=
  start.memory.record ((), encodeBatch first) (replyOf (firstReceipt u)) (afterFirst u)

/-- The concrete preformed packet is actually written and issued by native code.
The terminal memory law retains all correlations; no source-law equality is assumed. -/
theorem packet_memory_law :
    (execute machine (environment limits sample) (4 * (encodeBatch first).length + 6)
      start).map World.memory = (PMF.uniformOfFintype Bool).map answeredMemory := by
  have ht := MultiTapePTM.computesTidily_queryTakePTM () (encodeBatch first) 0 []
    (Memory Unit (ServerState 3 Bool)) (handler (environment limits sample))
    start.memory start.config (Cfg.init_eq_wordsCfg _ _) (by intro op; cases op; rfl)
  have hm := congrArg (PMF.map Prod.snd) ht.1
  simp only [PMF.map_comp, Function.comp_def, MultiTapePTM.runOracleConfigFrom] at hm
  simp only [Nat.mul_zero, Nat.add_zero] at hm
  simp only [execute, PMF.map_comp, Function.comp_def]
  dsimp only [machine]
  refine hm.trans ?_
  simp only [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
    PMF.monad_map_eq_map, PMF.map_comp]
  change ((serve limits sample (encodeBatch first) (initial false)).map
    (fun out => (out.1.word, start.memory.record ((), encodeBatch first) out.1 out.2))).map
      Prod.snd = _
  rw [first_law, PMF.map_comp, PMF.map_comp]
  rfl

/-- Actual native resource observations follow the same correlated two-call law:
one accepted batch, duration five, and a response-dependent summed cancellation bill. -/
theorem packet_resources_law :
    (execute machine (environment limits sample) (4 * (encodeBatch first).length + 6)
      start).map (fun world => (world.memory.privateState.history.length,
        tokenBill world.memory.events, elapsed world.memory.events)) =
      (PMF.uniformOfFintype Bool).map (fun u =>
        (1, (if u then 11 else 3 : ℝ≥0), (5 : ℝ≥0))) := by
  have hm := congrArg (PMF.map (fun memory : Memory Unit (ServerState 3 Bool) =>
    (memory.privateState.history.length, tokenBill memory.events, elapsed memory.events)))
      packet_memory_law
  simp only [PMF.map_comp, Function.comp_def] at hm
  refine hm.trans ?_
  congr 1
  funext u
  obtain ⟨hd, ht, _⟩ := first_resources u
  simp [answeredMemory, Memory.record, start, afterFirst, commit, initial,
    tokenBill, elapsed, replyOf, hd, ht]

/-- Every actual finite native world in this run has source-feasible history,
matching native/source bills, latency and completed-response candidate provenance. -/
example (fuel : ℕ)
    (next : World 0 (MultiTapePTM.QueryTakeState ⊕ RewindState) Unit (ServerState 3 Bool) input)
    (hn : next ∈ (execute machine (environment limits sample) fuel start).support) :
    Cslib.Probability.NativeBatch.Invariant limits next.memory :=
  Cslib.Probability.NativeBatch.execute_invariant limits sample machine fuel start next
    (Cslib.Probability.NativeBatch.initial_invariant limits false) hn

/-- Actual native pre-response batch dispatch instantiates the existing finite
quantitative oracle table, preserving the complete next world and hidden bit. -/
example {Control : Type} {k : ℕ} {x : List Bool}
    (world : World k Control Unit (ServerState 3 Bool) x) (next : Control)
    (hw : (world.config.channels ()).queryBuffer = encodeBatch first)
    (hd : world.memory.privateState.elapsed < limits.deadline)
    (ht : world.memory.privateState.history.length < limits.turns)
    (hu : Disjoint (active first.slots) world.memory.privateState.used) :
    dispatch (environment limits (profileSampler profile [] () id)) (.query world () next) =
      (profile.law [] ()).toPMF.map (fun u =>
        let receipt := profileReceipt profile limits
          (limits.deadline - world.memory.privateState.elapsed) [] () u
        (⟨world.config.receive () next (replyOf receipt).word,
          world.memory.record ((), encodeBatch first) (replyOf receipt)
            (commit world.memory.privateState receipt u)⟩ :
          World k Control Unit (ServerState 3 Bool) x)) :=
  native_dispatch_law profile limits world next [] () id hw hd ht hu

/-- Complete selected-before-response source-epoch histories use the derived
behavioral kernel, including arbitrary hidden tapes and null-history completion. -/
example {H : Type}
    (observe : Option (Phase 0 (MultiTapePTM.QueryTakeState ⊕ RewindState) Unit
      (ServerState 3 Bool) input) → H)
    (turns : ℕ) (history : List H) :
    ObservedProcess.nextHistory
      (Cslib.Probability.NativeBatch.sourceStep limits sample machine) observe turns
      (some (.ready start)) history =
      (((Cslib.Probability.NativeBatch.sourceHistoryPrior limits sample machine
        observe turns start history).bind
          (Cslib.Probability.NativeBatch.seekSourceFrom limits sample machine)).map
            (Cslib.Probability.NativeBatch.sourceSignal limits)).bind (fun selected =>
          (Cslib.Probability.NativeBatch.sourceResponse limits sample machine
            (Cslib.Probability.NativeBatch.sourceHistoryPrior limits sample machine
              observe turns start history) selected).map (fun next => observe next :: history)) :=
  Cslib.Probability.NativeBatch.source_history_kernel limits sample machine
    observe turns start history

/-- Any finite number of accepted batch epochs resumes to the actual native
terminal law, rather than assuming a machine/epoch representation identity. -/
example (turns : ℕ) :
    (ObservedProcess.stateLaw (Cslib.Probability.NativeBatch.sourceStep limits sample machine)
      turns (some (.ready start))).bind
        (Cslib.Probability.NativeBatch.finishSource limits sample machine) =
      Cslib.Probability.NativeInterface.terminal machine (environment limits sample) start :=
  Cslib.Probability.NativeBatch.resume_source_prefix limits sample machine turns start

end ComplexityTests.NativeBatch
