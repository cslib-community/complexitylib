/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import CslibFrontier.Probability.PMF.ObservedProcess
public import Mathlib.Basic.NNReal.Defs
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Halting
import Mathlib.Tactic

/-!
# Actual open native execution with history and resource observations

A stateful oracle answers actual native query buffers, recording its raw answer,
nonnegative issued token charge and external duration. Its law may depend on the
entire previous transcript and private oracle state. No finite response alphabet
or finite private-storage approximation is used.

The explicit native transition kernel is proved equal to the interpreted native
program. Pause/resume and supported halting preserve full configurations, channel
buffers, oracle state and the complete query history. Instruction-indexed public
behavioral kernels are constructed from the actual hidden-state path posterior.
These include silent local steps; collapsing them to oracle-turn stopping epochs,
unbounded local stopping and a source batch/query codec remain separate obligations.

## Main results

* `execute_eq_stateLaw`: actual native execution equals the derived transition process.
* `execute_add`: exact pause/resume, retaining all hidden state and observations.
* `execute_public_paths`: entire public path laws from actual native checkpoints.
* `execute_history_law`: the public process has the actual complete query-trace law.
* `execute_resources`: actual prefix charges plus newly recorded charges.
* `execute_padding`: supported native halting stops all further calls and resources.
* `execute_public_score`: extended nonnegative public/native expectation equality.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeOpenExecution
open Turing Turing.MultiTapeMachine
open scoped NNReal

/-- One external response with its reported nonnegative resource charges. A
batch-oriented handler reports the batch's total bill and parallel duration. -/
structure Reply where
  /-- Actual word installed on the native answer tape. -/
  word : List Bool
  /-- Tokens charged through return or cancellation. -/
  tokens : ℝ≥0
  /-- External elapsed duration; local native instructions are excluded. -/
  duration : ℝ≥0

/-- One actual native query and response, including resource observations. -/
structure Event (Operation : Type) where
  /-- Invoked communication channel. -/
  operation : Operation
  /-- Submitted native query buffer. -/
  request : List Bool
  /-- Returned word and reported charges. -/
  reply : Reply

/-- Oracle private state and complete actual query history, newest first. -/
structure Memory (Operation Private : Type) where
  /-- Arbitrary private state shared by successive oracle calls. -/
  privateState : Private
  /-- All completed or canceled external calls, without local coin samples. -/
  events : List (Event Operation)

/-- Source history-dependent response law; no independence between calls is
imposed, and the observation law may have countably infinite support. -/
abbrev Environment (Operation Private : Type) :=
  Operation × List Bool → Memory Operation Private → PMF (Reply × Private)

variable {Operation Private Control : Type} {k : ℕ} {input : List Bool}

/-- Update the private oracle state and append exactly one actual event. -/
@[expose] def Memory.record (memory : Memory Operation Private) (q : Operation × List Bool)
    (reply : Reply) (privateState : Private) : Memory Operation Private :=
  ⟨privateState, ⟨q.1, q.2, reply⟩ :: memory.events⟩

/-- Actual stateful native word handler, with charges and transcript recorded
from the same jointly sampled reply that is installed on the answer tape. -/
@[expose] def handler (env : Environment Operation Private) (q : Operation × List Bool) :
    StateT (Memory Operation Private) PMF (List Bool) := fun memory =>
  (env q memory).map fun (reply, privateState) =>
    (reply.word, memory.record q reply privateState)

/-- The entire hidden native configuration and oracle state. Work tapes, query
buffers and answer heads are retained directly, without an exported packet. -/
structure World (k : ℕ) (Control Operation Private : Type) (input : List Bool) where
  /-- Actual native tapes, control and all communication channels. -/
  config : Config k Bool Control Operation input
  /-- Oracle private state and observed query history. -/
  memory : Memory Operation Private

variable [DecidableEq Operation]
variable (machine : MultiTapePTM k Bool Control Operation) (env : Environment Operation Private)

/-- The actual clocked open native program, interpreted against the stateful
history-dependent word handler, retaining its complete joint final state. -/
@[expose] def execute (fuel : ℕ) (world : World k Control Operation Private input) :
    PMF (World k Control Operation Private input) :=
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    (machine.runConfigFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op word => ProbOracleComp.query (op, word)) fuel world.config)).run world.memory).map
        (fun (config, memory) => ⟨config, memory⟩)

/-- One explicit native instruction. Private fair coins select the actual
transition table; only an actual query samples the external response law. -/
@[expose] def step (world : World k Control Operation Private input) :
    PMF (World k Control Operation Private input) :=
  match world.config.tapes.state with
  | none => PMF.pure world
  | some control => (PMF.uniformOfFintype Bool).bind fun bit =>
    match machine.tr control world.config.tapes.inputSymbol world.config.tapes.workTapeSymbols
        world.config.answerSymbols bit with
    | .step action symbol move => PMF.pure ⟨world.config.step action symbol move, world.memory⟩
    | .query op next =>
      (env (op, (world.config.channels op).queryBuffer) world.memory).map
        fun (reply, privateState) =>
        ⟨world.config.receive op next reply.word,
          world.memory.record (op, (world.config.channels op).queryBuffer) reply privateState⟩

/-- An empty clock preserves the full joint state, without issuing a call. -/
theorem execute_zero (world : World k Control Operation Private input) :
    execute machine env 0 world = PMF.pure world := by
  simp [execute, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom]

/-- Native pause/resume preserves the complete joint state, including all
correlations and prior query charges. No representation identity is assumed. -/
theorem execute_add (first second : ℕ) (world : World k Control Operation Private input) :
    execute machine env (first + second) world =
      (execute machine env first world).bind (execute machine env second) := by
  simp only [execute, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom_add,
    OracleComp.interpret_bind, StateT.run_bind, PMF.monad_bind_eq_bind,
    PMF.map_bind, PMF.bind_map]
  rfl

/-- The explicit transition kernel is the actual native one-instruction law. -/
theorem execute_one (world : World k Control Operation Private input) :
    execute machine env 1 world = step machine env world := by
  cases hs : world.config.tapes.state with
  | none => simp [execute, step, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, hs]
  | some control =>
    simp only [execute, step, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom, hs,
      bind_map_left, OracleComp.interpret_bind, StateT.run_bind,
      ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform,
      PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind]
    congr 1
    funext bit
    cases ht : machine.tr control world.config.tapes.inputSymbol world.config.tapes.workTapeSymbols
        world.config.answerSymbols bit with
    | step action symbol move =>
      simp [ht, OracleComp.interpret_pure, StateT.run_pure]
    | query op next =>
      simp only [Function.comp_apply, ht, bind_pure_comp, OracleComp.interpret_map,
        ProbOracleComp.interpret_query, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp]
      change ((env (op, (world.config.channels op).queryBuffer) world.memory).map
        (fun (reply, privateState) =>
          (reply.word, world.memory.record (op, (world.config.channels op).queryBuffer)
            reply privateState))).map
              (fun (word, memory) =>
                (⟨world.config.receive op next word, memory⟩ :
                  World k Control Operation Private input)) = _
      rw [PMF.map_comp]
      rfl

/-- The full actual native run is the derived hidden-state transition process. -/
theorem execute_eq_stateLaw (fuel : ℕ) (world : World k Control Operation Private input) :
    execute machine env fuel world = ObservedProcess.stateLaw (step machine env) fuel world := by
  induction fuel with
  | zero => exact execute_zero machine env world
  | succ n ih =>
    rw [execute_add, ih, ObservedProcess.stateLaw]
    congr 1
    funext next
    exact execute_one machine env next

/-- Complete public path representation by actual native one-instruction
checkpoints. Each checkpoint retains the full configuration and oracle memory;
`execute_add` identifies their composition with uninterrupted native execution. -/
theorem execute_public_paths {H : Type}
    (observe : World k Control Operation Private input → H) (fuel : ℕ)
    (world : World k Control Operation Private input) :
    ObservedProcess.publicLaw (step machine env) observe fuel world =
      (ObservedProcess.privateLaw (execute machine env 1) observe fuel world).map
        ObservedProcess.Path.observations := by
  have he : step (input := input) machine env = execute machine env 1 :=
    funext fun next => (execute_one machine env next).symm
  rw [he, ObservedProcess.public_eq_observed]

/-- Derived instruction-indexed history-dependent public kernels have exactly
the actual native query-history law. Local stuttering observations are retained. -/
theorem execute_history_law (fuel : ℕ) (world : World k Control Operation Private input) :
    (ObservedProcess.publicLaw (step machine env) (fun w => w.memory.events) fuel world).map
        (fun history => history.headD world.memory.events) =
      (execute machine env fuel world).map (fun w => w.memory.events) := by
  rw [execute_eq_stateLaw]
  exact ObservedProcess.public_current _ _ _ _

/-- Actual accumulated nonnegative token bill, excluding all local instructions. -/
@[expose] def tokenBill (events : List (Event Operation)) : ℝ≥0 :=
  (events.map fun event => event.reply.tokens).sum

/-- Sequential external duration. A batch record supplies its parallel duration,
so local instruction clocks do not enter this sum. -/
@[expose] def elapsed (events : List (Event Operation)) : ℝ≥0 :=
  (events.map fun event => event.reply.duration).sum

omit [DecidableEq Operation] in
/-- Appending actual events adds their token charges. -/
theorem tokenBill_append (a b : List (Event Operation)) :
    tokenBill (a ++ b) = tokenBill a + tokenBill b := by simp [tokenBill]

omit [DecidableEq Operation] in
/-- Appending actual sequential batch events adds their physical durations. -/
theorem elapsed_append (a b : List (Event Operation)) :
    elapsed (a ++ b) = elapsed a + elapsed b := by simp [elapsed]

private theorem step_trace (world next : World k Control Operation Private input)
    (h : next ∈ (step machine env world).support) :
    ∃ fresh, fresh.length ≤ 1 ∧ next.memory.events = fresh ++ world.memory.events := by
  cases hs : world.config.tapes.state with
  | none =>
    simp only [step, hs, PMF.mem_support_pure_iff] at h
    subst next
    exact ⟨[], by simp, rfl⟩
  | some control =>
    simp only [step, hs, PMF.mem_support_bind_iff] at h
    obtain ⟨bit, _, h⟩ := h
    cases ht : machine.tr control world.config.tapes.inputSymbol world.config.tapes.workTapeSymbols
        world.config.answerSymbols bit with
    | step action symbol move =>
      simp only [ht, PMF.mem_support_pure_iff] at h
      subst next
      exact ⟨[], by simp, rfl⟩
    | query op state =>
      simp only [ht, PMF.mem_support_map_iff] at h
      obtain ⟨⟨reply, privateState⟩, _, he⟩ := h
      subst next
      exact ⟨[⟨op, (world.config.channels op).queryBuffer, reply⟩], by simp, rfl⟩

/-- Every supported run extends its actual query history by at most one event
per native instruction. No earlier resource observation can be erased. -/
theorem execute_trace (fuel : ℕ) (world next : World k Control Operation Private input)
    (h : next ∈ (execute machine env fuel world).support) :
    ∃ fresh, fresh.length ≤ fuel ∧ next.memory.events = fresh ++ world.memory.events := by
  rw [execute_eq_stateLaw] at h
  induction fuel generalizing next with
  | zero =>
    simp only [ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at h
    subst next
    exact ⟨[], by simp, rfl⟩
  | succ fuel ih =>
    simp only [ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at h
    obtain ⟨mid, hm, hn⟩ := h
    obtain ⟨a, ha, he⟩ := ih mid hm
    obtain ⟨b, hb, hf⟩ := step_trace machine env mid next hn
    refine ⟨b ++ a, ?_, ?_⟩
    · simp only [List.length_append]
      omega
    · rw [hf, he, List.append_assoc]

/-- The actual bill and duration are sums of newly observed charges plus the
retained prefix charges; no bounded-total-bill or integrability premise is used. -/
theorem execute_resources (fuel : ℕ) (world next : World k Control Operation Private input)
    (h : next ∈ (execute machine env fuel world).support) :
    ∃ fresh, next.memory.events = fresh ++ world.memory.events ∧
      tokenBill next.memory.events = tokenBill fresh + tokenBill world.memory.events ∧
      elapsed next.memory.events = elapsed fresh + elapsed world.memory.events := by
  obtain ⟨fresh, _, he⟩ := execute_trace machine env fuel world next h
  exact ⟨fresh, he, by rw [he, tokenBill_append], by rw [he, elapsed_append]⟩

/-- Supported bills and physical elapsed times grow monotonically. -/
theorem execute_resources_mono (fuel : ℕ) (world next : World k Control Operation Private input)
    (h : next ∈ (execute machine env fuel world).support) :
    tokenBill world.memory.events ≤ tokenBill next.memory.events ∧
      elapsed world.memory.events ≤ elapsed next.memory.events := by
  obtain ⟨fresh, _, hb, hd⟩ := execute_resources machine env fuel world next h
  rw [hb, hd]
  exact ⟨le_add_of_nonneg_left (show 0 ≤ tokenBill fresh from bot_le),
    le_add_of_nonneg_left (show 0 ≤ elapsed fresh from bot_le)⟩

/-- Native halting stops all future queries, bills and elapsed duration while
retaining the full hidden configuration and oracle state. -/
theorem execute_halted (fuel : ℕ) (world : World k Control Operation Private input)
    (h : world.config.tapes.state = none) : execute machine env fuel world = PMF.pure world := by
  simp [execute, MultiTapePTM.runConfigFrom, MultiTapeMachine.runConfigFrom_halted, h]

/-- After actual supported halting, a larger local clock preserves the full
joint native state and query/resource path law. -/
theorem execute_padding (fuel padding : ℕ) (world : World k Control Operation Private input)
    (h : ∀ next ∈ (execute machine env fuel world).support, next.config.tapes.state = none) :
    execute machine env (fuel + padding) world = execute machine env fuel world := by
  rw [execute_add]
  conv_rhs => rw [← PMF.bind_pure (execute machine env fuel world)]
  apply PMF.bind_congr_on_support
  intro next hn
  exact execute_halted machine env padding next (h next hn)

/-- All nonnegative public-path scores have their actual native expectation.
This applies to accumulated bill, physical duration and joint deadline events;
expectations may be infinite, so integrability is not assumed. -/
theorem execute_public_score (fuel : ℕ) (world : World k Control Operation Private input)
    (score : List (Event Operation) → ENNReal) :
    (∑' history, ObservedProcess.publicLaw (step machine env) (fun w => w.memory.events)
      fuel world history * score (history.headD world.memory.events)) =
      ∑' next, execute machine env fuel world next * score next.memory.events := by
  have h := congrArg
    (fun law : PMF (List (Event Operation)) => ∑' events, law events * score events)
    (execute_history_law machine env fuel world)
  simpa only [PMF.tsum_map_mul] using h

end Cslib.Probability.NativeOpenExecution
