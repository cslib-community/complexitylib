/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import ComplexityTests.ConcurrentBatch
import Complexity.Computability.Probabilistic.NativeBatch.Quantitative
import Mathlib.Tactic

/-!
# Whole native policy with two correlated concurrent batches

A finite-control native machine actually writes both binary batch packets. The
first concurrent batch and the later deadline-clipped call share private oracle
state. Whole-policy traces retain resource observations and project to the exact
native terminal law. The conditional kernel never publishes a latent scenario label.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle.ConcurrentBatch
open Cslib.Probability.NativeBatch
open scoped NNReal ENNReal
namespace ComplexityTests.NativeBatchPolicy
open ComplexityTests.ConcurrentBatch (limits paths sample)

/-- Both first-batch query words are preformed empty words, not an empty batch. -/
def first : Batch 3 := ⟨![some [], some [], none], ⟨0, by simp [active, Finset.mem_filter]⟩⟩

/-- One remaining opportunity follows the concurrently completed first batch. -/
def second : Batch 3 := ComplexityTests.ConcurrentBatch.second

example : encodeBatch first = [true, false, true, false, false] := rfl
example : encodeBatch second = [false, false, true, false] := rfl

/-- Actual finite-control code writes the two packets and issues exactly two queries. -/
def machine : MultiTapePTM 0 Bool (Fin 12) Unit where
  initial := 0
  tr c _ _ _ _ :=
    if c = 5 then .query () 6
    else if c = 10 then .query () 11
    else .step
      { inputTape := 0, workTapes := Fin.elim0, output := none,
        state := if c = 11 then none else some (c + 1) }
      (fun _ => if c = 11 then none else some (decide (c = 0 ∨ c = 2 ∨ c = 8)))
      (fun _ => 0)

/-- A concrete ordinary native world, retaining the real channel and oracle state. -/
def atState (c : Fin 12) (word answer : List Bool) (memory : Memory Unit (ServerState 3 Bool)) :
    World 0 (Fin 12) Unit (ServerState 3 Bool) [] :=
  ⟨⟨(Cfg.init 0 []).withState (some c), fun _ => ⟨word, answer, 0⟩⟩, memory⟩

/-- Actual machine start; no preloaded query packet is assumed. -/
def start : World 0 (Fin 12) Unit (ServerState 3 Bool) [] :=
  ⟨machine.initialConfig [], ⟨StochasticOracle.ConcurrentBatch.initial false, []⟩⟩

private theorem start_eq : start = atState 0 [] [] start.memory := rfl

private theorem instruction_write (c : Fin 12) (word answer : List Bool)
    (memory : Memory Unit (ServerState 3 Bool)) (h₅ : c ≠ 5) (h₁₀ : c ≠ 10) (h₁₁ : c ≠ 11)
    (bit : Bool) :
    instruction machine (atState c word answer memory) bit =
      .local (atState (c + 1) (word ++ [decide (c = 0 ∨ c = 2 ∨ c = 8)]) answer memory) := by
  simp only [instruction, atState, Cfg.withState, Cfg.init, Fin.isValue,
    machine, Bool.decide_or, List.length_nil, h₅, ite_false, h₁₀, h₁₁,
    MultiTapeMachine.Config.step, Action.apply, moveInputPos_zero, zero_add,
    Option.toList_none, List.append_nil, Option.toList_some, SignType.coe_zero, add_zero]
  congr 4 <;> funext i <;> exact Fin.elim0 i

private theorem write_step (c : Fin 12) (word answer : List Bool)
    (memory : Memory Unit (ServerState 3 Bool)) (h₅ : c ≠ 5) (h₁₀ : c ≠ 10) (h₁₁ : c ≠ 11) :
    NativeOpenExecution.step machine (environment limits sample) (atState c word answer memory) =
      PMF.pure (atState (c + 1)
        (word ++ [decide (c = 0 ∨ c = 2 ∨ c = 8)]) answer memory) := by
  rw [← prepare_dispatch]
  simp [prepare, instruction_write c word answer memory h₅ h₁₀ h₁₁, PMF.bind_map,
    Function.comp_def, dispatch]

private theorem seek_write (c : Fin 12) (word answer : List Bool)
    (memory : Memory Unit (ServerState 3 Bool)) (h₅ : c ≠ 5) (h₁₀ : c ≠ 10) (h₁₁ : c ≠ 11) :
    seekSourceFrom limits sample machine (some (.ready (atState c word answer memory))) =
      seekSourceFrom limits sample machine
        (some (.ready (atState (c + 1)
          (word ++ [decide (c = 0 ∨ c = 2 ∨ c = 8)]) answer memory))) := by
  have hready : sourceSilent limits sample machine (.ready (atState c word answer memory)) =
      PMF.pure (.pending (.local (atState (c + 1)
        (word ++ [decide (c = 0 ∨ c = 2 ∨ c = 8)]) answer memory))) := by
    have hstate : (atState c word answer memory).config.tapes.state = some c := rfl
    simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
      NativeUnboundedExecution.halted, hstate, reduceCtorEq, ite_false,
      phaseStep, Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp,
      Function.comp_def, instruction_write c word answer memory h₅ h₁₀ h₁₁]
    exact PMF.map_const _ _
  simp only [seekSourceFrom]
  rw [StoppedProcess.terminal_step (sourceSilent limits sample machine)
    (sourceBoundary limits) (StoppedProcess.beforeBoundary_absorbs _ _), hready,
    PMF.pure_bind, StoppedProcess.terminal_step (sourceSilent limits sample machine)
      (sourceBoundary limits) (StoppedProcess.beforeBoundary_absorbs _ _)]
  simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, phaseStep, dispatch]

/-- Both call paths and the next private state arise from the same first hidden bit. -/
def firstReceipt (u : Bool) : Exchange 3 := observe limits 8 first (paths u)

def afterFirst (u : Bool) : ServerState 3 Bool :=
  commit (StochasticOracle.ConcurrentBatch.initial false) (firstReceipt u) u

def firstMemory (u : Bool) : Memory Unit (ServerState 3 Bool) :=
  start.memory.record ((), encodeBatch first) (replyOf (firstReceipt u)) (afterFirst u)

private theorem first_admit : admit limits start.memory.privateState (encodeBatch first) =
    some first := by
  simp [admit, decodeBatch_encode, start, StochasticOracle.ConcurrentBatch.initial, limits]

private theorem first_dispatch : dispatch (environment limits sample)
      (.query (atState 5 (encodeBatch first) [] start.memory) () 6) =
    (PMF.uniformOfFintype Bool).map (fun u =>
      atState 6 [] (replyOf (firstReceipt u)).word (firstMemory u)) := by
  simp only [dispatch, atState, environment]
  rw [serve_accepted _ _ _ _ _ first_admit]
  simp only [sample, start, StochasticOracle.ConcurrentBatch.initial, ite_true, PMF.map_comp]
  simp only [firstReceipt, afterFirst, firstMemory, start, MultiTapeMachine.Config.receive]
  simp only [limits, tsub_zero, Function.comp_def]
  congr 1

/-- Actual first packet is written by five native instructions, before any response. -/
example : execute machine (environment limits sample) 5 start =
    PMF.pure (atState 5 (encodeBatch first) [] start.memory) := by
  rw [execute_eq_stateLaw, start_eq]
  norm_num [StoppedProcess.stateLaw_succ_left, ObservedProcess.stateLaw, write_step]
  rfl

private theorem seek_query (c next : Fin 12) (word answer : List Bool)
    (memory : Memory Unit (ServerState 3 Bool))
    (htr : ∀ bit, instruction machine (atState c word answer memory) bit =
      .query (atState c word answer memory) () next)
    (batch : Batch 3) (ha : admit limits memory.privateState word = some batch) :
    seekSourceFrom limits sample machine (some (.ready (atState c word answer memory))) =
      PMF.pure (some (.pending (.query (atState c word answer memory) () next))) := by
  have hready : sourceSilent limits sample machine (.ready (atState c word answer memory)) =
      PMF.pure (.pending (.query (atState c word answer memory) () next)) := by
    have hstate : (atState c word answer memory).config.tapes.state = some c := rfl
    simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
      NativeUnboundedExecution.halted, hstate, reduceCtorEq, ite_false, phaseStep,
      Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def, htr]
    exact PMF.map_const _ _
  simp only [seekSourceFrom]
  rw [StoppedProcess.terminal_step (sourceSilent limits sample machine)
    (sourceBoundary limits) (StoppedProcess.beforeBoundary_absorbs _ _), hready, PMF.pure_bind]
  apply StoppedProcess.terminal_halted
  simpa [sourceBoundary, atState] using congrArg Option.isSome ha

/-- First whole source epoch executes actual packet-writing code before sampling. -/
theorem first_seek : seekSourceFrom limits sample machine (some (.ready start)) =
    PMF.pure (some (.pending (.query (atState 5 (encodeBatch first) [] start.memory) () 6))) := by
  rw [start_eq]
  norm_num [seek_write]
  exact seek_query 5 6 (encodeBatch first) [] start.memory (by intro bit; rfl) first first_admit


/-- The first actual source receipt, hidden bit and native continuation remain joint. -/
def traceOne (u : Bool) : Trace.State 3 0 Bool (Fin 12) [] :=
  ⟨some (.ready (atState 6 [] (replyOf (firstReceipt u)).word (firstMemory u))),
    [some (firstReceipt u)]⟩

private theorem first_trace_step : Trace.step limits sample machine (Trace.initial start) =
    (PMF.uniformOfFintype Bool).map traceOne := by
  simp only [Trace.step, Trace.initial, first_seek, PMF.pure_bind,
    Trace.respond, respondSource, phaseStep, first_dispatch, PMF.map_comp]
  rfl

private theorem first_resources (u : Bool) :
    (firstReceipt u).duration = 5 ∧ (firstReceipt u).tokens = (if u then 11 else 3) := by
  have ha : active first.slots = {0, 1} := by decide
  dsimp only [firstReceipt, Exchange.duration, Exchange.tokens]
  change (active first.slots).sup _ = _ ∧ (∑ i ∈ active first.slots, _) = _
  rw [ha]
  cases u <;> norm_num [observe, paths, CallTrace.report, CallTrace.response,
    CallTrace.stop, ComplexityTests.ConcurrentBatch.delayedBill, limits, first]

/-- Later response shares the first hidden bit; absolute deadline leaves only three units. -/
def secondReceipt (u : Bool) : Exchange 3 := observe limits 3 second (paths u)

def afterSecond (u : Bool) : ServerState 3 Bool :=
  commit (afterFirst u) (secondReceipt u) u

def secondMemory (u : Bool) : Memory Unit (ServerState 3 Bool) :=
  (firstMemory u).record ((), encodeBatch second) (replyOf (secondReceipt u)) (afterSecond u)

private theorem second_admit (u : Bool) :
    admit limits (firstMemory u).privateState (encodeBatch second) = some second := by
  have hdisj : Disjoint (active second.slots) (active first.slots) := by decide
  have htime : (firstMemory u).privateState.elapsed = 5 := by
    change 0 + (firstReceipt u).duration = 5
    rw [(first_resources u).1, zero_add]
  have hused : (firstMemory u).privateState.used = active first.slots := by
    change active first.slots ∪ ∅ = _
    simp
  have hlen : (firstMemory u).privateState.history.length = 1 := rfl
  norm_num [admit, decodeBatch_encode, htime, hused, hlen, limits, hdisj]

private theorem second_seek (u : Bool) : seekSourceFrom limits sample machine
      (traceOne u).hidden =
    PMF.pure (some (.pending (.query
      (atState 10 (encodeBatch second) (replyOf (firstReceipt u)).word (firstMemory u))
        () 11))) := by
  simp only [traceOne]
  norm_num [seek_write]
  exact seek_query 10 11 (encodeBatch second) _ _ (by intro bit; rfl) second (second_admit u)

private theorem second_dispatch (u : Bool) : dispatch (environment limits sample)
      (.query (atState 10 (encodeBatch second) (replyOf (firstReceipt u)).word (firstMemory u))
        () 11) =
    PMF.pure (atState 11 [] (replyOf (secondReceipt u)).word (secondMemory u)) := by
  simp only [dispatch, atState, environment]
  rw [serve_accepted _ _ _ _ _ (second_admit u)]
  have hsub : limits.deadline - (firstMemory u).privateState.elapsed = 3 := by
    change (8 : ℝ≥0) - (0 + (firstReceipt u).duration) = 3
    rw [(first_resources u).1, zero_add]
    apply Subtype.ext
    norm_num [NNReal.coe_sub]
  have hs : sample (firstMemory u).privateState second = PMF.pure (paths u, u) := by
    simp [sample, firstMemory, afterFirst, Memory.record, commit]
  rw [hs, PMF.pure_map, hsub]
  simp only [secondReceipt, secondMemory, afterSecond,
    MultiTapeMachine.Config.receive, Cfg.withState, Function.update_eq_const_of_subsingleton,
    PMF.pure_map]
  rfl

/-- Both actual completed source batches, without latent-scenario abstraction. -/
def traceTwo (u : Bool) : Trace.State 3 0 Bool (Fin 12) [] :=
  ⟨some (.ready (atState 11 [] (replyOf (secondReceipt u)).word (secondMemory u))),
    [some (secondReceipt u), some (firstReceipt u)]⟩

private theorem second_trace_step (u : Bool) : Trace.step limits sample machine (traceOne u) =
    PMF.pure (traceTwo u) := by
  simp only [Trace.step, second_seek, PMF.pure_bind, Trace.respond, respondSource,
    phaseStep, second_dispatch, PMF.pure_map]
  rfl

/-- Actual whole-policy laws retain a correlated first receipt and second canceled call. -/
theorem law_one : Trace.law limits sample machine 1 start =
    (PMF.uniformOfFintype Bool).map traceOne := by
  simp [Trace.law, ObservedProcess.stateLaw, first_trace_step]

theorem law_two : Trace.law limits sample machine 2 start =
    (PMF.uniformOfFintype Bool).map traceTwo := by
  change (Trace.law limits sample machine 1 start).bind (Trace.step limits sample machine) = _
  rw [law_one, PMF.bind_map]
  simp only [Function.comp_def, second_trace_step]
  rfl


/-- Actual halted world after local completion, with both resource receipts retained. -/
def done (u : Bool) : World 0 (Fin 12) Unit (ServerState 3 Bool) [] :=
  let previous := atState 11 [] (replyOf (secondReceipt u)).word (secondMemory u)
  ⟨{ previous.config with tapes := previous.config.tapes.withState none }, previous.memory⟩

private theorem halt_instruction (u bit : Bool) : instruction machine
    (atState 11 [] (replyOf (secondReceipt u)).word (secondMemory u)) bit = .local (done u) := by
  simp only [instruction, atState, Cfg.withState, machine, Fin.isValue, done]
  norm_num [MultiTapeMachine.Config.step, Action.apply, Cfg.init, Cfg.withState]
  constructor <;> funext i <;> exact Fin.elim0 i

private theorem halt_seek (u : Bool) : seekSourceFrom limits sample machine (traceTwo u).hidden =
    PMF.pure (some (.ready (done u))) := by
  have hready : sourceSilent limits sample machine
      (.ready (atState 11 [] (replyOf (secondReceipt u)).word (secondMemory u))) =
      PMF.pure (.pending (.local (done u))) := by
    have hstate :
        (atState 11 [] (replyOf (secondReceipt u)).word (secondMemory u)).config.tapes.state =
          some 11 := rfl
    simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
      NativeUnboundedExecution.halted, hstate, reduceCtorEq, ite_false, phaseStep,
      Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def,
      halt_instruction]
    exact PMF.map_const _ _
  simp only [traceTwo, seekSourceFrom]
  rw [StoppedProcess.terminal_step (sourceSilent limits sample machine)
    (sourceBoundary limits) (StoppedProcess.beforeBoundary_absorbs _ _), hready, PMF.pure_bind,
    StoppedProcess.terminal_step (sourceSilent limits sample machine)
      (sourceBoundary limits) (StoppedProcess.beforeBoundary_absorbs _ _)]
  have hlocal : sourceSilent limits sample machine (.pending (.local (done u))) =
      PMF.pure (.ready (done u)) := by
    simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, phaseStep, dispatch]
  rw [hlocal, PMF.pure_bind]
  exact StoppedProcess.terminal_halted _ _ _ _ rfl

/-- Complete three-epoch trace: two issued batches followed by local native halting. -/
def traceDone (u : Bool) : Trace.State 3 0 Bool (Fin 12) [] :=
  ⟨some (.ready (done u)), [none, some (secondReceipt u), some (firstReceipt u)]⟩

private theorem halt_trace_step (u : Bool) : Trace.step limits sample machine (traceTwo u) =
    PMF.pure (traceDone u) := by
  simp only [Trace.step, halt_seek, PMF.pure_bind, Trace.respond, respondSource, phaseStep]
  have hh : (done u).config.tapes.state = none := rfl
  simp only [hh, Option.isNone_none, ite_true, PMF.pure_map]
  rfl

theorem law_three : Trace.law limits sample machine 3 start =
    (PMF.uniformOfFintype Bool).map traceDone := by
  change (Trace.law limits sample machine 2 start).bind (Trace.step limits sample machine) = _
  rw [law_two, PMF.bind_map]
  simp only [Function.comp_def, halt_trace_step]
  rfl

/-- Actual complete native terminal law follows from whole-policy transfer. -/
example : NativeUnboundedExecution.terminal machine (environment limits sample) start =
    (PMF.uniformOfFintype Bool).map (fun u => some (done u)) := by
  rw [← Trace.law_native_terminal limits sample machine start
    (NativeBatch.initial_invariant limits false)]
  change (Trace.law limits sample machine 3 start).map _ = _
  rw [law_three, PMF.map_comp]
  rfl

private theorem second_resources (u : Bool) : (secondReceipt u).duration = 3 ∧
    (secondReceipt u).tokens = (if u then 9 else 3) := by
  exact ⟨(ComplexityTests.ConcurrentBatch.second_resources u).1,
    (ComplexityTests.ConcurrentBatch.second_resources u).2.1⟩

/-- Exact whole-policy means: issued count two, bill thirteen, physical latency eight.
The epoch decision count is three and is not substituted for issued batches. -/
theorem whole_resources : Quantitative.expected limits sample machine Trace.issued 3 start = 2 ∧
    Quantitative.expected limits sample machine Trace.charge 3 start = 13 ∧
      Quantitative.expected limits sample machine Trace.duration 3 start = 8 := by
  have h₁ := first_resources true
  have h₂ := first_resources false
  have h₃ := second_resources true
  have h₄ := second_resources false
  simp only [Quantitative.expected, law_three, Quantitative.mean, PMF.tsum_map_mul]
  norm_num [tsum_bool, PMF.uniformOfFintype_apply, Trace.accrued, Trace.issued, Trace.charge,
    Trace.duration, traceDone, h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2, h₄.1, h₄.2]
  have hhalf : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  constructor
  · rw [hhalf, mul_one]
  · constructor
    · calc
        _ = (2 : ℝ≥0∞)⁻¹ * (2 * 13) := by norm_num [← mul_add]
        _ = 13 := by rw [← mul_assoc, hhalf, one_mul]
    · calc
        _ = (2 : ℝ≥0∞)⁻¹ * (2 * 8) := by norm_num [← mul_add]
        _ = 8 := by rw [← mul_assoc, hhalf, one_mul]


private theorem newest_bill_bounds (turn : ℕ) (ht : turn < 3)
    (state : Trace.State 3 0 Bool (Fin 12) [])
    (hs : state ∈ (Trace.law limits sample machine (turn + 1) start).support) :
    3 * Quantitative.newest Trace.issued state ≤ Quantitative.newest Trace.charge state ∧
      Quantitative.newest Trace.charge state ≤ 11 * Quantitative.newest Trace.issued state := by
  interval_cases turn
  · rw [law_one, PMF.mem_support_map_iff] at hs
    obtain ⟨u, _, rfl⟩ := hs
    have hr := (first_resources u).2
    cases u <;> norm_num [Quantitative.newest, traceOne, Trace.issued, Trace.charge, hr] at *
  · rw [law_two, PMF.mem_support_map_iff] at hs
    obtain ⟨u, _, rfl⟩ := hs
    have hr := (second_resources u).2
    cases u <;> norm_num [Quantitative.newest, traceTwo, Trace.issued, Trace.charge, hr] at *
  · rw [law_three, PMF.mem_support_map_iff] at hs
    obtain ⟨u, _, rfl⟩ := hs
    norm_num [Quantitative.newest, traceDone, Trace.issued, Trace.charge]

/-- Selected-epoch bounds are proved for every positive-mass full-history signal,
with hidden correlation retained, rather than supplied as a representation contract. -/
theorem conditional_bills (turn : ℕ) (ht : turn < 3) (o : Quantitative.Observation 3)
    (ho : o ∈ ((Quantitative.select limits sample machine
      (Trace.law limits sample machine turn start)).map (Quantitative.observe limits)).support) :
    3 * Quantitative.conditionalMean limits sample machine
        (Trace.law limits sample machine turn start) o Trace.issued ≤
      Quantitative.conditionalMean limits sample machine
        (Trace.law limits sample machine turn start) o Trace.charge ∧
    Quantitative.conditionalMean limits sample machine
        (Trace.law limits sample machine turn start) o Trace.charge ≤
      11 * Quantitative.conditionalMean limits sample machine
        (Trace.law limits sample machine turn start) o Trace.issued := by
  have hb (next : Trace.State 3 0 Bool (Fin 12) [])
      (hn : next ∈ (Quantitative.conditional limits sample machine
        (Trace.law limits sample machine turn start) o).support) :=
    newest_bill_bounds turn ht next
      (Quantitative.conditional_support limits sample machine _ o ho next hn)
  unfold Quantitative.conditionalMean Quantitative.mean
  constructor
  · rw [← ENNReal.tsum_mul_left]
    apply tsum_le_tsum
    intro next
    by_cases hn : next ∈ (Quantitative.conditional limits sample machine
        (Trace.law limits sample machine turn start) o).support
    · simpa only [mul_left_comm (3 : ℝ≥0∞)] using
        mul_le_mul_right (hb next hn).1
          (Quantitative.conditional limits sample machine
            (Trace.law limits sample machine turn start) o next)
    · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]
  · rw [← ENNReal.tsum_mul_left]
    apply tsum_le_tsum
    intro next
    by_cases hn : next ∈ (Quantitative.conditional limits sample machine
        (Trace.law limits sample machine turn start) o).support
    · simpa only [mul_left_comm (11 : ℝ≥0∞)] using
        mul_le_mul_right (hb next hn).2
          (Quantitative.conditional limits sample machine
            (Trace.law limits sample machine turn start) o next)
    · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]

/-- Whole-policy lower and upper resource comparisons follow from the actual
selected-before-response kernels, without any finite-policy table. -/
theorem native_comparison :
    3 * Quantitative.expected limits sample machine Trace.issued 3 start ≤
        Quantitative.expected limits sample machine Trace.charge 3 start ∧
    Quantitative.expected limits sample machine Trace.charge 3 start ≤
      11 * Quantitative.expected limits sample machine Trace.issued 3 start := by
  constructor
  · apply Quantitative.cost_lower limits sample machine 3 3 start
    intro turn ht o ho hi
    have h := (conditional_bills turn ht o ho).1
    simpa only [Quantitative.conditional_issued limits sample machine _ o ho,
      hi, ite_true, mul_one] using h
  · apply Quantitative.cost_upper limits sample machine 11 3 start
    intro turn ht o ho hi
    have h := (conditional_bills turn ht o ho).2
    simpa only [Quantitative.conditional_issued limits sample machine _ o ho,
      hi, ite_true, mul_one] using h

/-- Finite expectation is derived from the conditional envelope and actual
source turn budget, without assuming a bounded total bill or integrability. -/
theorem finite_budget_cost :
    Quantitative.expected limits sample machine Trace.charge 3 start ≤ 22 ∧
      Quantitative.expected limits sample machine Trace.charge 3 start ≠ ⊤ := by
  have he := Quantitative.cost_upper_budget limits sample machine 11 3 start
    (NativeBatch.initial_invariant limits false) (fun turn ht o ho hi => by
      have h := (conditional_bills turn ht o ho).2
      simpa only [Quantitative.conditional_issued limits sample machine _ o ho,
        hi, ite_true, mul_one, ENNReal.coe_ofNat] using h)
  norm_num [limits] at he ⊢
  exact he

/-- Empty-ground successful-output admission is preserved, including arbitrary clocks.
There are no candidate indices to fabricate, even on partial native outputs. -/
example : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
    (candidateParser (n := 3) 0) (decodeFamily 0) (fun _ => true) start := by
  intro fuel next hn C hc ha
  have he : C = ∅ := Finset.eq_empty_of_isEmpty C
  simp [he]


end ComplexityTests.NativeBatchPolicy
