/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.NativeRetention.Selector
import Complexity.Probability.StochasticOracle.NativeRetention.Execution
import Mathlib.Tactic

/-!
# Actual adaptive selection of two correlated partial covers

The first concurrent batch reveals one of two proper partial covers and charges a
canceled companion. The next query depends on the visible first proposal and must
request its complement. The oracle retains the same hidden bit across both turns.
The complete raw-interface program returns the two-set cover, rather than receiving
a successful retained family or a selector correctness contract as input.
This tests the program layer; its unbounded-reply native realization remains open.
-/

open Cslib Cslib.Probability StochasticOracle NativeRetention NativeOpenExecution
open ConcurrentBatch Selector
open scoped NNReal
namespace ComplexityTests.NativeRetentionSelector

/-- Two proper partial covers; caller-supplied proposals are deliberately bogus. -/
def input : Input := ⟨[[0], [1]], [1,1], [1,1], 1, [[99]]⟩

theorem valid : Valid input := by
  constructor
  · intro j
    rcases j with _ | (_ | j) <;> norm_num [input]
  · intro e
    rcases e with _ | (_ | e) <;> norm_num [input]
  · intro j
    rcases j with _ | (_ | j) <;>
      norm_num [elements, ground, input, List.range_succ]

/-- First batch runs two concurrent opportunities, one of which will be canceled. -/
def first : Batch 3 := ⟨fun i => if i = 2 then none else some [], by decide⟩

/-- The second query asks for the missing part, chosen only after the first reply. -/
def second (bit : Bool) : Batch 3 :=
  ⟨fun i => if i = 2 then some [!bit] else none, by cases bit <;> decide⟩

/-- Raw successful proposal masks in the original family ABI. -/
def partialWord (bit : Bool) : Word := if bit then [true,false] else [false,true]

/-- Read actual first-reply proposal data, rather than hidden scenario information. -/
def seen (s : Selector.State) : Bool :=
  (parseProposals 3 2 (s.history.headD [])).any fun C => decide ((0 : Fin 2) ∈ C)

/-- Closed deterministic scheduling code; a randomized closed program is also allowed. -/
def choose : Scheduler 3 := fun _ s =>
  pure ⟨some (if s.history.isEmpty then first else second (seen s)), s.privateState⟩

noncomputable section
/-- Positive cutoffs, two-turn bound, and sufficient absolute external deadline. -/
def limits : Limits 3 := ⟨fun _ => 2, by intro _; norm_num, 4, 2⟩

/-- Response and invoice share the actual hidden scenario. The canceled call has
no proposal but still charges three tokens and occupies its whole cutoff. -/
def paths (bit : Bool) (later correct : Bool) (i : Fin 3) : CallTrace :=
  if i = 1 then ⟨none, fun _ => 3, by intro _ _ _; exact le_rfl⟩ else
    ⟨some (1, if later then (if correct then partialWord (!bit) else []) else partialWord bit),
      fun _ => if later then 4 else 2, by intro _ _ _; exact le_rfl⟩

/-- The same hidden bit persists. A wrong second query receives no valid proposal. -/
def sample : Sampler 3 Bool := fun state batch =>
  PMF.pure (paths state.privateState (!state.history.isEmpty)
    (decide (batch.slots 2 = some [!state.privateState])), state.privateState)

/-- Exact accepted source receipts, not extra observations supplied to the program. -/
def receiptOne (bit : Bool) : Exchange 3 := observe limits 4 first (paths bit false false)

/-- Actual complementary receipt after the first batch has occupied two time units. -/
def receiptTwo (bit : Bool) : Exchange 3 :=
  observe limits 2 (second bit) (paths bit true true)

private theorem first_proposals (bit : Bool) :
    proposals 2 (receiptOne bit).report = [if bit then {0} else {1}] := by
  cases bit <;> norm_num [proposals, receiptOne, observe, paths, first, limits,
    CallTrace.report, CallTrace.response, partialWord, decodeFamily, List.ofFn_succ,
    Finset.mem_filter, List.filterMap_cons, List.filterMap_nil] <;> decide

private theorem first_duration (bit : Bool) : (receiptOne bit).duration = 2 := by
  have hf : active first.slots = {0,1} := by decide
  rw [receiptOne, Exchange.duration, show
    active (observe limits 4 first (paths bit false false)).batch.slots = {0,1} from hf]
  norm_num [observe, first, paths, CallTrace.stop, limits]

private theorem second_proposals (bit : Bool) :
    proposals 2 (receiptTwo bit).report = [if bit then {1} else {0}] := by
  cases bit <;> norm_num [proposals, receiptTwo, observe, paths, second, limits,
    CallTrace.report, CallTrace.response, partialWord, decodeFamily, List.ofFn_succ,
    Finset.mem_filter, List.filterMap_cons, List.filterMap_nil] <;> decide

private def stateOne (bit : Bool) : Selector.State :=
  ⟨[(replyOf (receiptOne bit)).word], false, [encodeBatch first], []⟩

private def stateTwo (bit : Bool) : Selector.State :=
  ⟨[(replyOf (receiptTwo bit)).word, (replyOf (receiptOne bit)).word], false,
    [encodeBatch (second bit), encodeBatch first], []⟩

private theorem data_one (bit : Bool) :
    Selector.data 3 input (stateOne bit) =
      { input with proposals := [if bit then [0] else [1]] } := by
  simp only [Selector.data, stateOne, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    replyOf, parseProposals_report]
  rw [show input.rows.length = 2 from rfl, first_proposals]
  cases bit <;> rfl

private theorem data_two (bit : Bool) :
    Selector.data 3 input (stateTwo bit) =
      { input with proposals := [if bit then [0] else [1], if bit then [1] else [0]] } := by
  simp only [Selector.data, stateTwo, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    replyOf, parseProposals_report]
  rw [show input.rows.length = 2 from rfl, first_proposals, second_proposals]
  cases bit <;> rfl


/-- Asking for the first part again yields no decodable candidate family. -/
example (bit : Bool) :
    proposals 2 (observe limits 2 (second (!bit)) (paths bit true false)).report = [] := by
  cases bit <;> norm_num [proposals, observe, paths, second, limits,
    CallTrace.report, CallTrace.response, decodeFamily, List.ofFn_succ,
    Finset.mem_filter, List.filterMap_cons, List.filterMap_nil]

/-- Raw replies alone drive the adaptive choice. Both branches first retain a
proper partial cover and issue genuinely different second query strings. -/
theorem actual_choice (bit : Bool) :
    choose (Selector.data 3 input (stateOne bit)) (stateOne bit) =
      pure ⟨some (second bit), []⟩ := by
  cases bit <;> simp [choose, seen, stateOne, replyOf, parseProposals_report, first_proposals]

/-- Both correlated paths complete by actual parsing and rational local scans. -/
theorem actual_output (bit : Bool) :
    result 3 input (stateTwo bit) =
      some [true,true] := by
  unfold result
  rw [data_two]
  cases bit <;> norm_num [complete, output, retain, NativeRetention.step, certified, newly,
    covered, NativeRetention.normalize, population, ground, cost, price, input, List.range_succ]


/-- No input proposal list can make the selector succeed before its first query. -/
example : result 3 input Selector.initial = none := by
  norm_num [result, Selector.data, Selector.initial, complete, covered, ground, retain,
    input, List.range_succ]

private def memoryZero (bit : Bool) : Memory Unit (ServerState 3 Bool) :=
  ⟨ConcurrentBatch.initial bit, []⟩

private def memoryOne (bit : Bool) : Memory Unit (ServerState 3 Bool) :=
  (memoryZero bit).record ((), encodeBatch first) (replyOf (receiptOne bit))
    (commit (ConcurrentBatch.initial bit) (receiptOne bit) bit)

private def memoryTwo (bit : Bool) : Memory Unit (ServerState 3 Bool) :=
  (memoryOne bit).record ((), encodeBatch (second bit)) (replyOf (receiptTwo bit))
    (commit (memoryOne bit).privateState (receiptTwo bit) bit)

private theorem first_step (bit : Bool) :
    transition (environment limits sample) choose input (Selector.initial, memoryZero bit) =
      PMF.pure (stateOne bit, memoryOne bit) := by
  have hd : complete (Selector.data 3 input Selector.initial) = false := by
    norm_num [Selector.data, Selector.initial, complete, covered, ground, retain,
      input, List.range_succ]
  have ha : admit limits (ConcurrentBatch.initial bit) (encodeBatch first) = some first := by
    simp [admit, decodeBatch_encode, ConcurrentBatch.initial, limits]
  simp only [transition, show Selector.initial.stopped = false from rfl, Bool.false_or,
    hd, Bool.false_eq_true, ↓reduceIte]
  rw [show choose (Selector.data 3 input Selector.initial) Selector.initial =
    pure ⟨some first, []⟩ from rfl]
  simp only [ProbComp.eval_pure, PMF.pure_bind]
  change (serve limits sample (encodeBatch first) (ConcurrentBatch.initial bit)).map _ = _
  rw [serve_accepted limits sample _ _ _ ha]
  simp only [sample, ConcurrentBatch.initial, List.isEmpty_nil, Bool.not_true,
    PMF.pure_map, tsub_zero]
  rfl

private theorem second_step (bit : Bool) :
    transition (environment limits sample) choose input (stateOne bit, memoryOne bit) =
      PMF.pure (stateTwo bit, memoryTwo bit) := by
  have hd : complete (Selector.data 3 input (stateOne bit)) = false := by
    rw [data_one]
    cases bit <;> norm_num [complete, retain, NativeRetention.step, certified, newly,
      covered, NativeRetention.normalize, population, ground, cost, price, input, List.range_succ]
  have ha : admit limits (memoryOne bit).privateState (encodeBatch (second bit)) =
      some (second bit) := by
    have hs : (receiptOne bit).batch = first := rfl
    simp only [admit, decodeBatch_encode, memoryOne, Memory.record, commit,
      ConcurrentBatch.initial, zero_add, first_duration, hs, List.length_cons, List.length_nil]
    norm_num [limits, active, first, second, Finset.disjoint_left]
  simp only [transition, show (stateOne bit).stopped = false from rfl, Bool.false_or,
    hd, Bool.false_eq_true, ↓reduceIte]
  rw [show choose (Selector.data 3 input (stateOne bit)) (stateOne bit) =
    pure ⟨some (second bit), []⟩ from actual_choice bit]
  simp only [ProbComp.eval_pure, PMF.pure_bind]
  change (serve limits sample (encodeBatch (second bit)) (memoryOne bit).privateState).map _ = _
  rw [serve_accepted limits sample _ _ _ ha]
  have hc : (second bit).slots 2 = some [!bit] := by simp [second]
  simp only [sample, memoryOne, Memory.record, commit, ConcurrentBatch.initial,
    List.isEmpty_cons, Bool.not_false, hc, decide_true, PMF.pure_map, zero_add, first_duration]
  have hrem : limits.deadline - 2 = 2 := by
    apply NNReal.eq
    norm_num [NNReal.coe_sub, limits]
  rw [hrem]
  simp only [stateTwo, memoryTwo, memoryOne, Memory.record, commit,
    ConcurrentBatch.initial, zero_add, first_duration]
  rfl

/-- End-to-end execution of the complete program on the actual guarded source,
with the same hidden state and both actual bills/latencies carried to the result. -/
theorem execute_two (bit : Bool) :
    execute (environment limits sample) (program choose input 2) (memoryZero bit) =
      PMF.pure (some [true,true], memoryTwo bit) := by
  rw [program_joint]
  change ((PMF.pure (Selector.initial, memoryZero bit)).bind
    (transition (environment limits sample) choose input) |>.bind
      (transition (environment limits sample) choose input)).map _ = _
  rw [PMF.pure_bind, first_step, PMF.pure_bind, second_step, PMF.pure_map]
  exact congrArg PMF.pure (congrArg (fun w => (w, memoryTwo bit)) (actual_output bit))

/-- Cancellation is actually billed; it neither supplies a family nor vanishes
when a different concurrent opportunity returns a useful proper partial cover. -/
example (bit : Bool) : (receiptOne bit).report 1 = some (none, 3) := by
  norm_num [receiptOne, observe, first, paths, limits, CallTrace.report,
    CallTrace.response, CallTrace.stop]

private theorem first_tokens (bit : Bool) : (receiptOne bit).tokens = 5 := by
  have hf : active first.slots = {0,1} := by decide
  rw [receiptOne, observe_tokens, hf]
  norm_num [paths]

private theorem second_tokens (bit : Bool) : (receiptTwo bit).tokens = 4 := by
  have hf : active (second bit).slots = {2} := by cases bit <;> decide
  rw [receiptTwo, observe_tokens, hf]
  norm_num [paths]

private theorem second_duration (bit : Bool) : (receiptTwo bit).duration = 1 := by
  have hf : active (second bit).slots = {2} := by cases bit <;> decide
  rw [receiptTwo, Exchange.duration, show
    active (observe limits 2 (second bit) (paths bit true true)).batch.slots = {2} from hf]
  norm_num [observe, second, paths, CallTrace.stop, limits]

/-- Exact joint resources of the same successful execution, including cancellation. -/
example (bit : Bool) : tokenBill (memoryTwo bit).events = 9 ∧
    elapsed (memoryTwo bit).events = 3 := by
  norm_num [tokenBill, elapsed, memoryTwo, memoryOne, memoryZero, Memory.record,
    replyOf, first_tokens, second_tokens, first_duration, second_duration]

/-- Random initial private state stays correlated across both queries. Output is
certain for this instance, while the complete hidden final memory retains that bit. -/
example : ((PMF.uniformOfFintype Bool).bind fun bit =>
    execute (environment limits sample) (program choose input 2) (memoryZero bit)).map Prod.fst =
      PMF.pure (some [true,true]) := by
  simp only [execute_two, PMF.map_bind, PMF.pure_map]
  exact PMF.bind_const _ _

/-- The complete client's actual emitted mask satisfies the general source theorem,
with no separately supplied admission or desired certification proof. -/
example (bit : Bool) : ∃ C : Finset (Fin input.rows.length),
    decodeFamily input.rows.length [true,true] = some C ∧
    C ⊆ NativeBatch.sourceAvailable input.rows.length (memoryTwo bit).privateState.history ∧
    (instanceOf input valid).covered (C.image Fin.val) = (instanceOf input valid).ground ∧
    (instanceOf input valid).cost (C.image Fin.val) ≤
      (input.rho : ℝ) * ∑ e ∈ (instanceOf input valid).ground, (instanceOf input valid).dual e ∧
    (memoryTwo bit).privateState.elapsed ≤ limits.deadline := by
  apply program_correct limits sample choose input valid 2 bit _ _
  rw [show (⟨ConcurrentBatch.initial bit, []⟩ : Memory Unit (ServerState 3 Bool)) =
    memoryZero bit from rfl, execute_two]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- An already complete state does not even evaluate the scheduling program. -/
example (bit : Bool) : turn choose input (stateTwo bit) =
    pure { stateTwo bit with stopped := true } := by
  apply turn_complete
  rw [data_two]
  cases bit <;> norm_num [complete, retain, NativeRetention.step, certified, newly,
    covered, NativeRetention.normalize, population, ground, cost, price, input, List.range_succ]

/-- Empty ground finishes without an oracle call even for a scheduler requesting
another batch. Initial fabricated proposals are still ignored. -/
example {Private : Type} (env : Environment Unit Private) (memory : Memory Unit Private) :
    execute env (program choose ⟨[], [], [], 1, [[0]]⟩ 1) memory =
      PMF.pure (some [], memory) := by
  simp [Selector.execute, program, run, OracleComp.iterate_succ, OracleComp.iterate_zero,
    turn, result, Selector.initial, Selector.data, complete, ground, output, population,
    OracleComp.interpret_pure, StateT.run_pure]

/-- A policy may retain its private coin even when it explicitly halts. The oracle
cannot observe this draw, and its entire resource ledger is left untouched. -/
def saveCoin : Scheduler 3 := fun _ s => do
  let coin ← ProbComp.uniform Bool
  pure ⟨none, s.privateState ++ [coin]⟩

example {Private : Type} (env : Environment Unit Private) (memory : Memory Unit Private) :
    execute env (turn saveCoin input Selector.initial) memory =
      (PMF.uniformOfFintype Bool).map fun coin =>
        ((⟨[], true, [], [coin]⟩ : Selector.State), memory) := by
  rw [turn_joint]
  have hd : complete (Selector.data 3 input Selector.initial) = false := by
    norm_num [Selector.data, Selector.initial, complete, covered, ground, retain,
      input, List.range_succ]
  simp only [transition, show Selector.initial.stopped = false from rfl, Bool.false_or,
    hd, Bool.false_eq_true, ↓reduceIte, saveCoin, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  rw [PMF.bind_bind]
  simp only [PMF.pure_bind]
  rfl

end
end ComplexityTests.NativeRetentionSelector
