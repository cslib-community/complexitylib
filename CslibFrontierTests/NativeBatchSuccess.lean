/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontierTests.NativeBatchProgress
import CslibFrontierTests.NativeBatchSingleton
import CslibFrontierTests.NativeBatchProgram
import CslibFrontier.Computability.Probabilistic.NativeBatch.Deadline
import Mathlib.Tactic

/-!
# Successful admitted native selection policy and the source cost lower bound

The machine writes a real packet, issues its sole opportunity, then writes a
covering output. Admission follows from the actual terminal law and concrete
response codec. All source envelopes are discharged, including the final no-call
halting epoch. This is a nonempty, probability-one edge client, not a uniform selector.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle ConcurrentBatch PartialCover AdaptiveSelection
open Cslib.Probability.NativeBatch
open scoped ENNReal NNReal
namespace CslibFrontierTests.NativeBatchSuccess
open CslibFrontierTests.NativeBatchSingleton
open CslibFrontierTests.NativeBatchProgram (machine world)

/-- Ordinary initial machine configuration and empty source memory. -/
def start : World 0 (Fin 4) Unit (ServerState 1 Unit) [] :=
  ⟨machine.initialConfig [], ⟨ConcurrentBatch.initial (), []⟩⟩

/-- Actual native boundary after writing the complete request packet. -/
def queried := world (some 2) (encodeBatch batch) [] [] start.memory

/-- Actual recorded reply and committed source ledger. -/
def memory : Memory Unit (ServerState 1 Unit) := start.memory.record ((), encodeBatch batch)
  (replyOf receipt) (commit start.memory.privateState receipt ())

/-- Native continuation after receiving the oracle response. -/
def answered := world (some 3) [] (replyOf receipt).word [] memory

/-- Actual halted world with the encoded singleton family on its output tape. -/
def done := world none [] (replyOf receipt).word [true] memory

/-- Actual first-epoch receipt and native continuation. -/
def firstTrace : Trace.State 1 0 Unit (Fin 4) [] :=
  ⟨some (.ready answered), [some receipt]⟩

/-- The actual output/halting epoch retains the preceding receipt. -/
def finalTrace : Trace.State 1 0 Unit (Fin 4) [] :=
  ⟨some (.ready done), [none, some receipt]⟩

private theorem admit_first : admit limits start.memory.privateState (encodeBatch batch) =
    some batch := by
  simp [admit, decodeBatch_encode, start, ConcurrentBatch.initial, limits]

private theorem seek_first : seekSourceFrom limits sample machine (some (.ready start)) =
    PMF.pure (some (.pending (.query queried () 3))) := by
  exact NativeBatchProgram.seek_first sample start.memory admit_first

private theorem dispatch_first : dispatch (environment limits sample) (.query queried () 3) =
    PMF.pure answered := by
  simp only [dispatch, environment, queried, world]
  rw [serve, admit_first]
  have hd : limits.deadline - start.memory.privateState.elapsed = 2 := by
    norm_num [limits, start, ConcurrentBatch.initial]
  simp only [sample, PMF.pure_map, hd, answered, memory, receipt, world,
    MultiTapeMachine.Config.receive, Function.update_eq_const_of_subsingleton]
  rfl

private theorem seek_last : seekSourceFrom limits sample machine (some (.ready answered)) =
    PMF.pure (some (.ready done)) := by
  exact NativeBatchProgram.seek_output sample memory (replyOf receipt).word

private theorem step_first : Trace.step limits sample machine (Trace.initial start) =
    PMF.pure firstTrace := by
  simp only [Trace.step, Trace.initial, seek_first, PMF.pure_bind, Trace.respond,
    respondSource, phaseStep, dispatch_first, PMF.pure_map]
  rfl

private theorem step_last : Trace.step limits sample machine firstTrace = PMF.pure finalTrace := by
  simp only [Trace.step, firstTrace, seek_last, PMF.pure_bind, Trace.respond, respondSource,
    phaseStep]
  have hh : done.config.tapes.state = none := rfl
  simp only [hh, Option.isNone_none, ite_true, PMF.pure_map]
  rfl

private theorem law_one : Trace.law limits sample machine 1 start = PMF.pure firstTrace := by
  simp [Trace.law, ObservedProcess.stateLaw, step_first]
private theorem law_two : Trace.law limits sample machine 2 start = PMF.pure finalTrace := by
  change (Trace.law limits sample machine 1 start).bind (Trace.step limits sample machine) = _
  rw [law_one, PMF.pure_bind, step_last]

/-- Concrete packet-writing, response and output code terminates with its actual cover. -/
theorem terminal_law : NativeUnboundedExecution.terminal machine (environment limits sample)
    start = PMF.pure (some done) := by
  rw [← Trace.law_native_terminal limits sample machine start
    (NativeBatch.initial_invariant limits ())]
  change (Trace.law limits sample machine 2 start).map _ = _
  rw [law_two, PMF.pure_map]
  rfl

/-- Successful-output-only admission is proved for every actual finite clock;
it is not a representation or provenance premise for this concrete client. -/
theorem admitted : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
    (candidateParser (n := 1) 1) (decodeFamily 1) (Coverage.coverAccept coverInstance) start := by
  intro fuel next hn C hc _
  have hh : NativeUnboundedExecution.halted next := by
    by_contra hh
    simp only [NativeUnboundedExecution.halted] at hh
    simp [NativeOpenSelection.result, hh] at hc
  have ht := (NativeUnboundedExecution.terminal_support machine
    (environment limits sample) start next).mpr ⟨hh, fuel, hn⟩
  rw [terminal_law, PMF.mem_support_pure_iff, Option.some.injEq] at ht
  subst next
  have hC : C = {0} := by
    simpa [NativeOpenSelection.result, done, world, decodeFamily] using hc.symm
  subst C
  rw [candidateParser_proposals]
  have hi := NativeBatch.terminal_invariant limits sample machine start done
    (NativeBatch.initial_invariant limits ()) (by simp [terminal_law])
  rw [hi.2.2.2]
  simp [done, world, memory, Memory.record, commit, sourceAvailable, receipt_proposals,
    start, ConcurrentBatch.initial]

/-- The actual nonempty covering result has probability one. -/
theorem success_probability : ((Trace.law limits sample machine 2 start).map
    (Coverage.success (Coverage.coverAccept coverInstance))) true = 1 := by
  rw [law_two, PMF.pure_map]
  norm_num [Coverage.success, finalTrace, NativeOpenSelection.result, done, world,
    decodeFamily, Coverage.coverAccept, coverInstance, Instance.covered, PMF.pure_apply]

private def firstSelection : Quantitative.Selected 1 0 Unit (Fin 4) [] :=
  ⟨Trace.initial start, some (.pending (.query queried () 3))⟩
private def lastSelection : Quantitative.Selected 1 0 Unit (Fin 4) [] :=
  ⟨firstTrace, some (.ready done)⟩

private theorem select_first : Quantitative.select limits sample machine
    (PMF.pure (Trace.initial start)) = PMF.pure firstSelection := by
  simp [Quantitative.select, Trace.initial, seek_first, firstSelection]

private theorem select_last : Quantitative.select limits sample machine
    (PMF.pure firstTrace) = PMF.pure lastSelection := by
  simp [Quantitative.select, firstTrace, seek_last, lastSelection]

private theorem cost_envelope : ∀ t < 2, ∀ o ∈ ((Quantitative.select limits sample machine
      (Trace.law limits sample machine t start)).map (Quantitative.observe limits)).support,
    o.issued = true → Quantitative.conditionalMean limits sample machine
      (Trace.law limits sample machine t start) o Trace.charge = 2 := by
  intro t ht o ho hi
  interval_cases t
  · change o ∈ ((Quantitative.select limits sample machine
      (PMF.pure (Trace.initial start))).map (Quantitative.observe limits)).support at ho
    rw [select_first, PMF.pure_map, PMF.mem_support_pure_iff] at ho
    subst o
    have h := Quantitative.selection_factor limits sample machine (PMF.pure (Trace.initial start))
    rw [select_first, PMF.pure_map, PMF.pure_bind, PMF.pure_bind, step_first] at h
    change Quantitative.mean (Quantitative.conditional limits sample machine
      (PMF.pure (Trace.initial start)) (Quantitative.observe limits firstSelection)) _ = 2
    rw [h]
    norm_num [Quantitative.mean, Quantitative.newest, firstTrace, Trace.charge, PMF.pure_apply,
      receipt, Exchange.tokens, batch, active, limits, path, ConcurrentBatch.observe,
      CallTrace.stop, CallTrace.report, CallTrace.response]
  · rw [law_one, select_last, PMF.pure_map, PMF.mem_support_pure_iff] at ho
    subst o
    change false = true at hi
    cases hi

private theorem cap_envelope : ∀ t < 2, ∀ o ∈ ((Quantitative.select limits sample machine
      (Trace.law limits sample machine t start)).map (Quantitative.observe limits)).support,
    ∀ next ∈ (Quantitative.conditional limits sample machine
      (Trace.law limits sample machine t start) o).support,
      (revealed coverInstance (Coverage.proposal 1) next.records \
        revealed coverInstance (Coverage.proposal 1) o.history).card ≤ 1 := by
      intro t ht o ho next hn
      calc
        _ ≤ (revealed coverInstance (Coverage.proposal 1) next.records).card :=
          Finset.card_le_card Finset.sdiff_subset
        _ ≤ coverInstance.ground.card := by
          apply Finset.card_le_card
          rw [Coverage.revealed_source]
          exact coverInstance.covered_subset _
        _ = 1 := by simp [coverInstance]

private theorem progress_envelope : ∀ t < 2, ∀ o ∈ ((Quantitative.select limits sample machine
      (Trace.law limits sample machine t start)).map (Quantitative.observe limits)).support,
    o.issued = true → History.conditionalMean limits sample machine
      (Trace.law limits sample machine t start) o
      (fun h x => if reveals coverInstance (Coverage.proposal 1) h x then 1 else 0) ≤ 1 := by
      intro t ht o ho hi
      unfold History.conditionalMean Quantitative.mean
      calc
        _ ≤ ∑' next, Quantitative.conditional limits sample machine
            (Trace.law limits sample machine t start) o next * 1 := by
          apply tsum_le_tsum
          intro next
          apply mul_le_mul_right
          unfold History.newest
          dsimp only
          split_ifs <;> norm_num
        _ = 1 := by simp [PMF.tsum_coe]

/-- The genuine success-level lower endpoint is instantiated with proved
admission and actual reached-history source envelopes, giving a positive bound. -/
example : 2 ≤ Quantitative.expected limits sample machine Trace.charge 2 start := by
  have h := Coverage.success_cost_lower limits sample machine coverInstance 1 1 1 2
    (by
      intro q hq
      have hq0 : q = 0 := by omega
      subst q
      simp [coverInstance])
    start (NativeBatch.initial_invariant limits ()) rfl (Coverage.coverAccept coverInstance)
    (by intro C hC; simpa [Coverage.coverAccept] using hC) admitted
    cap_envelope progress_envelope
    (by norm_num) (by norm_num)
    (fun t ht o ho hi => (cost_envelope t ht o ho hi).ge)
  rw [← Coverage.success_law limits sample machine (Coverage.coverAccept coverInstance) start
    (NativeBatch.initial_invariant limits ())] at h
  simpa only [show limits.turns + 1 = 2 from rfl, Nat.cast_one,
    success_probability, mul_one, one_mul, div_one] using h

/-- Native completion uses one issued trial, although full output needs the
second silent halting epoch. The source success event is the original native one. -/
example : (NativeUnboundedExecution.terminal machine (environment limits sample) start).map
    (Coverage.nativeSuccess (Coverage.coverAccept coverInstance)) true ≤ ENNReal.ofReal
      (∫ j, (if 1 ≤ j then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial 1 ⟨1, by norm_num⟩) :=
  Coverage.success_binomial limits sample machine coverInstance 1 1
    (by
      intro q hq
      have hq0 : q = 0 := by omega
      subst q
      simp [coverInstance])
    start (NativeBatch.initial_invariant limits ()) rfl (Coverage.coverAccept coverInstance)
    (by intro C hC; simpa [Coverage.coverAccept] using hC) admitted cap_envelope
    ⟨1, by norm_num⟩ (fun t ht o ho hi => by
      simpa using progress_envelope t (by change t < 1 at ht; omega) o ho hi)

private theorem productive_first : productive coverInstance 1 (Coverage.proposal 1) 1
    [] (some receipt) = true := by
  norm_num [productive, AdaptiveSelection.residual, selected, Coverage.proposal,
    receipt_proposals, Instance.retain, Instance.Certified, coverInstance,
    Instance.covered, Instance.cost]

/-- The actual successful native code, including its halting padding, has the
source productivity envelope. This does not assume a completion probability. -/
private theorem productivity_envelope : ∀ t < 2, ∀ o ∈ ((Quantitative.select limits sample machine
      (Trace.law limits sample machine t start)).map (Quantitative.observe limits)).support,
    ENNReal.ofReal (1 : ℝ) ≤ History.conditionalMean limits sample machine
      (Trace.law limits sample machine t start) o
      (fun h x => if productive coverInstance 1 (Coverage.proposal 1) 1 h x then 1 else 0) := by
  intro t ht o ho
  interval_cases t
  · change o ∈ ((Quantitative.select limits sample machine
      (PMF.pure (Trace.initial start))).map (Quantitative.observe limits)).support at ho
    rw [select_first, PMF.pure_map, PMF.mem_support_pure_iff] at ho
    subst o
    have h := Quantitative.selection_factor limits sample machine (PMF.pure (Trace.initial start))
    rw [select_first, PMF.pure_map, PMF.pure_bind, PMF.pure_bind, step_first] at h
    change _ ≤ Quantitative.mean (Quantitative.conditional limits sample machine
      (PMF.pure (Trace.initial start)) (Quantitative.observe limits firstSelection)) _
    rw [h]
    simp only [Quantitative.mean, PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
    simp [History.newest, firstTrace, productive_first]
  · rw [law_one, select_last, PMF.pure_map, PMF.mem_support_pure_iff] at ho
    subst o
    have h := Quantitative.selection_factor limits sample machine (PMF.pure firstTrace)
    rw [select_last, PMF.pure_map, PMF.pure_bind, PMF.pure_bind, step_last] at h
    change _ ≤ Quantitative.mean (Quantitative.conditional limits sample machine
      (Trace.law limits sample machine 1 start) (Quantitative.observe limits lastSelection)) _
    rw [law_one, h]
    simp only [Quantitative.mean, PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
    norm_num [History.newest, finalTrace, productive,
      AdaptiveSelection.residual, selected, Coverage.proposal, receipt_proposals,
      Instance.retain, Instance.Certified, coverInstance, Instance.covered, Instance.cost]

/-- The upper tail-sum/mean theorem also applies through native output and
halting. Both bounds equal the actual invoice in this nonempty `p = 1` case. -/
example : Quantitative.expected limits sample machine Trace.charge 2 start ≤ 2 := by
  have h := Retained.complete_cost_mean limits sample machine coverInstance 1
    (Coverage.proposal 1) 1 1
    (by simp [coverInstance]) ⟨1, by norm_num⟩ (by norm_num) 2 start
    (NativeBatch.initial_invariant limits ())
    (fun t ht => productivity_envelope t (by change t < 1 at ht; omega))
    (by
      intro t ht o ho hi
      have ht0 : t = 0 := by change t < 1 at ht; omega
      subst t
      change o ∈ ((Quantitative.select limits sample machine
        (PMF.pure (Trace.initial start))).map (Quantitative.observe limits)).support at ho
      rw [select_first, PMF.pure_map, PMF.mem_support_pure_iff] at ho
      subst o
      norm_num [Quantitative.observe, firstSelection, Trace.initial, Retained.complete,
        selected, coverInstance, Instance.covered])
    (fun t ht o ho hi => (cost_envelope t (by change t < 1 at ht; omega) o ho hi).le)
  simpa only [show limits.turns + 1 = 2 from rfl, Nat.cast_one, one_div, inv_one, mul_one,
    ENNReal.ofReal_one] using h

private theorem latency_envelope : Deadline.LowerLatency limits sample machine start 1 := by
  intro t ht o ho hi next hn
  have hs := Quantitative.conditional_support limits sample machine
    (Trace.law limits sample machine t start) o ho next hn
  have ht' : t < 2 := ht
  interval_cases t
  · change next ∈ (Trace.law limits sample machine 1 start).support at hs
    rw [law_one, PMF.mem_support_pure_iff] at hs
    subst next
    norm_num [firstTrace, receipt, Exchange.duration, ConcurrentBatch.observe, limits,
      batch, path, active, CallTrace.stop, CallTrace.response]
  · change next ∈ (Trace.law limits sample machine 2 start).support at hs
    rw [law_two, PMF.mem_support_pure_iff] at hs
    subst next
    have he := Quantitative.conditional_record_isSome limits sample machine _ o ho finalTrace hn
    rw [hi] at he
    cases he

/-- The assembled native source lower transfer applies to the actual successful
packet-writing/output code, its proved admission and all four reached envelopes. -/
example :
    (((NativeUnboundedExecution.terminal machine (environment limits sample) start).map
        (Deadline.nativeByDeadline (Coverage.coverAccept coverInstance) limits.deadline)
      true) * 1 * 2) / 1 ≤
      Quantitative.expected limits sample machine Trace.charge (limits.turns + 1) start ∧
    (NativeUnboundedExecution.terminal machine (environment limits sample) start).map
        (Deadline.nativeByDeadline (Coverage.coverAccept coverInstance) limits.deadline)
      true ≤ ENNReal.ofReal
      (∫ j, (if 1 ≤ j then (1 : ℝ) else 0)
        ∂ProbabilityTheory.binomial (Deadline.effectiveTurns limits 1) ⟨1, by norm_num⟩) := by
  simpa only [ENNReal.ofReal_one, Nat.cast_one] using
    Deadline.lower_guarantees limits sample machine
    coverInstance 1 1
    (by
      intro q hq
      have hq0 : q = 0 := by omega
      subst q
      simp [coverInstance])
    start (NativeBatch.initial_invariant limits ()) rfl (Coverage.coverAccept coverInstance)
    (by intro C hC; simpa [Coverage.coverAccept] using hC) admitted
    ⟨1, by norm_num⟩ (by norm_num) 2 1 (by norm_num) cap_envelope
    (fun t ht o ho hi => by simpa using progress_envelope t ht o ho hi)
    (fun t ht o ho hi => (cost_envelope t ht o ho hi).ge) latency_envelope

/-- Adding the real native elapsed-deadline test preserves this constructed
machine's positive accepted mass; the event is not merely retained coverage. -/
example : (NativeUnboundedExecution.terminal machine (environment limits sample) start).map
    (Deadline.nativeByDeadline (Coverage.coverAccept coverInstance) limits.deadline) true = 1 := by
  rw [Deadline.deadline_success_law limits sample machine _ start
    (NativeBatch.initial_invariant limits ()),
    ← Coverage.success_law limits sample machine _ start (NativeBatch.initial_invariant limits ())]
  exact success_probability

end CslibFrontierTests.NativeBatchSuccess
