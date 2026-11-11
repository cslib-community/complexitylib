/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCoverNativeRisk
import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.TokenBounds
import Mathlib.Tactic

/-!
# Every call-count vector on the same native controller

[Wang2027], Theorem 4, first sentence, PDF pp. 10–11. Supplied original-oracle
occurrences are runtime data of the same controller as the computed greedy mode.
The inherited source input has nonempty finite ground. Each occurrence has its own
fresh concurrent opportunity. Zero calls stop before
querying; nonempty calls enter the actual source-admitted native episode.

## Main definitions

* `vectorCalls`, `withCounts`: a source count vector and its original-index batch input.

## Main results

* `chances_vector`: eligible counts equal the source sum over original oracles.
* `native_risk_all`: actual certified tape-risk bound, including the empty batch.
* `native_resources_all`: actual terminal bill and oracle deadline for every batch.
* `vector_guarantee`: the assembled source every-vector native success/bill/deadline claim.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.PartialCover.NativeExecution
open Turing NativeOpenExecution ConcurrentBatch NativeRetention
open scoped NNReal ENNReal

/-- Expand source counts in original oracle order; repetitions are separate calls. -/
@[expose] def vectorCalls (x : Input) (ζ : Fin x.planner.val.rows.length → ℕ) : List ℕ :=
  (List.finRange x.planner.val.rows.length).flatMap fun i => List.replicate (ζ i) i.val

/-- Each original oracle occurs exactly the supplied number of times. -/
theorem vectorCalls_count (x : Input) (ζ : Fin x.planner.val.rows.length → ℕ)
    (i : Fin x.planner.val.rows.length) : (vectorCalls x ζ).count i.val = ζ i := by
  simp [vectorCalls, List.count_flatMap, List.count_replicate, List.finRange,
    List.map_ofFn, List.sum_ofFn, Fin.val_inj]

/-- Runtime input of an arbitrary source batch, without a supplied admission law. -/
@[expose] def withCounts (x : Input) (ζ : Fin x.planner.val.rows.length → ℕ) : Input :=
  { x with
    calls := some (vectorCalls x ζ)
    calls_valid := by
      intro ls hs j hj
      cases hs
      obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hj
      have he : j = i.val := (List.mem_replicate.mp hi).2
      subst j
      exact i.isLt }

/-- The same native selector executes precisely the supplied source count vector. -/
theorem labels_withCounts (x : Input) (ζ : Fin x.planner.val.rows.length → ℕ) :
    labels (withCounts x ζ) = vectorCalls x ζ := rfl

/-- Source eligible-call counts, without independence or homogeneity premises. -/
theorem chances_vector (x : Input) (ζ : Fin x.planner.val.rows.length → ℕ) (e : ℕ) :
    Instance.chances e (eligible (withCounts x ζ)) =
      ∑ i : Fin x.planner.val.rows.length,
        if e ∈ (GreedyNative.oracleAt x.planner.val i.val).eligible.image Fin.val
          then ζ i else 0 := by
  simp only [eligible, labels_withCounts, vectorCalls, List.map_flatMap, List.map_replicate]
  rw [Instance.chances_batch]
  simp [List.finRange, List.map_ofFn, List.sum_ofFn, withCounts]

/-- The actual risk transfer applies to every runtime batch, including zero calls.
The only stochastic premise is the source reached-history envelope, evaluated
using posterior kernels derived from this same joint oracle sample. -/
theorem native_risk_all {P : Type} (x : Input) (hx : Valid x.system)
    (limits : Limits (labels x).length) (sample : Sampler (labels x).length P) (seed : P)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns) {p : ℝ}
    (hp : 0 ≤ p) (hpone : p ≤ 1)
    (had : ∀ hs : RuntimeControl.stopped (initial x) = false,
      (sourceInstance x hx).Admissible x.system.rho p
        (Disintegration.kernel (sample (ConcurrentBatch.initial seed)
          (batch x (live_nonempty x hs))) (response x limits hs)) [] ∅ (eligible x)) :
    max 0 (1 - ∑ e ∈ (instanceOf x.system hx).ground,
      (1 - p) ^ Instance.chances e (eligible x)) ≤
      ((((NativeUnboundedExecution.terminal controller.program (environment limits sample)
        ⟨controller.program.initialConfig (encoding x), ⟨ConcurrentBatch.initial seed, []⟩⟩).map
          (Option.map (NativeReplyContext.observe controller.context))).map
            (certified x hx limits.deadline)) true).toReal := by
  cases hs : RuntimeControl.stopped (initial x) with
  | false => exact native_risk x hx limits sample seed hs hd ht hp hpone (had hs)
  | true =>
    have hz : labels x = [] := by
      apply List.length_eq_zero_iff.mp
      by_contra hn
      have h := startup_live_of_nonempty x (Nat.pos_of_ne_zero hn)
      simp [hs] at h
    have hn : 0 < x.system.dual.length := by
      change 0 < x.source.dual.length
      rw [← x.ground_eq]
      exact x.planner.property.ground_pos
    have hnonpos : (1 : ℝ) - x.system.dual.length ≤ 0 := by
      have h : (1 : ℝ) ≤ x.system.dual.length := by exact_mod_cast hn
      linarith
    have hleft : max 0 (1 - ∑ e ∈ (instanceOf x.system hx).ground,
        (1 - p) ^ Instance.chances e (eligible x)) = 0 := by
      simp only [eligible, hz, List.map_nil, Instance.chances, List.filter_nil,
        List.length_nil, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hc : (instanceOf x.system hx).ground.card = x.system.dual.length := by
        simp [instanceOf, ground, List.toFinset_range]
      rw [hc]
      exact max_eq_left hnonpos
    rw [hleft]
    exact ENNReal.toReal_nonneg

/-- All native terminal outcomes have the source sum-of-caps bill and oracle
maximum-latency bound. The zero-call case preserves the empty event ledger. -/
theorem native_resources_all {P : Type} (x : Input)
    (limits : Limits (labels x).length) (sample : Sampler (labels x).length P) (seed : P)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns)
    (caps : ℕ → ℝ)
    (hcap : ∀ hs : RuntimeControl.stopped (initial x) = false,
      ∀ pair ∈ (sample (ConcurrentBatch.initial seed) (batch x (live_nonempty x hs))).support,
      ∀ i, ((pair.1 i).accrued (limits.cutoff i) : ℝ) ≤
        caps ((labels x).get i))
    (outcome : Option (NativeReplyContext.Observation (ServerState (labels x).length P)))
    (houtcome : outcome ∈ ((NativeUnboundedExecution.terminal controller.program
      (environment limits sample) ⟨controller.program.initialConfig (encoding x),
        ⟨ConcurrentBatch.initial seed, []⟩⟩).map
          (Option.map (NativeReplyContext.observe controller.context))).support) :
    ∃ final, outcome = some final ∧
      (tokenBill final.memory.events : ℝ) ≤ ((labels x).map caps).sum ∧
      elapsed final.memory.events ≤ limits.deadline ∧ final.memory.events.length ≤ 1 := by
  cases hs : RuntimeControl.stopped (initial x) with
  | false =>
    rw [source_law x limits sample seed hs hd ht] at houtcome
    obtain ⟨⟨paths, next⟩, hp, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp houtcome
    have hb := observe_tokens_le limits limits.deadline (batch x (live_nonempty x hs)) paths
      (fun i => caps ((labels x).get i)) (fun i _ => hcap hs _ hp i)
    rw [show active (batch x (live_nonempty x hs)).slots = Finset.univ from active_slots x] at hb
    have hsum : (∑ i, caps ((labels x).get i)) = ((labels x).map caps).sum := by
      rw [← List.sum_ofFn]
      exact congrArg List.sum (List.ofFn_getElem_eq_map (labels x) caps)
    rw [hsum] at hb
    refine ⟨_, rfl, ?_, ?_, by norm_num [finished, Memory.record]⟩
    · simpa only [finished, Memory.record, tokenBill, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, replyOf, NNReal.coe_natCast] using hb
    · simpa only [finished, Memory.record, elapsed, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, replyOf] using
          observe_duration_le limits limits.deadline (batch x (live_nonempty x hs)) paths
  | true =>
    have hz : labels x = [] := by
      apply List.length_eq_zero_iff.mp
      by_contra hn
      have h := startup_live_of_nonempty x (Nat.pos_of_ne_zero hn)
      simp [hs] at h
    rw [stopped_law _ x _ hs] at houtcome
    have he : outcome = some (⟨tapeOfList (RuntimeControl.packet (initial x)),
        RuntimeControl.result (initial x), ⟨ConcurrentBatch.initial seed, []⟩⟩ :
          NativeReplyContext.Observation (ServerState (labels x).length P)) := by
      simpa using houtcome
    refine ⟨_, he, ?_, ?_, by norm_num⟩
    · simp [tokenBill, hz]
    · simp [elapsed]

/-- The source sum `c(ζ)`, charging every repeated original oracle call. -/
theorem bill_vector (x : Input) (ζ : Fin x.planner.val.rows.length → ℕ) :
    Cslib.Algorithms.Lean.Multicover.bill
      ((labels (withCounts x ζ)).map (GreedyNative.oracleAt x.planner.val)) =
        ∑ i : Fin x.planner.val.rows.length,
          (GreedyNative.oracleAt x.planner.val i.val).cost * (ζ i : ℚ) := by
  simp [labels_withCounts, vectorCalls, Cslib.Algorithms.Lean.Multicover.bill,
    List.map_replicate, List.flatMap_def, List.sum_flatten, List.sum_replicate,
    List.finRange, List.map_ofFn, List.sum_ofFn, nsmul_eq_mul, mul_comm]

/-- Analytic per-call bounds may be real; the native batch need not encode them. -/
theorem caps_vector (x : Input) (ζ : Fin x.planner.val.rows.length → ℕ) (caps : ℕ → ℝ) :
    ((labels (withCounts x ζ)).map caps).sum =
      ∑ i : Fin x.planner.val.rows.length, caps i.val * (ζ i : ℝ) := by
  simp [labels_withCounts, vectorCalls, List.map_replicate,
    List.flatMap_def, List.sum_flatten, List.sum_replicate,
    List.finRange, List.map_ofFn, List.sum_ofFn, nsmul_eq_mul, mul_comm]

/-- Actual full native law; this definition fixes the program and complete memory,
not a supplied representation or successful-output contract. -/
@[expose] def terminalLaw {P : Type} (x : Input) (limits : Limits (labels x).length)
    (sample : Sampler (labels x).length P) (seed : P) :=
  (NativeUnboundedExecution.terminal controller.program (environment limits sample)
    ⟨controller.program.initialConfig (encoding x), ⟨ConcurrentBatch.initial seed, []⟩⟩).map
      (Option.map (NativeReplyContext.observe controller.context))

/-- Theorem 4's every-vector clause for actual native execution, from original
binary WSC promises and the reached posterior envelopes on that same oracle.
The per-outcome bill bound includes zero calls and canceled-call charges. -/
theorem vector_guarantee {P : Type} (x : Input)
    (ζ : Fin x.planner.val.rows.length → ℕ) (hx : SourceEncoding.Valid x.source)
    (limits : Limits (labels (withCounts x ζ)).length)
    (sample : Sampler (labels (withCounts x ζ)).length P) (seed : P)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns) {p : ℝ}
    (hp : 0 ≤ p) (hpone : p ≤ 1)
    (had : ∀ hs : RuntimeControl.stopped (initial (withCounts x ζ)) = false,
      (sourceInstance (withCounts x ζ) (SourceEncoding.valid_toNative x.source hx)).Admissible
        x.system.rho p (Disintegration.kernel (sample (ConcurrentBatch.initial seed)
          (batch (withCounts x ζ) (live_nonempty (withCounts x ζ) hs)))
          (response (withCounts x ζ) limits hs)) [] ∅ (eligible (withCounts x ζ)))
    (caps : ℕ → ℝ)
    (hcap : ∀ hs : RuntimeControl.stopped (initial (withCounts x ζ)) = false,
      ∀ pair ∈ (sample (ConcurrentBatch.initial seed)
        (batch (withCounts x ζ) (live_nonempty (withCounts x ζ) hs))).support,
      ∀ i, ((pair.1 i).accrued (limits.cutoff i) : ℝ) ≤
        caps ((labels (withCounts x ζ)).get i)) :
    let data := withCounts x ζ
    let valid := SourceEncoding.valid_toNative x.source hx
    max 0 (1 - ∑ e ∈ (instanceOf data.system valid).ground,
      (1 - p) ^ (∑ i : Fin x.planner.val.rows.length,
        if e ∈ (GreedyNative.oracleAt x.planner.val i.val).eligible.image Fin.val
          then ζ i else 0)) ≤
        (((terminalLaw data limits sample seed).map (certified data valid limits.deadline))
          true).toReal ∧
    ∀ outcome ∈ (terminalLaw data limits sample seed).support,
      ∃ final, outcome = some final ∧
        (tokenBill final.memory.events : ℝ) ≤
          (∑ i : Fin x.planner.val.rows.length, caps i.val * (ζ i : ℝ)) ∧
        elapsed final.memory.events ≤ limits.deadline ∧ final.memory.events.length ≤ 1 := by
  dsimp only [terminalLaw]
  constructor
  · have h := native_risk_all (withCounts x ζ) (SourceEncoding.valid_toNative x.source hx)
      limits sample seed hd ht hp hpone had
    simpa only [chances_vector] using h
  · intro outcome houtcome
    obtain ⟨final, he, hb, hdur, ht⟩ := native_resources_all (withCounts x ζ)
      limits sample seed hd ht caps hcap outcome houtcome
    refine ⟨final, he, ?_, hdur, ht⟩
    change (tokenBill final.memory.events : ℝ) ≤
      ((labels (withCounts x ζ)).map caps).sum at hb
    rw [caps_vector] at hb
    exact hb

end Cslib.Probability.StochasticOracle.PartialCover.NativeExecution
