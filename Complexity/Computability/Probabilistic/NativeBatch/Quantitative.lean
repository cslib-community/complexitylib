/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeBatch.Trace
public import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Disintegration.Support
import Mathlib.Tactic

/-!
# Whole-policy quantitative transfer for actual native source epochs

[Wang2027], Theorem 5(2), PDF p. 12, Appendix A.5 p. 16: the tower property
applies after selecting the batch and before its response. These kernels are
derived from actual complete native source-epoch traces against a single fixed
oracle sampler. All histories and hidden metadata may be infinite discrete types;
no finite table, public latent-scenario label or representation identity is assumed.

Nonnegative extended expectations allow unbounded charges without assuming
integrability. Accrued receipts persist after silent divergence. This module
establishes whole-policy accounting and transfers local conditional resource
comparisons, not the remaining source success/count/binomial/certification bounds.

## Main results

* `selection_factor`: actual complete policy law, conditioned after source-batch selection.
* `expected_accrued`: accrued resources equal the sum of selected conditional expectations.
* `conditional_comparison`: local supported epoch comparisons transfer to the whole policy.
* `cost_upper_budget`: finite total expectation derived from conditional envelopes.
* `universal_cost_lower`: one fixed oracle and seed, every admitted native competitor.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Quantitative
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing Trace
open scoped ENNReal NNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)
variable (machine : MultiTapePTM k Bool Control Unit)

/-- Actual pre-response hidden checkpoint and its retained earlier source receipts. -/
structure Selected (n k : ℕ) (Private Control : Type) (input : List Bool) where
  /-- Whole native trace before seeking the next source batch. -/
  before : State n k Private Control input
  /-- Actual next source boundary, or silent divergence. -/
  checkpoint : Option (Phase k Control Unit (ServerState n Private) input)

/-- Full reached receipt history and actual selected source signal, before response. -/
structure Observation (n : ℕ) where
  /-- Previous receipts include zero-call halt/divergence decisions. -/
  history : List (Record n)
  /-- The previous accepted source history and whole preformed batch, or halt/divergence. -/
  signal : Option (List (Exchange n) × Option (Batch n))

/-- Run actual silent code without dispatching the selected source batch. -/
@[expose] def select (prior : PMF (State n k Private Control input)) :
    PMF (Selected n k Private Control input) := do
  let state ← prior
  let hit ← seekSourceFrom limits sample machine state.hidden
  pure ⟨state, hit⟩

/-- No hidden tapes, oracle memory or future responses are exposed by selection. -/
@[expose] def observe (selected : Selected n k Private Control input) : Observation n :=
  ⟨selected.before.records, sourceSignal limits selected.checkpoint⟩

/-- Actual conditional next trace; null observations use harmless posterior completion. -/
@[expose] def conditional (prior : PMF (State n k Private Control input)) (o : Observation n) :
    PMF (State n k Private Control input) :=
  (PMF.posterior (select limits sample machine prior) (observe limits) o).bind fun selected =>
    respond limits sample machine selected.before selected.checkpoint

/-- The same fixed oracle is dispatched after selection for every native policy.
This is a derived whole-law identity, not an admission or abstraction hypothesis. -/
theorem selection_factor (prior : PMF (State n k Private Control input)) :
    ((select limits sample machine prior).map (observe limits)).bind
      (conditional limits sample machine prior) = prior.bind (step limits sample machine) := by
  unfold conditional
  rw [PMF.posterior_bind]
  simp only [select, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  rfl

/-- Nonnegative extended expectation of a retained trace score. -/
@[expose] def mean (prior : PMF (State n k Private Control input))
    (score : State n k Private Control input → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' state, prior state * score state

/-- Score of the actual newest receipt; a zero-call decision has record `none`. -/
@[expose] def newest (score : Record n → ℝ≥0∞) (state : State n k Private Control input) :
    ℝ≥0∞ := score (state.records.headD none)

/-- One source-selected conditional resource/count mean, derived from native law. -/
@[expose] def conditionalMean (prior : PMF (State n k Private Control input))
    (o : Observation n) (score : Record n → ℝ≥0∞) : ℝ≥0∞ :=
  mean (conditional limits sample machine prior o) (newest score)

/-- Whether the observed selected source signal is an actual batch. -/
@[expose] def Observation.issued (o : Observation n) : Bool :=
  o.signal.any fun (_, batch) => batch.isSome

/-- Every actually selected nondivergent checkpoint is a source boundary, before response. -/
theorem selected_boundary (prior : PMF (State n k Private Control input))
    (picked : Selected n k Private Control input)
    (hp : picked ∈ (select limits sample machine prior).support)
    (phase : Phase k Control Unit (ServerState n Private) input)
    (he : picked.checkpoint = some phase) : sourceBoundary limits phase := by
  simp only [select, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hp
  obtain ⟨state, _, hit, hh, rfl⟩ := hp
  simp only at he
  subst hit
  cases hs : state.hidden with
  | none => simp [hs, seekSourceFrom] at hh
  | some start =>
    simp only [hs, seekSourceFrom] at hh
    exact ((StoppedProcess.terminal_support _ _ _ _ _).mp hh).1

/-- The actual new receipt exists exactly for an observed issued source batch.
This support theorem retains all response/private-state correlations. -/
theorem conditional_record_isSome (prior : PMF (State n k Private Control input))
    (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (observe limits)).support)
    (next : State n k Private Control input)
    (hn : next ∈ (conditional limits sample machine prior o).support) :
    (next.records.headD none).isSome = o.issued := by
  simp only [conditional, PMF.mem_support_bind_iff] at hn
  obtain ⟨picked, hp, hn⟩ := hn
  obtain ⟨hp, he⟩ := PMF.mem_support_of_posterior _ _ _ ho _ hp
  simp only [respond, PMF.mem_support_map_iff] at hn
  obtain ⟨nextPhase, hr, rfl⟩ := hn
  have hb := response_issued limits sample machine picked.checkpoint nextPhase
    (selected_boundary limits sample machine prior picked hp) hr
  have he' := congrArg Observation.issued he
  change batchIssued limits picked.checkpoint = o.issued at he'
  simpa only [List.headD_cons] using hb.trans he'

/-- Every supported response at a positive-mass selection is an actual next
whole-policy trace. Null-history completion cannot create a reached branch. -/
theorem conditional_support (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (observe limits)).support)
    (next : State n k Private Control input)
    (hn : next ∈ (conditional limits sample machine prior o).support) :
    next ∈ (prior.bind (step limits sample machine)).support := by
  rw [← selection_factor limits sample machine prior]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨o, ho, hn⟩

/-- On a positive-probability selected batch the actual conditional issued count
is one; on a halt/divergence signal it is zero. This follows from the actual epoch
and concrete guarded dispatch, not an assumed source-validity contract. -/
theorem conditional_issued (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (observe limits)).support) :
    conditionalMean limits sample machine prior o issued = if o.issued then 1 else 0 := by
  have hs : ∀ next ∈ (conditional limits sample machine prior o).support,
      newest issued next = if o.issued then 1 else 0 := by
    intro next hn
    simp only [newest, issued,
      conditional_record_isSome limits sample machine prior o ho next hn]
  unfold conditionalMean mean
  calc
    _ = ∑' next, conditional limits sample machine prior o next *
        (if o.issued then 1 else 0) := by
      apply tsum_congr
      intro next
      by_cases hn : next ∈ (conditional limits sample machine prior o).support
      · rw [hs next hn]
      · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Halt/divergence decisions have no new resource charge, while their earlier
accrued receipts remain in the whole trace. -/
theorem conditional_zero (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (observe limits)).support)
    (hz : o.issued = false) (score : Record n → ℝ≥0∞) (hscore : score none = 0) :
    conditionalMean limits sample machine prior o score = 0 := by
  unfold conditionalMean mean
  apply tsum_eq_zero_iff.mpr
  intro next
  by_cases hn : next ∈ (conditional limits sample machine prior o).support
  · have he := conditional_record_isSome limits sample machine prior o ho next hn
    rw [hz] at he
    cases hx : next.records.headD none with
    | none =>
      change _ * score (next.records.headD none) = 0
      rw [hx, hscore, mul_zero]
    | some record =>
      rw [hx] at he
      cases he
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]

/-- Supported response-wise resource bounds imply the derived conditional
bounds. This is a sufficient discharge rule for concrete oracles; the source
transfer theorems themselves require only conditional means, not these stronger
pointwise bounds on hidden states. -/
theorem conditional_of_response_bound
    (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (observe limits)).support)
    (left right : Record n → ℝ≥0∞) (c d : ℝ≥0∞)
    (H : ∀ picked ∈ (select limits sample machine prior).support,
      ∀ next ∈ (respond limits sample machine picked.before picked.checkpoint).support,
      c * newest left next ≤ d * newest right next) :
    c * conditionalMean limits sample machine prior o left ≤
      d * conditionalMean limits sample machine prior o right := by
  have hs (next : State n k Private Control input)
      (hn : next ∈ (conditional limits sample machine prior o).support) :
      c * newest left next ≤ d * newest right next := by
    simp only [conditional, PMF.mem_support_bind_iff] at hn
    obtain ⟨picked, hp, hn⟩ := hn
    exact H picked (PMF.mem_support_of_posterior _ _ _ ho _ hp).1 next hn
  unfold conditionalMean mean
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply tsum_le_tsum
  intro next
  by_cases hn : next ∈ (conditional limits sample machine prior o).support
  · simpa only [mul_left_comm c, mul_left_comm d] using
      mul_le_mul_right (hs next hn) (conditional limits sample machine prior o next)
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]

/-- Actual selected-batch tower, with arbitrary discrete history/metadata and no
integrability premise. Null observations contribute zero mass. -/
theorem selected_mean (prior : PMF (State n k Private Control input))
    (score : Record n → ℝ≥0∞) :
    mean (prior.bind (step limits sample machine)) (newest score) =
      ∑' o, (select limits sample machine prior).map (observe limits) o *
        conditionalMean limits sample machine prior o score := by
  rw [← selection_factor limits sample machine prior]
  exact PMF.tsum_bind_mul _ _ _

private theorem respond_accrued (state : State n k Private Control input)
    (hit : Option (Phase k Control Unit (ServerState n Private) input))
    (score : Record n → ℝ≥0∞) :
    mean (respond limits sample machine state hit) (accrued score) =
      accrued score state + mean (respond limits sample machine state hit) (newest score) := by
  simp only [mean, respond, PMF.tsum_map_mul, accrued, List.map_cons, List.sum_cons,
    newest, List.headD_cons, mul_add, tsum_add, ENNReal.tsum_mul_right,
    (respondSource limits sample machine hit).tsum_coe, one_mul, add_comm]

/-- Actual accrued invoices persist across epochs, including later divergence. -/
theorem step_accrued (prior : PMF (State n k Private Control input))
    (score : Record n → ℝ≥0∞) :
    mean (prior.bind (step limits sample machine)) (accrued score) =
      mean prior (accrued score) +
        mean (prior.bind (step limits sample machine)) (newest score) := by
  simp only [mean, Trace.step, PMF.tsum_bind_mul]
  change (∑' state, prior state * ∑' hit,
      seekSourceFrom limits sample machine state.hidden hit *
        mean (respond limits sample machine state hit) (accrued score)) =
    (∑' state, prior state * accrued score state) +
      (∑' state, prior state * ∑' hit,
        seekSourceFrom limits sample machine state.hidden hit *
          mean (respond limits sample machine state hit) (newest score))
  simp only [respond_accrued, mul_add, tsum_add, ENNReal.tsum_mul_right,
    PMF.tsum_coe, one_mul]

/-- Complete actual trace expectation of a resource/count after the given epochs. -/
@[expose] def expected (score : Record n → ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) : ℝ≥0∞ :=
  mean (law limits sample machine turns world) (accrued score)

/-- Expected actual resource at one selected source epoch. -/
@[expose] def marginal (score : Record n → ℝ≥0∞) (turn : ℕ)
    (world : World k Control Unit (ServerState n Private) input) : ℝ≥0∞ :=
  ∑' o, (select limits sample machine (law limits sample machine turn world)).map
    (observe limits) o *
      conditionalMean limits sample machine (law limits sample machine turn world) o score

/-- Whole-policy quantitative accounting from actual native laws and derived
selected-before-response kernels; no finite response/history abstraction is needed. -/
theorem expected_accrued (score : Record n → ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) :
    expected limits sample machine score turns world =
      ∑ turn ∈ Finset.range turns, marginal limits sample machine score turn world := by
  induction turns with
  | zero =>
    simp [expected, mean, law, ObservedProcess.stateLaw, Trace.initial, accrued, PMF.pure_apply]
  | succ turns ih =>
    change mean ((law limits sample machine turns world).bind (step limits sample machine))
      (accrued score) = _
    rw [step_accrued, selected_mean, Finset.sum_range_succ]
    exact congrArg (· + marginal limits sample machine score turns world) ih

/-- A finite epoch horizon bounds the actual expected issued-batch count,
including halt/divergence decisions and arbitrary hidden metadata. -/
theorem expected_issued_le (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) :
    expected limits sample machine issued turns world ≤ turns := by
  unfold expected mean
  calc
    _ ≤ ∑' state, law limits sample machine turns world state * (turns : ℝ≥0∞) := by
      apply tsum_le_tsum
      intro state
      by_cases hs : state ∈ (law limits sample machine turns world).support
      · exact mul_le_mul_right ((accrued_issued_le state).trans_eq
          (congrArg Nat.cast (law_length limits sample machine turns world state hs))) _
      · simp [(PMF.apply_eq_zero_iff _ _).mpr hs]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Actual source feasibility bounds the expected issued count even on traces
which later diverge silently. Zero-call padding does not consume the turn budget. -/
theorem expected_issued_budget (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) :
    expected limits sample machine issued turns world ≤ limits.turns := by
  unfold expected mean
  calc
    _ ≤ ∑' state, law limits sample machine turns world state * (limits.turns : ℝ≥0∞) := by
      apply tsum_le_tsum
      intro state
      by_cases hs : state ∈ (law limits sample machine turns world).support
      · have hb := (law_ledger_bound limits sample machine turns world hi state hs).1
        have hl : (state.records.filterMap id).length ≤ limits.turns := by
          rw [List.length_append] at hb
          omega
        apply mul_le_mul_right _ _
        rw [accrued_issued]
        exact_mod_cast hl
      · simp [(PMF.apply_eq_zero_iff _ _).mpr hs]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Adding another decision after the whole policy has halted/diverged does not
change any accumulated resource with zero charge for a no-call decision. -/
theorem complete_expected_step (score : Record n → ℝ≥0∞) (hscore : score none = 0)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) :
    expected limits sample machine score (limits.turns + 2) world =
      expected limits sample machine score (limits.turns + 1) world := by
  change mean ((law limits sample machine (limits.turns + 1) world).bind
    (step limits sample machine)) (accrued score) = _
  unfold mean
  rw [PMF.tsum_bind_mul]
  apply tsum_congr
  intro state
  by_cases hs : state ∈ (law limits sample machine (limits.turns + 1) world).support
  · rw [step_done limits sample machine state (law_done limits sample machine world hi state hs)]
    simp [accrued, hscore, PMF.pure_apply]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hs]

/-- A supported selected-before-response resource comparison transfers to the
whole actual native policy. Infinite expectations are allowed; no bounded total
bill, integrability, lower cost or representation conclusion is assumed. -/
theorem conditional_comparison (left right : Record n → ℝ≥0∞) (c d : ℝ≥0∞)
    (turns : ℕ) (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ turn < turns, ∀ o ∈
      ((select limits sample machine (law limits sample machine turn world)).map
        (observe limits)).support,
      c * conditionalMean limits sample machine (law limits sample machine turn world) o left ≤
        d * conditionalMean limits sample machine (law limits sample machine turn world) o right) :
    c * expected limits sample machine left turns world ≤
      d * expected limits sample machine right turns world := by
  rw [expected_accrued, expected_accrued, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro turn ht
  rw [Finset.mem_range] at ht
  unfold marginal
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply tsum_le_tsum
  intro o
  by_cases ho : o ∈ ((select limits sample machine
      (law limits sample machine turn world)).map (observe limits)).support
  · simpa only [mul_left_comm c, mul_left_comm d] using
      mul_le_mul_right (H turn ht o ho)
        (((select limits sample machine (law limits sample machine turn world)).map
          (observe limits)) o)
  · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]

/-- The source's reached-history, selected-batch cost lower envelope transfers
to the entire actual native policy, with one fixed oracle sampler. No finite
alphabet, expected-total-cost or integrability premise is imposed. -/
theorem cost_lower (c : ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ turn < turns, ∀ o ∈
      ((select limits sample machine (law limits sample machine turn world)).map
        (observe limits)).support, o.issued = true →
      c ≤ conditionalMean limits sample machine (law limits sample machine turn world) o charge) :
    c * expected limits sample machine issued turns world ≤
      expected limits sample machine charge turns world := by
  apply (conditional_comparison limits sample machine issued charge c 1 turns world ?_).trans_eq
    (one_mul _)
  intro turn ht o ho
  rw [conditional_issued limits sample machine _ o ho]
  by_cases hi : o.issued = true
  · simpa only [hi, ite_true, mul_one, one_mul] using H turn ht o ho hi
  · simp [hi]

/-- The corresponding source conditional upper envelope also transfers to the
whole actual native policy, including earlier charges on divergent outcomes. -/
theorem cost_upper (c : ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ turn < turns, ∀ o ∈
      ((select limits sample machine (law limits sample machine turn world)).map
        (observe limits)).support, o.issued = true →
      conditionalMean limits sample machine (law limits sample machine turn world) o charge ≤ c) :
    expected limits sample machine charge turns world ≤
      c * expected limits sample machine issued turns world := by
  have he := conditional_comparison limits sample machine charge issued 1 c turns world
  rw [one_mul] at he
  apply he
  intro turn ht o ho
  rw [conditional_issued limits sample machine _ o ho, one_mul]
  by_cases hi : o.issued = true
  · simpa only [hi, ite_true, mul_one, one_mul] using H turn ht o ho hi
  · have hz : o.issued = false := Bool.eq_false_iff.mpr hi
    rw [conditional_zero limits sample machine _ o ho hz charge rfl]
    simp [hi]

/-- Finite local upper envelopes imply a finite whole-policy nonnegative
expectation; integrability or bounded total invoices are not premises. -/
theorem cost_upper_finite (c : ℝ≥0) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ turn < turns, ∀ o ∈
      ((select limits sample machine (law limits sample machine turn world)).map
        (observe limits)).support, o.issued = true →
      conditionalMean limits sample machine (law limits sample machine turn world) o charge ≤ c) :
    expected limits sample machine charge turns world ≤ (c : ℝ≥0∞) * turns ∧
      expected limits sample machine charge turns world ≠ ⊤ := by
  have hb := (cost_upper limits sample machine c turns world H).trans
    (mul_le_mul_right (expected_issued_le limits sample machine turns world) (c : ℝ≥0∞))
  exact ⟨hb, ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hb⟩

/-- The source turn budget, rather than the extra zero-call halting decision,
bounds the actual whole-policy expected bill under a finite conditional upper envelope. -/
theorem cost_upper_budget (c : ℝ≥0) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory)
    (H : ∀ turn < turns, ∀ o ∈
      ((select limits sample machine (law limits sample machine turn world)).map
        (observe limits)).support, o.issued = true →
      conditionalMean limits sample machine (law limits sample machine turn world) o charge ≤ c) :
    expected limits sample machine charge turns world ≤ (c : ℝ≥0∞) * limits.turns ∧
      expected limits sample machine charge turns world ≠ ⊤ := by
  have hb := (cost_upper limits sample machine c turns world H).trans
    (mul_le_mul_right (expected_issued_budget limits sample machine turns world hi) (c : ℝ≥0∞))
  exact ⟨hb, ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hb⟩

/-- Universal source token accounting over all source-admitted actual native
machines using this very same oracle, including every finite-control competitor.
Selection-only admission is the original
successful-output condition. Each competitor needs only its own reached
selected-before-response cost envelope, not bounds on other competitors, a
representation assumption or an optimality claim. -/
theorem universal_cost_lower (m : ℕ) (accept : Finset (Fin m) → Bool) (c : ℝ≥0∞)
    (seed : Private) :
    ∀ (tapes : ℕ) (Controls : Type) (x : List Bool)
      (competitor : MultiTapePTM tapes Bool Controls Unit),
      NativeUnboundedExecution.SelectionOnly competitor (environment limits sample)
        (candidateParser (n := n) m) (decodeFamily m) accept
          (startWorld (n := n) (input := x) competitor seed) →
      (∀ turn < limits.turns + 1, ∀ o ∈
        ((select limits sample competitor
          (law limits sample competitor turn
            (startWorld (n := n) (input := x) competitor seed))).map (observe limits)).support,
        o.issued = true → c ≤ conditionalMean limits sample competitor
          (law limits sample competitor turn
            (startWorld (n := n) (input := x) competitor seed)) o charge) →
      c * expected limits sample competitor issued (limits.turns + 1)
          (startWorld (n := n) (input := x) competitor seed) ≤
        expected limits sample competitor charge (limits.turns + 1)
          (startWorld (n := n) (input := x) competitor seed) := by
  intro tapes Controls x competitor _ H
  exact cost_lower limits sample competitor c (limits.turns + 1)
    (startWorld (n := n) (input := x) competitor seed) H

end Cslib.Probability.NativeBatch.Quantitative
