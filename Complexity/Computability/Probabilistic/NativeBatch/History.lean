/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeBatch.Quantitative
public import Complexity.Probability.StochasticOracle.AdaptiveSelection
import Complexity.Probability.PMF.Disintegration.Support
import Mathlib.Tactic

/-!
# History-dependent rewards on actual native batch traces

[Wang2027], Theorem 5 and Appendix A.5, PDF pp. 12,16. Revealed progress and
retained productivity depend on all preceding receipts. These rewards use actual
native source epochs and their selected-before-response posteriors, without
restricting the response alphabet or private metadata.

## Main results

* `conditional_records`: actual conditional receipts extend the observed full history.
* `selected_history`: pre-response histories have the actual prior history law.
* `expected_sum`: the actual history-dependent reward tower.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.History
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing Trace Quantitative
open scoped ENNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)
variable (machine : MultiTapePTM k Bool Control Unit)

/-- Every actual source epoch appends its one real receipt or no-call record. -/
theorem step_records (state next : State n k Private Control input)
    (hn : next ∈ (Trace.step limits sample machine state).support) :
    ∃ record, next.records = record :: state.records := by
  simp only [Trace.step, PMF.mem_support_bind_iff] at hn
  obtain ⟨hit, _, hn⟩ := hn
  simp only [respond, PMF.mem_support_map_iff] at hn
  obtain ⟨phase, _, rfl⟩ := hn
  exact ⟨_, rfl⟩

/-- Conditional responses at positive-mass observations retain the entire true
previous receipt history. No finite history abstraction is assumed. -/
theorem conditional_records (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support)
    (next : State n k Private Control input)
    (hn : next ∈ (conditional limits sample machine prior o).support) :
    ∃ record, next.records = record :: o.history := by
  simp only [conditional, PMF.mem_support_bind_iff] at hn
  obtain ⟨picked, hp, hn⟩ := hn
  have he := (PMF.mem_support_of_posterior _ _ _ ho _ hp).2
  have hh := congrArg Observation.history he
  simp only [Quantitative.observe] at hh
  simp only [respond, PMF.mem_support_map_iff] at hn
  obtain ⟨phase, _, rfl⟩ := hn
  exact ⟨_, congrArg (_ :: ·) hh⟩

/-- The source selection stage changes no earlier receipt history, even when
silent native computation is unbounded or divergent. -/
theorem selected_history (prior : PMF (State n k Private Control input))
    (f : List (Record n) → ℝ≥0∞) :
    (∑' o, (select limits sample machine prior).map (Quantitative.observe limits) o * f o.history) =
      mean prior (fun state => f state.records) := by
  simp only [PMF.tsum_map_mul, select, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.tsum_bind_mul, PMF.tsum_map_mul, Quantitative.observe, mean]
  simp [PMF.pure_apply, ENNReal.tsum_mul_right]

/-- Read an actual history-dependent reward from the newest native receipt. -/
@[expose] def newest (reward : List (Record n) → Record n → ℝ≥0∞)
    (state : State n k Private Control input) : ℝ≥0∞ :=
  reward state.records.tail (state.records.headD none)

/-- Actual accumulated rewards along a newest-first receipt history. -/
@[expose] def accumulated (reward : List (Record n) → Record n → ℝ≥0∞) :
    List (Record n) → ℝ≥0∞
  | [] => 0
  | record :: history => accumulated reward history + reward history record

/-- Actual expected accumulated history-dependent reward. -/
@[expose] def expected (reward : List (Record n) → Record n → ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) : ℝ≥0∞ :=
  mean (law limits sample machine turns world) (fun state => accumulated reward state.records)

/-- Actual selected conditional mean of a history-dependent reward. -/
@[expose] def conditionalMean (prior : PMF (State n k Private Control input))
    (o : Observation n) (reward : List (Record n) → Record n → ℝ≥0∞) : ℝ≥0∞ :=
  mean (conditional limits sample machine prior o) (newest reward)

/-- Exact conditional tower for every nonnegative trace score. -/
theorem selected_mean (prior : PMF (State n k Private Control input))
    (f : State n k Private Control input → ℝ≥0∞) :
    mean (prior.bind (Trace.step limits sample machine)) f =
      ∑' o, (select limits sample machine prior).map (Quantitative.observe limits) o *
        mean (conditional limits sample machine prior o) f := by
  rw [← selection_factor limits sample machine prior]
  exact PMF.tsum_bind_mul _ _ _

private theorem respond_accumulated (state : State n k Private Control input)
    (hit : Option (Phase k Control Unit (ServerState n Private) input))
    (reward : List (Record n) → Record n → ℝ≥0∞) :
    mean (respond limits sample machine state hit) (fun next => accumulated reward next.records) =
      accumulated reward state.records + mean (respond limits sample machine state hit)
        (newest reward) := by
  simp only [mean, respond, PMF.tsum_map_mul, accumulated, newest, List.tail_cons,
    List.headD_cons, mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Accumulated rewards satisfy the actual one-epoch tower, without integrability. -/
theorem step_accumulated (prior : PMF (State n k Private Control input))
    (reward : List (Record n) → Record n → ℝ≥0∞) :
    mean (prior.bind (Trace.step limits sample machine))
        (fun state => accumulated reward state.records) =
      mean prior (fun state => accumulated reward state.records) +
        mean (prior.bind (Trace.step limits sample machine)) (newest reward) := by
  simp only [mean, Trace.step, PMF.tsum_bind_mul]
  change (∑' state, prior state * ∑' hit, seekSourceFrom limits sample machine state.hidden hit *
      mean (respond limits sample machine state hit)
        (fun next => accumulated reward next.records)) =
    (∑' state, prior state * accumulated reward state.records) +
      (∑' state, prior state * ∑' hit, seekSourceFrom limits sample machine state.hidden hit *
        mean (respond limits sample machine state hit) (newest reward))
  simp only [respond_accumulated, mul_add, tsum_add, ENNReal.tsum_mul_right,
    PMF.tsum_coe, one_mul]

/-- Full history-dependent accounting on the actual native process. -/
theorem expected_sum (reward : List (Record n) → Record n → ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) :
    expected limits sample machine reward turns world = ∑ turn ∈ Finset.range turns,
      ∑' o, (select limits sample machine (law limits sample machine turn world)).map
        (Quantitative.observe limits) o *
          conditionalMean limits sample machine
            (law limits sample machine turn world) o reward := by
  induction turns with
  | zero =>
    simp [expected, mean, law, ObservedProcess.stateLaw, Trace.initial, accumulated,
      PMF.pure_apply]
  | succ turns ih =>
    change mean ((law limits sample machine turns world).bind
      (Trace.step limits sample machine)) _ = _
    rw [step_accumulated, selected_mean, Finset.sum_range_succ]
    exact congrArg (· + _) ih

/-- Static invoice/count rewards agree with the existing resource accounting. -/
theorem expected_static (score : Record n → ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) :
    expected limits sample machine (fun _ => score) turns world =
      Quantitative.expected limits sample machine score turns world := by
  have he (history : List (Record n)) : accumulated (fun _ => score) history =
      (history.map score).sum := by
    induction history with
    | nil => rfl
    | cons record history ih => simp [accumulated, ih, add_comm]
  simp only [expected, Quantitative.expected, he]
  rfl

/-- History-dependent indicator accumulation is the exact actual progress count. -/
theorem accumulated_count (event : List (Record n) → Record n → Bool) (history : List (Record n)) :
    accumulated (fun h x => if event h x then 1 else 0) history =
      (StochasticOracle.AdaptiveSelection.count event history : ℝ≥0∞) := by
  induction history with
  | nil => simp [accumulated, StochasticOracle.AdaptiveSelection.count]
  | cons record history ih =>
    simp only [accumulated, StochasticOracle.AdaptiveSelection.count, Nat.cast_add, ih]
    cases event history record <;> simp

/-- The extra silent completion epoch cannot issue a batch beyond the source
turn budget. This uses actual guarded requests and native live-epoch accounting. -/
theorem final_not_issued (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (o : Observation n)
    (ho : o ∈ ((select limits sample machine
      (law limits sample machine limits.turns world)).map (Quantitative.observe limits)).support) :
    o.issued = false := by
  obtain ⟨picked, hp, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  have hb := selected_boundary limits sample machine _ picked hp
  simp only [select, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hp
  obtain ⟨state, hs, hit, hh, rfl⟩ := hp
  cases hit with
  | none => rfl
  | some phase =>
    have hb := hb phase rfl
    cases phase with
    | ready next => rfl
    | pending chosen =>
      cases chosen with
      | halted next => exact hb.elim
      | «local» next => exact hb.elim
      | query next op control =>
        cases op
        change (admit limits next.memory.privateState
          (next.config.channels ()).queryBuffer).isSome = true at hb
        have hv := law_valid limits sample machine limits.turns world hi state hs
        cases hz : state.hidden with
        | none => simp [hz, seekSourceFrom] at hh
        | some previous =>
          cases previous with
          | pending tx => simp [Trace.Valid, hz] at hv
          | ready previous =>
            have hl : ¬NativeUnboundedExecution.halted previous := by
              intro hl
              have he : seekSourceFrom limits sample machine (some (.ready previous)) =
                  PMF.pure (some (.ready previous)) :=
                StoppedProcess.terminal_halted (sourceSilent limits sample machine)
                  (sourceBoundary limits) (StoppedProcess.beforeBoundary_absorbs _ _) _ hl
              simp [hz, he] at hh
            have hc := law_live_count limits sample machine _ world previous hi state hs hz hl
            rw [hz] at hh
            have he := seek_state limits sample machine (.ready previous)
              (.pending (.query next () control)) hh
            change next.memory.privateState = previous.memory.privateState at he
            cases ha : admit limits next.memory.privateState
                (next.config.channels ()).queryBuffer with
            | none => simp [ha] at hb
            | some batch =>
              have hb := (admit_sound limits _ _ batch ha).2.2.2.1
              rw [he] at hb
              omega

/-- At any actual prior whose reached selected signals issue no batch, the next
receipt is exactly no-call padding. Silent code may still halt or diverge. -/
theorem no_call_records_mean (prior : PMF (State n k Private Control input))
    (H : ∀ o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support,
      o.issued = false) (f : List (Record n) → ℝ≥0∞) :
    mean (prior.bind (Trace.step limits sample machine)) (fun state => f state.records) =
      mean prior (fun state => f (none :: state.records)) := by
  rw [selected_mean, ← selected_history limits sample machine _ (fun h => f (none :: h))]
  apply tsum_congr
  intro o
  by_cases ho : o ∈ ((select limits sample machine
      prior).map (Quantitative.observe limits)).support
  · congr 1
    have he : ∀ next ∈ (conditional limits sample machine
        prior o).support,
        next.records = none :: o.history := by
      intro next hn
      obtain ⟨record, hr⟩ := conditional_records limits sample machine _ o ho next hn
      have hissued := conditional_record_isSome limits sample machine _ o ho next hn
      rw [H o ho, hr, List.headD_cons] at hissued
      cases record with
      | none => exact hr
      | some receipt => cases hissued
    calc
      _ = ∑' next, conditional limits sample machine
          prior o next * f (none :: o.history) := by
        apply tsum_congr
        intro next
        by_cases hn : next ∈ (conditional limits sample machine
            prior o).support
        · simp only [he next hn]
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]

/-- Completion changes no receipt resource/progress after the issued-turn budget:
the final epoch appends exactly a no-call record, while its hidden code may halt
or diverge. The earlier whole receipt history retains its exact law. -/
theorem final_records_mean (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (f : List (Record n) → ℝ≥0∞) :
    mean (law limits sample machine (limits.turns + 1) world) (fun state => f state.records) =
      mean (law limits sample machine limits.turns world)
        (fun state => f (none :: state.records)) :=
  no_call_records_mean limits sample machine _ (final_not_issued limits sample machine world hi) f

/-- The final silent completion epoch adds no source resource. In particular,
upper source envelopes are needed for only `limits.turns` genuine trial positions. -/
theorem final_expected_static (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (score : Record n → ℝ≥0∞) (hscore : score none = 0) :
    Quantitative.expected limits sample machine score (limits.turns + 1) world =
      Quantitative.expected limits sample machine score limits.turns world := by
  unfold Quantitative.expected
  change mean (law limits sample machine (limits.turns + 1) world)
    (fun state => (state.records.map score).sum) = _
  rw [final_records_mean limits sample machine world hi (fun h => (h.map score).sum)]
  simp only [List.map_cons, List.sum_cons, hscore, zero_add]
  rfl

end Cslib.Probability.NativeBatch.History
