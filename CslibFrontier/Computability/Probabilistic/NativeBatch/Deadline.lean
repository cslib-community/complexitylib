/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Coverage
import CslibFrontier.Probability.PMF.Disintegration.Support
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Actual native physical deadline transfer

[Wang2027], Theorem 5(2), PDF p. 12, Appendix A.5 p. 16. The lower latency
envelope concerns the maximum concurrent batch latency, including cutoffs and
cancellation, on reached selected-response supports. Local computation is excluded
from the external duration, as in the source model. All receipt and hidden-state
laws are the actual native ones; silent divergence retains earlier receipts.

## Main results

* `latency_sum_lower`: selected-response lower latency envelopes add on actual paths.
* `issued_bound`, `no_call_after`: derive the source physical/turn allowance.
* `records_mean_stable`: exact retained-receipt accounting beyond that allowance.
* `lower_guarantees`: assembled native success-level bill and deadline bounds.
* `zero_deadline_failure`: universal nonempty-cover failure with no envelopes.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Deadline
open NativeOpenExecution NativeInterface StochasticOracle ConcurrentBatch Turing Trace Quantitative
open AdaptiveSelection PartialCover Coverage
open scoped ENNReal NNReal
variable {n k m : ℕ} {Private Control E : Type} [DecidableEq E] {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)
variable (machine : MultiTapePTM k Bool Control Unit)

/-- A real issued source response resumes the native machine at its query's
continuation state. It cannot be mistaken for a halted or divergent decision. -/
theorem issued_live
    (hit next : Option (Phase k Control Unit (ServerState n Private) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase)
    (hn : next ∈ (respondSource limits sample machine hit).support)
    (hi : (receipt hit next).isSome = true) :
    ∃ world, next = some (.ready world) ∧ ¬NativeUnboundedExecution.halted world := by
  cases hit with
  | none => simp [receipt] at hi
  | some phase =>
    have hb := hb phase rfl
    cases phase with
    | ready world => simp [receipt] at hi
    | pending chosen =>
      cases chosen with
      | halted world => exact hb.elim
      | «local» world => exact hb.elim
      | query world op control =>
        cases op
        change (admit limits world.memory.privateState
          (world.config.channels ()).queryBuffer).isSome = true at hb
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer with
        | none => simp [ha] at hb
        | some batch =>
          simp only [respondSource, phaseStep, dispatch, environment, serve, ha,
            PMF.map_comp, PMF.mem_support_map_iff] at hn
          obtain ⟨out, _, rfl⟩ := hn
          exact ⟨_, rfl, by simp [NativeUnboundedExecution.halted,
            MultiTapeMachine.Config.receive]⟩

/-- A pointwise lower bound on issued selected batch durations adds along every
actual native path. No envelope on null histories or independent responses is needed. -/
theorem latency_sum_lower (ℓ : ℝ≥0) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → ∀ next ∈ (conditional limits sample machine
        (law limits sample machine t world) o).support,
        ℓ ≤ (next.records.headD none).elim 0 Exchange.duration)
    (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine turns world).support) :
    ℓ * (state.records.filterMap id).length ≤
      ((state.records.filterMap id).map Exchange.duration).sum := by
  induction turns generalizing state with
  | zero =>
    simp only [law, ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at hs
    subst state
    simp [Trace.initial]
  | succ turns ih =>
    have hs' : state ∈ ((law limits sample machine turns world).bind
        (Trace.step limits sample machine)).support := hs
    obtain ⟨before, hb, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs'
    obtain ⟨record, he⟩ := History.step_records limits sample machine before state hn
    have hp := ih (fun t ht => H t (by omega)) before hb
    rw [← selection_factor limits sample machine] at hs'
    obtain ⟨o, ho, hc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs'
    have hi := conditional_record_isSome limits sample machine _ o ho state hc
    rw [he, List.headD_cons] at hi
    rw [he]
    cases record with
    | none => simpa using hp
    | some receipt =>
      have hl := H turns (by omega) o ho hi.symm state hc
      rw [he, List.headD_cons] at hl
      simp only [List.filterMap_cons, id_eq, List.length_cons, Nat.cast_add, Nat.cast_one,
        List.map_cons, List.sum_cons, mul_add, mul_one]
      exact (add_le_add hp hl).trans_eq (add_comm _ _)

/-- Source physical duration limits the number of completed issued batches. -/
@[expose] def effectiveTurns (ℓ : ℝ≥0) : ℕ :=
  min limits.turns ⌊limits.deadline / ℓ⌋₊

/-- The source lower-latency contract on actual selected-response supports.
Zero-call decisions impose no latency requirement. -/
@[expose] def LowerLatency (world : World k Control Unit (ServerState n Private) input)
    (ℓ : ℝ≥0) : Prop :=
  ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
      (law limits sample machine t world)).map (Quantitative.observe limits)).support,
    o.issued = true → ∀ next ∈ (conditional limits sample machine
      (law limits sample machine t world) o).support,
      ℓ ≤ (next.records.headD none).elim 0 Exchange.duration

/-- The deadline bound concerns actual accrued receipt duration, including all
canceled calls' batch maxima. It is derived pathwise, not assumed as a turn cap. -/
theorem issued_bound (ℓ : ℝ≥0) (hℓ : 0 < ℓ) (turns : ℕ) (ht : turns ≤ limits.turns + 1)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hz : world.memory.privateState.history = [])
    (H : LowerLatency limits sample machine world ℓ)
    (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine turns world).support) :
    (state.records.filterMap id).length ≤ effectiveTurns limits ℓ := by
  have hl := latency_sum_lower limits sample machine ℓ turns world
    (fun t htt => H t (by omega)) state hs
  have hb := law_ledger_bound limits sample machine turns world hi state hs
  simp only [hz, List.append_nil] at hb
  apply le_min hb.1
  apply Nat.le_floor
  apply (le_div_iff₀ hℓ).mpr
  simpa only [mul_comm] using hl.trans hb.2.1

/-- A still-live source epoch has issued at least its index's number of batches;
the lower latency envelope therefore bounds that actual index by the deadline. -/
theorem live_epoch_le (ℓ : ℝ≥0) (hℓ : 0 < ℓ) (turns : ℕ) (ht : turns ≤ limits.turns + 1)
    (world next : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hz : world.memory.privateState.history = [])
    (H : LowerLatency limits sample machine world ℓ)
    (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine turns world).support)
    (he : state.hidden = some (.ready next)) (hl : ¬NativeUnboundedExecution.halted next) :
    turns ≤ effectiveTurns limits ℓ := by
  have hc := law_live_count limits sample machine turns world next hi state hs he hl
  have hv := law_valid limits sample machine turns world hi state hs
  simp only [Trace.Valid, he, hz, List.append_nil] at hv
  rw [hv.2] at hc
  exact hc.trans (issued_bound limits sample machine ℓ hℓ turns ht world hi hz H state hs)

/-- Positive-probability issued selected batches produce actual live native
continuations, retaining hidden state and response correlation. -/
theorem conditional_live (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support)
    (hi : o.issued = true) (next : State n k Private Control input)
    (hn : next ∈ (conditional limits sample machine prior o).support) :
    ∃ world, next.hidden = some (.ready world) ∧ ¬NativeUnboundedExecution.halted world := by
  have hr := conditional_record_isSome limits sample machine prior o ho next hn
  rw [hi] at hr
  simp only [conditional, PMF.mem_support_bind_iff] at hn
  obtain ⟨picked, hp, hn⟩ := hn
  have hp := (PMF.mem_support_of_posterior _ _ _ ho _ hp).1
  simp only [respond, PMF.mem_support_map_iff] at hn
  obtain ⟨out, hn, rfl⟩ := hn
  exact issued_live limits sample machine picked.checkpoint out
    (selected_boundary limits sample machine prior picked hp) hn hr

/-- Once the derived physical/turn allowance is exhausted, every reached selected
signal is a no-call decision. This is a native execution theorem, not a supplied
truncation or representation contract. -/
theorem no_call_after (ℓ : ℝ≥0) (hℓ : 0 < ℓ) (t : ℕ) (ht : t ≤ limits.turns)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hz : world.memory.privateState.history = [])
    (H : LowerLatency limits sample machine world ℓ) (hv : effectiveTurns limits ℓ ≤ t)
    (o : Observation n)
    (ho : o ∈ ((select limits sample machine (law limits sample machine t world)).map
      (Quantitative.observe limits)).support) : o.issued = false := by
  cases he : o.issued with
  | false => rfl
  | true =>
    obtain ⟨next, hn⟩ := (conditional limits sample machine
      (law limits sample machine t world) o).support_nonempty
    obtain ⟨out, hout, hl⟩ := conditional_live limits sample machine _ o ho he next hn
    have hs := conditional_support limits sample machine _ o ho next hn
    have hb := live_epoch_le limits sample machine ℓ hℓ (t + 1) (by omega) world out
      hi hz H next hs hout hl
    omega

/-- All actual receipt observables unchanged by no-call padding have the same
law of expectation after the derived physical deadline allowance. This retains
accrued bills and durations even when later silent code diverges. -/
theorem records_mean_stable (ℓ : ℝ≥0) (hℓ : 0 < ℓ) (later : ℕ)
    (ht : later ≤ limits.turns + 1)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hz : world.memory.privateState.history = [])
    (H : LowerLatency limits sample machine world ℓ) (hv : effectiveTurns limits ℓ ≤ later)
    (f : List (Record n) → ℝ≥0∞) (hf : ∀ h, f (none :: h) = f h) :
    mean (law limits sample machine later world) (fun state => f state.records) =
      mean (law limits sample machine (effectiveTurns limits ℓ) world)
        (fun state => f state.records) := by
  induction later with
  | zero =>
    have he : effectiveTurns limits ℓ = 0 := by omega
    rw [he]
  | succ t ih =>
    by_cases hv' : effectiveTurns limits ℓ ≤ t
    · change mean ((law limits sample machine t world).bind
        (Trace.step limits sample machine)) _ = _
      rw [History.no_call_records_mean limits sample machine _
        (no_call_after limits sample machine ℓ hℓ t (by omega) world hi hz H hv') f]
      simp only [hf]
      exact ih (by omega) hv'
    · have he : effectiveTurns limits ℓ = t + 1 := by omega
      rw [he]

/-- Source Theorem 5(2)'s exact necessary deadline/binomial bound for an actual
admitted native competitor. Neither a physical turn cap nor an output/count
representation is assumed: both follow from actual native source execution. -/
theorem success_binomial (I : Instance E (Fin m)) (b r : ℕ)
    (hr : ∀ q < r, b * q < I.ground.card)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hz : world.memory.privateState.history = [])
    (accept : Finset (Fin m) → Bool)
    (haccept : ∀ C, accept C = true → I.covered C = I.ground)
    (hselect : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world)
    (Hcap : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ∀ next ∈ (conditional limits sample machine (law limits sample machine t world) o).support,
        (revealed I (proposal m) next.records \ revealed I (proposal m) o.history).card ≤ b)
    (p : Set.Icc (0 : ℝ) 1) (ℓ : ℝ≥0) (hℓ : 0 < ℓ)
    (Hprob : ∀ t < effectiveTurns limits ℓ, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if reveals I (proposal m) h x then 1 else 0) ≤ ENNReal.ofReal p)
    (Hlat : LowerLatency limits sample machine world ℓ) :
    (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
        (nativeSuccess accept) true ≤ ENNReal.ofReal
      (∫ j, (if r ≤ j then (1 : ℝ) else 0)
        ∂ProbabilityTheory.binomial (effectiveTurns limits ℓ) p) := by
  classical
  have hm : Monotone (fun j : ℕ => if r ≤ j then (1 : ℝ) else 0) := by
    intro i j hij
    dsimp only
    split_ifs <;> norm_num; omega
  have hc := ProgressComparison.count_upper limits sample machine world
    (reveals I (proposal m)) p (effectiveTurns limits ℓ)
    (by
      intro t ht o ho
      have hp := revealed_envelope limits sample machine I (ENNReal.ofReal p) _ o ho
        (Hprob t ht o ho)
      apply hp.trans
      split_ifs <;> simp)
    _ hm (by intro j; split_ifs <;> norm_num)
  rw [bernoulliExpectation_eq_integral] at hc
  simp only [Nat.zero_add] at hc
  apply le_trans _ hc
  have hb := success_count_tail limits sample machine I b r hr world hi hz
    accept haccept hselect Hcap
  apply hb.trans_eq
  apply records_mean_stable limits sample machine ℓ hℓ _ le_rfl world hi hz Hlat
    ((min_le_left _ _).trans (Nat.le_succ _))
    (fun h => ENNReal.ofReal (if r ≤ count (reveals I (proposal m)) h then 1 else 0))
  intro h
  simp [count, reveals, revealed, proposal, Instance.covered]

/-- Every actual native terminal outcome satisfies the concrete source deadline,
with original native durations and accrued cutoff/cancellation charges. -/
theorem terminal_duration_le
    (world next : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory)
    (hn : some next ∈ (NativeUnboundedExecution.terminal machine
      (environment limits sample) world).support) :
    elapsed next.memory.events ≤ limits.deadline := by
  have hv := NativeBatch.terminal_invariant limits sample machine world next hi hn
  exact hv.2.2.1.trans_le hv.1.2.2.1

/-- Original native accepted output together with its actual external deadline.
Local instruction time is excluded, exactly as in the source convention. -/
@[expose] def nativeByDeadline (accept : Finset (Fin m) → Bool) (D : ℝ≥0)
    (result : Option (World k Control Unit (ServerState n Private) input)) : Bool :=
  result.any fun next => (NativeOpenSelection.result (decodeFamily m) next).any accept &&
    decide (elapsed next.memory.events ≤ D)

/-- The actual native protocol guarantees the external deadline jointly with
output acceptance; adding this deadline test loses no accepted terminal mass. -/
theorem deadline_success_law (accept : Finset (Fin m) → Bool)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) :
    (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
        (nativeByDeadline accept limits.deadline) =
      (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
        (nativeSuccess accept) := by
  apply PMF.bind_congr_on_support
  intro result hr
  cases result with
  | none => rfl
  | some next =>
    have hd := terminal_duration_le limits sample machine world next hi hr
    simp [nativeByDeadline, nativeSuccess, hd]

/-- With zero external deadline no source batch can be selected, for any actual
native policy or hidden history. This follows from concrete request admission. -/
theorem no_call_zero_deadline (hD : limits.deadline = 0)
    (prior : PMF (State n k Private Control input)) (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support) :
    o.issued = false := by
  obtain ⟨picked, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  cases he : picked.checkpoint with
  | none => simp [Quantitative.observe, Observation.issued, he, sourceSignal]
  | some phase =>
    cases phase with
    | ready world => simp [Quantitative.observe, Observation.issued, he, sourceSignal]
    | pending chosen =>
      cases chosen with
      | halted world => simp [Quantitative.observe, Observation.issued, he, sourceSignal]
      | «local» world => simp [Quantitative.observe, Observation.issued, he, sourceSignal]
      | query world op control =>
        cases op
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer with
        | none => simp [Quantitative.observe, Observation.issued, he, sourceSignal, ha]
        | some batch =>
          have hd := (admit_sound limits _ _ batch ha).2.2.1
          rw [hD] at hd
          exact (not_lt_of_ge (show 0 ≤ world.memory.privateState.elapsed from bot_le) hd).elim

/-- Every actual admitted native policy fails to return an accepted nonempty
cover at deadline zero, regardless of local random computation or silent divergence.
No conditional progress, latency or cost envelopes are required for this edge case. -/
theorem zero_deadline_failure (hD : limits.deadline = 0) (I : Instance E (Fin m))
    (hg : I.ground.Nonempty)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hz : world.memory.privateState.history = [])
    (accept : Finset (Fin m) → Bool)
    (haccept : ∀ C, accept C = true → I.covered C = I.ground)
    (hselect : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world) :
    (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
      (nativeByDeadline accept limits.deadline) true = 0 := by
  have hv : effectiveTurns limits 1 = 0 := by simp [effectiveTurns, hD]
  have hb := success_binomial limits sample machine I I.ground.card 1
    (by
      intro q hq
      have hq0 : q = 0 := by omega
      subst q
      simpa using Finset.card_pos.mpr hg)
    world hi hz accept haccept hselect
    (by
      intro t ht o ho next hn
      calc
        _ ≤ (revealed I (proposal m) next.records).card :=
          Finset.card_le_card Finset.sdiff_subset
        _ ≤ I.ground.card := by
          apply Finset.card_le_card
          rw [revealed_source]
          exact I.covered_subset _)
    ⟨1, by norm_num⟩ 1 (by norm_num)
    (by intro t ht; rw [hv] at ht; omega)
    (by
      intro t ht o ho hissued next hn
      rw [no_call_zero_deadline limits sample machine hD _ o ho] at hissued
      cases hissued)
  rw [hv] at hb
  have hz' : (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
      (nativeSuccess accept) true = 0 := by
    apply le_antisymm _ (show (0 : ℝ≥0∞) ≤ _ from zero_le)
    simpa only [ProbabilityTheory.binomial_zero, MeasureTheory.integral_dirac,
      Nat.reduceLeDiff, ite_false, ENNReal.ofReal_zero] using hb
  rw [deadline_success_law limits sample machine accept world hi, hz']

/-- Assembled native Theorem 5(2) transfer: genuine accepted-cover probability
controls both the accrued expected bill and the exact physical deadline tail.
The same fixed sampler is used throughout, and the statement applies to every
native competitor satisfying original SelectionOnly admission and the reached
source envelopes. No desired resource, success or representation conclusion is
among the hypotheses. External instance encodings remain separate. -/
theorem lower_guarantees (I : Instance E (Fin m)) (b r : ℕ)
    (hr : ∀ q < r, b * q < I.ground.card)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hz : world.memory.privateState.history = [])
    (accept : Finset (Fin m) → Bool)
    (haccept : ∀ C, accept C = true → I.covered C = I.ground)
    (hselect : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world)
    (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ)) (c : ℝ≥0∞) (ℓ : ℝ≥0) (hℓ : 0 < ℓ)
    (Hcap : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ∀ next ∈ (conditional limits sample machine (law limits sample machine t world) o).support,
        (revealed I (proposal m) next.records \ revealed I (proposal m) o.history).card ≤ b)
    (Hprob : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if reveals I (proposal m) h x then 1 else 0) ≤ ENNReal.ofReal p)
    (Hcost : ∀ t < limits.turns + 1, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → c ≤ Quantitative.conditionalMean limits sample machine
        (law limits sample machine t world) o charge)
    (Hlat : LowerLatency limits sample machine world ℓ) :
    (((NativeUnboundedExecution.terminal machine (environment limits sample) world).map
        (nativeByDeadline accept limits.deadline) true) * r * c) / ENNReal.ofReal p ≤
      Quantitative.expected limits sample machine charge (limits.turns + 1) world ∧
    (NativeUnboundedExecution.terminal machine (environment limits sample) world).map
        (nativeByDeadline accept limits.deadline) true ≤ ENNReal.ofReal
      (∫ j, (if r ≤ j then (1 : ℝ) else 0)
        ∂ProbabilityTheory.binomial (effectiveTurns limits ℓ) p) := by
  rw [deadline_success_law limits sample machine accept world hi]
  constructor
  · exact Coverage.success_cost_lower limits sample machine I b r (ENNReal.ofReal p) c hr
      world hi hz accept haccept hselect Hcap Hprob (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
      ENNReal.ofReal_ne_top Hcost
  · exact success_binomial limits sample machine I b r hr world hi hz accept haccept hselect
      Hcap p ℓ hℓ (fun t ht => Hprob t
        (lt_of_lt_of_le ht ((min_le_left _ _).trans (Nat.le_succ _)))) Hlat

end Cslib.Probability.NativeBatch.Deadline
