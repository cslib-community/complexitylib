/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.History
public import CslibFrontier.Probability.StochasticOracle.DiscreteComparison
import Mathlib.Tactic

/-!
# Native progress comparison without a finite response alphabet

[Wang2027], Appendix A.5, PDF p. 16. Conditional envelopes are imposed only at
positive-probability observations of the actual selected source batch. The count
uses actual native receipt histories, including zero-call decisions. Hidden memory,
private randomness and all response correlations remain in the native law.

## Main results

* `count_upper`, `count_lower`: increasing nonnegative count payoffs compared with
  independent Bernoulli trials, without independence of actual responses.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.ProgressComparison
open NativeOpenExecution NativeInterface StochasticOracle ConcurrentBatch Turing Trace Quantitative
open scoped ENNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)
variable (machine : MultiTapePTM k Bool Control Unit)

/-- The exact native progress indicator at the most recent epoch. -/
@[expose] def indicator (event : List (Record n) → Record n → Bool)
    (state : State n k Private Control input) : Bool :=
  event state.records.tail (state.records.headD none)

private theorem conditional_payoff (prior : PMF (State n k Private Control input))
    (o : Observation n)
    (ho : o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support)
    (event : List (Record n) → Record n → Bool) (f : ℕ → ℝ) :
    mean (conditional limits sample machine prior o)
        (fun state => ENNReal.ofReal (f (AdaptiveSelection.count event state.records))) =
      ∑' state, conditional limits sample machine prior o state *
        ENNReal.ofReal (if indicator event state then
          f (AdaptiveSelection.count event o.history + 1)
          else f (AdaptiveSelection.count event o.history)) := by
  apply tsum_congr
  intro state
  by_cases hs : state ∈ (conditional limits sample machine prior o).support
  · obtain ⟨record, he⟩ := History.conditional_records limits sample machine prior o ho state hs
    have hc : AdaptiveSelection.count event state.records =
        AdaptiveSelection.count event o.history + if indicator event state then 1 else 0 := by
      simp only [indicator, he, AdaptiveSelection.count, List.tail_cons, List.headD_cons]
    change _ * ENNReal.ofReal (f (AdaptiveSelection.count event state.records)) = _
    rw [hc]
    cases indicator event state <;> simp
  · simp [(PMF.apply_eq_zero_iff _ _).mpr hs]

/-- One actual selected epoch satisfies the Bernoulli upper comparison. -/
theorem step_upper (prior : PMF (State n k Private Control input))
    (event : List (Record n) → Record n → Bool) (p : Set.Icc (0 : ℝ) 1)
    (H : ∀ o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support,
      History.conditionalMean limits sample machine prior o
        (fun h x => if event h x then 1 else 0) ≤ ENNReal.ofReal p)
    (f : ℕ → ℝ) (hf : Monotone f) (hf0 : ∀ j, 0 ≤ f j)
    (remaining : ℕ) :
    mean (prior.bind (Trace.step limits sample machine)) (fun state => ENNReal.ofReal
        (bernoulliExpectation p f remaining (AdaptiveSelection.count event state.records))) ≤
      mean prior (fun state => ENNReal.ofReal
        (bernoulliExpectation p f (remaining + 1)
          (AdaptiveSelection.count event state.records))) := by
  rw [History.selected_mean, ← History.selected_history limits sample machine prior
    (fun h => ENNReal.ofReal (bernoulliExpectation p f (remaining + 1)
      (AdaptiveSelection.count event h)))]
  apply tsum_le_tsum
  intro o
  by_cases ho : o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support
  · apply mul_le_mul_right
    rw [conditional_payoff limits sample machine prior o ho]
    exact DiscreteComparison.binary_mean_upper _ (indicator event) p _ _ p.2.1
      (DiscreteComparison.bernoulli_nonneg p f hf0 _ _)
      (bernoulliExpectation_mono p p.2.1 p.2.2 f hf _ (Nat.le_succ _)) (H o ho)
  · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]

/-- One actual selected epoch satisfies the Bernoulli lower comparison. -/
theorem step_lower (prior : PMF (State n k Private Control input))
    (event : List (Record n) → Record n → Bool) (p : Set.Icc (0 : ℝ) 1)
    (H : ∀ o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support,
      ENNReal.ofReal p ≤ History.conditionalMean limits sample machine prior o
        (fun h x => if event h x then 1 else 0))
    (f : ℕ → ℝ) (hf : Monotone f) (hf0 : ∀ j, 0 ≤ f j)
    (remaining : ℕ) :
    mean prior (fun state => ENNReal.ofReal
        (bernoulliExpectation p f (remaining + 1) (AdaptiveSelection.count event state.records))) ≤
      mean (prior.bind (Trace.step limits sample machine)) (fun state => ENNReal.ofReal
        (bernoulliExpectation p f remaining (AdaptiveSelection.count event state.records))) := by
  rw [History.selected_mean, ← History.selected_history limits sample machine prior
    (fun h => ENNReal.ofReal (bernoulliExpectation p f (remaining + 1)
      (AdaptiveSelection.count event h)))]
  apply tsum_le_tsum
  intro o
  by_cases ho : o ∈ ((select limits sample machine prior).map (Quantitative.observe limits)).support
  · apply mul_le_mul_right
    rw [conditional_payoff limits sample machine prior o ho]
    exact DiscreteComparison.binary_mean_lower _ (indicator event) p _ _
      (DiscreteComparison.bernoulli_nonneg p f hf0 _ _)
      (bernoulliExpectation_mono p p.2.1 p.2.2 f hf _ (Nat.le_succ _)) (H o ho)
  · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]

/-- Actual native count upper comparison. Envelopes concern only reached selected
histories; neither finite metadata nor independent responses are required. -/
theorem count_upper (world : World k Control Unit (ServerState n Private) input)
    (event : List (Record n) → Record n → Bool) (p : Set.Icc (0 : ℝ) 1) (turns : ℕ)
    (H : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      History.conditionalMean limits sample machine (law limits sample machine t world) o
        (fun h x => if event h x then 1 else 0) ≤ ENNReal.ofReal p)
    (f : ℕ → ℝ) (hf : Monotone f) (hf0 : ∀ j, 0 ≤ f j) :
    mean (law limits sample machine turns world)
        (fun state => ENNReal.ofReal (f (AdaptiveSelection.count event state.records))) ≤
      ENNReal.ofReal (bernoulliExpectation p f turns 0) := by
  have hd (t : ℕ) (ht : t ≤ turns) :
      mean (law limits sample machine t world) (fun state => ENNReal.ofReal
          (bernoulliExpectation p f (turns - t) (AdaptiveSelection.count event state.records))) ≤
        ENNReal.ofReal (bernoulliExpectation p f turns 0) := by
    induction t with
    | zero => simp [law, ObservedProcess.stateLaw, Trace.initial, mean, PMF.pure_apply,
        AdaptiveSelection.count]
    | succ t ih =>
      have hlt : t < turns := by omega
      have he : turns - t = turns - (t + 1) + 1 := by omega
      exact (step_upper limits sample machine _ event p (H t hlt) f hf hf0
        (turns - (t + 1))).trans (by simpa only [he] using ih (by omega))
  simpa only [Nat.sub_self, bernoulliExpectation] using hd turns le_rfl

/-- Actual native count lower comparison, including the degenerate parameters
`p = 1` and zero target count. Halting padding must be included in the event's
conditional envelope; no continuation or output correctness is assumed here. -/
theorem count_lower (world : World k Control Unit (ServerState n Private) input)
    (event : List (Record n) → Record n → Bool) (p : Set.Icc (0 : ℝ) 1) (turns : ℕ)
    (H : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ENNReal.ofReal p ≤ History.conditionalMean limits sample machine
        (law limits sample machine t world) o (fun h x => if event h x then 1 else 0))
    (f : ℕ → ℝ) (hf : Monotone f) (hf0 : ∀ j, 0 ≤ f j) :
    ENNReal.ofReal (bernoulliExpectation p f turns 0) ≤
      mean (law limits sample machine turns world)
        (fun state => ENNReal.ofReal (f (AdaptiveSelection.count event state.records))) := by
  have hd (t : ℕ) (ht : t ≤ turns) :
      ENNReal.ofReal (bernoulliExpectation p f turns 0) ≤
        mean (law limits sample machine t world) (fun state => ENNReal.ofReal
          (bernoulliExpectation p f (turns - t)
            (AdaptiveSelection.count event state.records))) := by
    induction t with
    | zero => simp [law, ObservedProcess.stateLaw, Trace.initial, mean, PMF.pure_apply,
        AdaptiveSelection.count]
    | succ t ih =>
      have hlt : t < turns := by omega
      have he : turns - t = turns - (t + 1) + 1 := by omega
      have hi := ih (by omega : t ≤ turns)
      rw [he] at hi
      exact hi.trans
        (step_lower limits sample machine _ event p (H t hlt) f hf hf0 (turns - (t + 1)))
  simpa only [Nat.sub_self, bernoulliExpectation] using hd turns le_rfl

end Cslib.Probability.NativeBatch.ProgressComparison
