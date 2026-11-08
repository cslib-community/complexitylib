/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeBatch.Coverage
import Complexity.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Actual native retained coverage and stopped tail-sum costs

[Wang2027], Theorem 5(1), PDF p. 12, Appendix A.5 p. 16. Run the existing local
dual test on decoded proposals in actual native receipts. Productivity controls
coverage through a proved residual-count argument. Issued batches cease at retained
completion; conditional source costs then give the binomial survival-sum bound.

The productivity envelope includes zero-call decisions. Consequently a machine
which halts or silently diverges before completion does not satisfy it for positive
progress parameters. Realizing a uniform native selector and returning its certified
retained cover remain separate obligations; this module proves the actual receipt
coverage/cost bounds, not that missing implementation.

## Main results

* `completion`: native retained coverage dominates the actual binomial upper tail.
* `failure`: the corresponding binomial survival bound.
* `cost_tail_sum`, `cost_mean`: actual accrued cost bounded by the survival sum and `c*r/p`.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Retained
open NativeOpenExecution NativeInterface StochasticOracle ConcurrentBatch Turing Trace Quantitative
open AdaptiveSelection PartialCover Coverage
open scoped ENNReal
variable {n k m : ℕ} {Private Control E : Type} [DecidableEq E] {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)
variable (machine : MultiTapePTM k Bool Control Unit)

open scoped Classical in
/-- Actual local-test retained completion, as a function of the true receipt history. -/
@[expose] def complete (I : Instance E (Fin m)) (ρ : ℝ) (history : List (Record n)) : Bool :=
  decide (I.covered (selected I ρ (proposal m) history) = I.ground)

/-- Conditional productivity on actual native epochs forces retained coverage;
no terminal coverage implication is supplied as a premise. -/
theorem completion (I : Instance E (Fin m)) (ρ : ℝ) (a r turns : ℕ)
    (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ENNReal.ofReal p ≤ History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if productive I ρ (proposal m) a h x then 1 else 0)) :
    ENNReal.ofReal (∫ j, (if r ≤ j then (1 : ℝ) else 0)
        ∂ProbabilityTheory.binomial turns p) ≤
      (law limits sample machine turns world).map
        (fun state => complete I ρ state.records) true := by
  classical
  have hm : Monotone (fun j : ℕ => if r ≤ j then (1 : ℝ) else 0) := by
    intro i j hij
    dsimp only
    split_ifs <;> norm_num; omega
  have hc := ProgressComparison.count_lower limits sample machine world
    (productive I ρ (proposal m) a) p turns H _ hm (by intro j; split_ifs <;> norm_num)
  rw [bernoulliExpectation_eq_integral] at hc
  simp only [Nat.zero_add] at hc
  apply hc.trans
  rw [← DiscreteComparison.indicator_mean]
  unfold mean
  apply tsum_le_tsum
  intro state
  apply mul_le_mul_right
  by_cases hs : r ≤ count (productive I ρ (proposal m) a) state.records
  · have he := count_completes I ρ (proposal m) a state.records
      (hr.trans (Nat.mul_le_mul_left a hs))
    simp [hs, complete, he]
  · simp [hs]

/-- Actual retained failure is bounded by the binomial survival probability. -/
theorem failure (I : Instance E (Fin m)) (ρ : ℝ) (a r turns : ℕ)
    (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (world : World k Control Unit (ServerState n Private) input)
    (H : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ENNReal.ofReal p ≤ History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if productive I ρ (proposal m) a h x then 1 else 0)) :
    (law limits sample machine turns world).map (fun state => !complete I ρ state.records) true ≤
      ENNReal.ofReal (binomialFailure p r turns) := by
  rw [PMF.map_not_true, binomialFailure_eq_complement, ENNReal.ofReal_sub _
    (by positivity), ENNReal.ofReal_one]
  exact tsub_le_tsub_left (completion limits sample machine I ρ a r turns hr p world H) 1

/-- Stopping issued batches at actual retained completion transfers the source
conditional invoice upper envelope to the binomial survival sum. -/
theorem cost_tail_sum (I : Instance E (Fin m)) (ρ : ℝ) (a r turns : ℕ)
    (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (c : ℝ≥0∞)
    (world : World k Control Unit (ServerState n Private) input)
    (Hprod : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ENNReal.ofReal p ≤ History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if productive I ρ (proposal m) a h x then 1 else 0))
    (Hstop : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → complete I ρ o.history = false)
    (Hcost : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → Quantitative.conditionalMean limits sample machine
        (law limits sample machine t world) o charge ≤ c) :
    Quantitative.expected limits sample machine charge turns world ≤
      c * ENNReal.ofReal (∑ t ∈ Finset.range turns, binomialFailure p r t) := by
  apply (cost_upper limits sample machine c turns world Hcost).trans
  apply mul_le_mul_right
  rw [expected_accrued, ENNReal.ofReal_sum_of_nonneg
    (fun t _ => binomialFailure_nonneg p r t)]
  apply Finset.sum_le_sum
  intro t ht
  have hlt := Finset.mem_range.mp ht
  apply le_trans _ (failure limits sample machine I ρ a r t hr p world
    (fun j hj => Hprod j (by omega)))
  unfold marginal
  rw [← DiscreteComparison.indicator_mean]
  change _ ≤ mean (law limits sample machine t world)
    (fun state => if !complete I ρ state.records then 1 else 0)
  rw [← History.selected_history limits sample machine
    (law limits sample machine t world) (fun h => if !complete I ρ h then 1 else 0)]
  apply tsum_le_tsum
  intro o
  by_cases ho : o ∈ ((select limits sample machine
      (law limits sample machine t world)).map (Quantitative.observe limits)).support
  · dsimp only
    rw [conditional_issued limits sample machine _ o ho]
    apply mul_le_mul_right
    by_cases hi : o.issued = true
    · simp [hi, Hstop t hlt o ho hi]
    · simp [hi]
  · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]

/-- Finite actual native accrued cost has the horizon-uniform `c*r/p` bound,
using the proved binomial tail sum rather than a stopping-mean hypothesis. -/
theorem cost_mean (I : Instance E (Fin m)) (ρ : ℝ) (a r turns : ℕ)
    (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ))
    (c : ℝ≥0∞) (world : World k Control Unit (ServerState n Private) input)
    (Hprod : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ENNReal.ofReal p ≤ History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if productive I ρ (proposal m) a h x then 1 else 0))
    (Hstop : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → complete I ρ o.history = false)
    (Hcost : ∀ t < turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → Quantitative.conditionalMean limits sample machine
        (law limits sample machine t world) o charge ≤ c) :
    Quantitative.expected limits sample machine charge turns world ≤ c * ENNReal.ofReal (r / p) :=
  (cost_tail_sum limits sample machine I ρ a r turns hr p c world Hprod Hstop Hcost).trans
    (mul_le_mul_right (ENNReal.ofReal_le_ofReal (sum_binomialFailure_le p hp turns r)) c)

/-- Whole-policy actual accrued bill, including retained bills on divergent
outcomes, has the source upper mean bound. Envelopes cover only the issued-turn
budget, not an additional fictitious productive trial for silent completion. -/
theorem complete_cost_mean (I : Instance E (Fin m)) (ρ : ℝ) (a r : ℕ)
    (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ))
    (c : ℝ≥0∞) (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory)
    (Hprod : ∀ t < limits.turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      ENNReal.ofReal p ≤ History.conditionalMean limits sample machine
        (law limits sample machine t world) o
        (fun h x => if productive I ρ (proposal m) a h x then 1 else 0))
    (Hstop : ∀ t < limits.turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → complete I ρ o.history = false)
    (Hcost : ∀ t < limits.turns, ∀ o ∈ ((select limits sample machine
        (law limits sample machine t world)).map (Quantitative.observe limits)).support,
      o.issued = true → Quantitative.conditionalMean limits sample machine
        (law limits sample machine t world) o charge ≤ c) :
    Quantitative.expected limits sample machine charge (limits.turns + 1) world ≤
      c * ENNReal.ofReal (r / p) := by
  rw [History.final_expected_static limits sample machine world hi charge rfl]
  exact cost_mean limits sample machine I ρ a r limits.turns hr p hp c world Hprod Hstop Hcost

end Cslib.Probability.NativeBatch.Retained
