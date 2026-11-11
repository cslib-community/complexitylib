/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOutput
public import CslibFrontier.Computability.Probabilistic.NativeBatch.PathCost
import Mathlib.Tactic

/-!
# Theorem 5 native output and real-integrable total path bill

[Wang2027], Theorem 5(1)/App. A.5, pp. 12,16. The same original-input native
block controller has certified tape success and the source survival-sum, mean and
budget bounds for its actual infinite-path total bill. Real integrability and
almost-sure finiteness are derived, not premises. Local execution remains clockless;
oracle time alone counts against the source deadline. The unrestricted source
scheduler/compiler and nonatomic interface gaps remain separate.

## Main results

* `upper_controller`: same-code certified success and real-integrable actual total-cost bounds.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchPathCost
open Turing NativeOpenExecution NativeInterface ConcurrentBatch NativeBatch
open Trace Quantitative MeasureTheory
open scoped NNReal ENNReal NativeBatch.PathCost
variable {n : ℕ}

/-- Source reached-history progress and cost envelopes imply real total-bill
integrability, certified output and all numerical upper bounds for the same
constructed native controller; no total-cost conclusion is supplied. -/
theorem upper_controller (width : ℕ) :
    let impl := BatchPlanner.controller n width
    let program := impl.program
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (_ : data.startup.turns = limits.turns) (_ : data.startup.turns ≤ data.allotments)
        (hx : Valid data.startup.system),
      let world : World impl.tapes impl.Controls Unit (ServerState n Private)
          (GuardedStartup.encoding data) :=
        ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
      let I := instanceOf data.startup.system hx
      let parse := BatchReceipts.proposal data.startup.system
      ∀ (a r : ℕ) (_ : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (_ : 0 < (p : ℝ))
        (c : ℝ≥0)
        (_ : ∀ t < limits.turns, ∀ o ∈ ((select limits sample program
          (law limits sample program t world)).map (Quantitative.observe limits)).support,
          o.issued = true → ENNReal.ofReal p ≤ History.conditionalMean limits sample program
            (law limits sample program t world) o
            (fun h x => if AdaptiveSelection.productive I data.startup.system.rho parse a h x
              then 1 else 0))
        (_ : ∀ t < limits.turns, ∀ o ∈ ((select limits sample program
          (law limits sample program t world)).map (Quantitative.observe limits)).support,
          o.issued = true → Quantitative.conditionalMean limits sample program
            (law limits sample program t world) o charge ≤ c),
        ENNReal.ofReal (∫ j, (if r ≤ j then (1 : ℝ) else 0)
          ∂ProbabilityTheory.binomial limits.turns p) ≤
          (NativeUnboundedExecution.terminal program (environment limits sample) world).map
            (BatchOutput.certified limits data.startup.system hx) true ∧
        (∀ᵐ ω ∂PathCost.pathMeasure limits sample program world,
          PathCost.totalBill charge ω < ⊤) ∧
        Integrable (fun ω => (PathCost.totalBill charge ω).toReal)
          (PathCost.pathMeasure limits sample program world) ∧
        (∫ ω, (PathCost.totalBill charge ω).toReal
          ∂PathCost.pathMeasure limits sample program world) ≤
          (c : ℝ) * (∑ t ∈ Finset.range limits.turns, binomialFailure p r t) ∧
        (∫ ω, (PathCost.totalBill charge ω).toReal
          ∂PathCost.pathMeasure limits sample program world) ≤ (c : ℝ) * (r / p) ∧
        (∫ ω, (PathCost.totalBill charge ω).toReal
          ∂PathCost.pathMeasure limits sample program world) ≤ (c : ℝ) * limits.turns := by
  let impl := BatchPlanner.controller n width
  let program := impl.program
  dsimp only
  intro Private limits sample data seed ell hn hw hc he hcut hd hbudget hallot hx
    a r hr p hp c Hprod Hcost
  let world : World impl.tapes impl.Controls Unit (ServerState n Private)
      (GuardedStartup.encoding data) :=
    ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
  let μ := PathCost.pathMeasure limits sample program world
  have hnum := BatchOutput.upper_controller (n := n) width Private limits sample data seed ell
    hn hw hc he hcut hd hbudget hallot hx a r hr p hp c Hprod Hcost
  obtain ⟨hcert, htail, hmean, hbudgetBill, hfinite⟩ := hnum
  have htotal := PathCost.lintegral_totalBill_complete limits sample program charge rfl world
    (initial_invariant limits seed)
  change (∫⁻ ω, PathCost.totalBill charge ω ∂μ) = _ at htotal
  have hm := PathCost.measurable_totalBill (n := n) (k := impl.tapes)
    (Private := Private) (Control := impl.Controls) (input := GuardedStartup.encoding data) charge
  have hf : (∫⁻ ω, PathCost.totalBill charge ω ∂μ) ≠ ⊤ := by rw [htotal]; exact hfinite
  have hae := ae_lt_top hm hf
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hf
  have hconvert (b : ℝ) (hb : 0 ≤ b)
      (H : Quantitative.expected limits sample program charge (limits.turns + 1) world ≤
        (c : ℝ≥0∞) * ENNReal.ofReal b) :
      (∫ ω, (PathCost.totalBill charge ω).toReal ∂μ) ≤ (c : ℝ) * b := by
    rw [integral_toReal hm.aemeasurable hae, htotal]
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hb] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) H
  refine ⟨hcert, hae, hi, hconvert _ ?_ htail, hconvert _ ?_ hmean, ?_⟩
  · exact Finset.sum_nonneg (fun t _ => binomialFailure_nonneg p r t)
  · exact div_nonneg (Nat.cast_nonneg r) hp.le
  · apply hconvert _ (Nat.cast_nonneg limits.turns)
    simpa only [ENNReal.ofReal_natCast] using hbudgetBill

end Cslib.Probability.StochasticOracle.NativeRetention.BatchPathCost
