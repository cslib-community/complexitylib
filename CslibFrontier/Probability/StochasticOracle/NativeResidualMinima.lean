/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualAll

/-!
# Attained two-turn native residual optimum

[Wang2027], Theorem 6, PDF p. 13. Both alternatives in the source minimum
are attained by fixed compiled controllers on the same original encoded input,
oracle and seed. Competitors are all admitted finite-control native machines,
with unbounded local computation and successful-output-only selection provenance.
Discrete invoices are explicitly identified with the source prices.

## Main results

* `native_cost_mem`: the source minimum is attained in the native competitor class.
* `native_optimum`: the native two-turn optimum equals the source minimum.

The native one-turn lower bound and equality, ratio and uniform cost-aware choice
are separate obligations; the one-turn all-specialist upper bound is already
`NativeResidualAll.native_upper`.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualMinima
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRetention ResidualCover
open NativeResidualEncoding NativeResidualAttainment
open scoped ENNReal
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- Both cases of the source minimum are attained as actual accrued native bills,
not merely as behavioral scores or upper envelopes. -/
theorem native_cost_mem (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    ENNReal.ofReal (min (∑ j, P.specialistCost j)
      (P.nearCost + P.missing.mean P.specialistCost)) ∈
      BatchOptimum.costs limits (NativeResidualOracle.sample T points candidates P invoice)
        (input T points candidates) () (valid T points candidates (by omega)) 1 := by
  by_cases h : P.nearCost + P.missing.mean P.specialistCost ≤ ∑ j, P.specialistCost j
  · rw [min_eq_right h]
    exact NativeResidualAttainment.native_cost_mem T points candidates P invoice hz hprice
  · rw [min_eq_left (le_of_not_ge h)]
    exact NativeResidualAll.native_cost_mem T points candidates P invoice hz 2 (by omega) hprice

/-- Exact native two-turn optimum over the existing common-oracle Theorem 5 class.
The controller witnessing the upper bound is chosen from the two concrete compiled
programs; no optimum, success or expected-cost certificate is assumed. -/
theorem native_optimum (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    BatchOptimum.optimum limits (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (min (∑ j, P.specialistCost j)
          (P.nearCost + P.missing.mean P.specialistCost)) := by
  apply le_antisymm (sInf_le (native_cost_mem T points candidates P invoice hz hprice))
  let c := (finCongr (rows_length T points candidates)).trans candidates
  have hdata : (input T points candidates).startup.system =
      SourceEncoding.toNative (source T points c) := by
    rw [source_reindex]
    rfl
  have hlower := NativeResidualOptimum.two_lower T points (input T points candidates) c
    P limits invoice (by omega) (valid T points candidates (by omega)) hdata rfl hprice
  dsimp only [c, input] at hlower
  rwa [NativeResidualOracle.sample_reindex T points candidates
    (rows_length T points candidates)] at hlower

end Cslib.Probability.StochasticOracle.NativeResidualMinima
