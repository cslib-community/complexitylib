/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualAll

/-!
# Attained one- and two-turn native residual optima

[Wang2027], Theorem 6, PDF p. 13. Both alternatives in the source minimum
are attained by fixed compiled controllers on the same original encoded input,
oracle and seed. Competitors are all admitted finite-control native machines,
with unbounded local computation and successful-output-only selection provenance.
Discrete invoices are explicitly identified with the source prices.

## Main results

* `native_cost_mem`: the source minimum is attained in the native competitor class.
* `native_optimum`, `native_one_optimum`: native optima equal the source minima.
* `native_ratio`, `native_linear_ratio`: the source adaptivity ratio for these native optima.

A uniform cost-aware choice compiled into a single program and arbitrary-real
invoice representation remain separate obligations.
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

/-- Exact one-turn native optimum. The all-specialist controller attains the
universal lower bound on the same original input, residual oracle and seed. -/
theorem native_one_optimum (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost) :
    BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (∑ j, P.specialistCost j) := by
  apply le_antisymm (NativeResidualAll.native_upper T points candidates P invoice hz 1
    (by omega) hprice)
  let c := (finCongr (rows_length T points candidates)).trans candidates
  have hdata : (input T points candidates).startup.system =
      SourceEncoding.toNative (source T points c) := by
    rw [source_reindex]
    rfl
  have hlower := NativeResidualOptimum.one_lower T points (input T points candidates) c
    P (NativeResidualAll.config 1) invoice (by omega)
    (valid T points candidates (by omega)) hdata rfl hprice
  dsimp only [c, input] at hlower
  rwa [NativeResidualOracle.sample_reindex T points candidates
    (rows_length T points candidates)] at hlower

/-- The source adaptivity ratio, now for the attained original native optima.
Both real parts are justified by the finite exact native optimum equalities. -/
theorem native_ratio (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost)
    (c α : ℝ) (hc : 0 < c) (hs : ∀ j, P.specialistCost j = c)
    (h0 : P.nearCost = α * c) :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal /
    (BatchOptimum.optimum limits (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal =
        (z : ℝ) / min (z : ℝ) (α + 1) := by
  have hsum : 0 ≤ ∑ j, P.specialistCost j :=
    Finset.sum_nonneg (fun j _ => (P.specialist_pos j).le)
  have hmean : 0 ≤ P.missing.mean P.specialistCost :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (P.missing.nonneg j) (P.specialist_pos j).le)
  rw [native_one_optimum T points candidates P invoice hz hprice,
    native_optimum T points candidates P invoice hz hprice,
    ENNReal.toReal_ofReal hsum,
    ENNReal.toReal_ofReal (le_min hsum (add_nonneg P.near_pos.le hmean))]
  exact homogeneous_ratio P c α hc hs h0

/-- The source's linear adaptivity-gap branch, with its threshold explicit. -/
theorem native_linear_ratio (P : Parameters z) (invoice : Fin (z + 1) → ℕ) (hz : 3 ≤ z)
    (hprice : ∀ i, (invoice i : ℝ) =
      (finSuccEquiv z i).elim P.nearCost P.specialistCost)
    (c α : ℝ) (hc : 0 < c) (hs : ∀ j, P.specialistCost j = c)
    (h0 : P.nearCost = α * c) (hgap : α + 1 < (z : ℝ)) :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal /
    (BatchOptimum.optimum limits (NativeResidualOracle.sample T points candidates P invoice)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal =
        (z : ℝ) / (α + 1) := by
  simpa only [min_eq_right hgap.le] using
    native_ratio T points candidates P invoice hz hprice c α hc hs h0

end Cslib.Probability.StochasticOracle.NativeResidualMinima
