/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualRealAdaptive

/-!
# Native residual optima with arbitrary fixed real expected prices

[Wang2027], Theorem 6 and proof, PDF p. 13. All admitted finite-control
selection-only native competitors use the same fresh-invoice residual oracle,
original encoded instance and seed. Their local computation is unbounded.
The constructed invoice law is drawn independently of the residual index `J`
and the preceding history. Universal lower accounting uses the derived primitive conditional
price means;
the two actual compiled strategies attain both upper alternatives. No integer
price identity, integrability, termination or optimum conclusion is assumed.

These equalities concern `FixedMeanInvoice`. Extending attained equalities to every
fixed invoice PMF with the same means, or to history-dependent invoice kernels
with those conditional means, remains separate work; the more general fixed-PMF
lower bounds alone do not supply that attainment.

## Main results

* `native_optimum`, `native_one_optimum`: attained two- and one-turn native optima.
* `native_ratio`, `native_linear_ratio`: the source adaptivity ratio for real prices.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualRealMinima
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRetention ResidualCover
open NativeResidualEncoding NativeResidualAttainment
open scoped ENNReal
variable {z n m : ℕ} (T : Fin z → Block)
variable (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)

/-- The source two-turn minimum equals the infimum over all admitted native
competitors, and is attained by the existing compiled source strategies. -/
theorem native_optimum (P : Parameters z) (hz : 3 ≤ z) :
    BatchOptimum.optimum limits (NativeResidualRealCost.sample T points candidates P)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (min (∑ j, P.specialistCost j)
          (P.nearCost + P.missing.mean P.specialistCost)) := by
  apply le_antisymm (sInf_le
    (NativeResidualRealAdaptive.minimum_cost_mem T points candidates P hz))
  let c := (finCongr (rows_length T points candidates)).trans candidates
  have hdata : (input T points candidates).startup.system =
      SourceEncoding.toNative (source T points c) := by
    rw [source_reindex]
    rfl
  have hlower := NativeResidualOptimum.two_lower_of_mean T points (input T points candidates) c
    P limits (FixedMeanInvoice.law (NativeResidualRealCost.prices P)) (by omega)
    (valid T points candidates (by omega)) hdata rfl (NativeResidualRealCost.hasMean P)
  dsimp only [c, input] at hlower
  rwa [NativeResidualInvoice.sample_reindex T points candidates
    (rows_length T points candidates)] at hlower

/-- All specialists attain the universal one-turn lower bound on this same oracle. -/
theorem native_one_optimum (P : Parameters z) (hz : 3 ≤ z) :
    BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualRealCost.sample T points candidates P)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (∑ j, P.specialistCost j) := by
  apply le_antisymm (NativeResidualRealCost.native_all_upper T points candidates P hz 1 (by omega))
  let c := (finCongr (rows_length T points candidates)).trans candidates
  have hdata : (input T points candidates).startup.system =
      SourceEncoding.toNative (source T points c) := by
    rw [source_reindex]
    rfl
  have hlower := NativeResidualOptimum.one_lower_of_mean T points (input T points candidates) c
    P (NativeResidualAll.config 1) (FixedMeanInvoice.law (NativeResidualRealCost.prices P))
    (by omega) (valid T points candidates (by omega)) hdata rfl (NativeResidualRealCost.hasMean P)
  dsimp only [c, input] at hlower
  rwa [NativeResidualInvoice.sample_reindex T points candidates
    (rows_length T points candidates)] at hlower

/-- The source ratio holds for arbitrary positive real costs, with both native
optima finite by their derived exact equalities. -/
theorem native_ratio (P : Parameters z) (hz : 3 ≤ z)
    (c α : ℝ) (hc : 0 < c) (hs : ∀ j, P.specialistCost j = c)
    (h0 : P.nearCost = α * c) :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualRealCost.sample T points candidates P)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal /
    (BatchOptimum.optimum limits (NativeResidualRealCost.sample T points candidates P)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal =
        (z : ℝ) / min (z : ℝ) (α + 1) := by
  have hsum : 0 ≤ ∑ j, P.specialistCost j :=
    Finset.sum_nonneg (fun j _ => (P.specialist_pos j).le)
  have hmean : 0 ≤ P.missing.mean P.specialistCost :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (P.missing.nonneg j) (P.specialist_pos j).le)
  rw [native_one_optimum T points candidates P hz, native_optimum T points candidates P hz,
    ENNReal.toReal_ofReal hsum,
    ENNReal.toReal_ofReal (le_min hsum (add_nonneg P.near_pos.le hmean))]
  exact homogeneous_ratio P c α hc hs h0

/-- The linear branch of the source ratio, with its threshold explicit. -/
theorem native_linear_ratio (P : Parameters z) (hz : 3 ≤ z)
    (c α : ℝ) (hc : 0 < c) (hs : ∀ j, P.specialistCost j = c)
    (h0 : P.nearCost = α * c) (hgap : α + 1 < (z : ℝ)) :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualRealCost.sample T points candidates P)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal /
    (BatchOptimum.optimum limits (NativeResidualRealCost.sample T points candidates P)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal =
        (z : ℝ) / (α + 1) := by
  simpa only [min_eq_right hgap.le] using
    native_ratio T points candidates P hz c α hc hs h0

end Cslib.Probability.StochasticOracle.NativeResidualRealMinima
