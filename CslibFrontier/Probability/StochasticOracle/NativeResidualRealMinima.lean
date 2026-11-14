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
The conditional invoice kernel may depend on the accepted source history, the
selected batch and its residual. `NativeResidualConditionalInvoice.HasMean` fixes
the expected batch charge before the residual is known. Universal lower accounting
uses those primitive means; both actual compiled strategies attain the upper
alternatives for that same kernel. Fixed-PMF results are constant-kernel
specializations. No integer price identity, integrability, termination
or optimum conclusion is assumed.

This is a generalization of the source's fixed-cost construction, not a
source-policy compiler or a general measurable-oracle representation theorem.

## Main results

* `native_optimum_conditional`, `native_one_optimum_conditional`: attained native optima
  for history- and response-dependent invoice laws.
* `native_ratio_conditional`, `native_linear_ratio_conditional`: their exact adaptivity ratios.
* `native_optimum`, `native_one_optimum`: fixed invoice-law specializations.
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
theorem native_optimum_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z) :
    BatchOptimum.optimum limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (min (∑ j, P.specialistCost j)
          (P.nearCost + P.missing.mean P.specialistCost)) := by
  apply le_antisymm (sInf_le
    (NativeResidualRealAdaptive.minimum_cost_mem_conditional T points candidates P ν hν hz))
  let c := (finCongr (rows_length T points candidates)).trans candidates
  have hdata : (input T points candidates).startup.system =
      SourceEncoding.toNative (source T points c) := by
    rw [source_reindex]
    rfl
  have hlower := NativeResidualOptimum.two_lower_of_conditional_mean T points
    (input T points candidates) c
    P limits ν (by omega)
    (valid T points candidates (by omega)) hdata rfl hν
  dsimp only [c, input] at hlower
  rwa [NativeResidualConditionalInvoice.sample_reindex T points candidates
    (rows_length T points candidates)] at hlower

/-- All specialists attain the universal one-turn lower bound on this same oracle. -/
theorem native_one_optimum_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z) :
    BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (∑ j, P.specialistCost j) := by
  apply le_antisymm (NativeResidualRealCost.native_all_upper_conditional T points candidates P ν hν
    hz 1
    (by omega))
  let c := (finCongr (rows_length T points candidates)).trans candidates
  have hdata : (input T points candidates).startup.system =
      SourceEncoding.toNative (source T points c) := by
    rw [source_reindex]
    rfl
  have hlower := NativeResidualOptimum.one_lower_of_conditional_mean T points
    (input T points candidates) c
    P (NativeResidualAll.config 1) ν
    (by omega) (valid T points candidates (by omega)) hdata rfl hν
  dsimp only [c, input] at hlower
  rwa [NativeResidualConditionalInvoice.sample_reindex T points candidates
    (rows_length T points candidates)] at hlower

/-- The source ratio holds for arbitrary positive real costs, with both native
optima finite by their derived exact equalities. -/
theorem native_ratio_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z)
    (c α : ℝ) (hc : 0 < c) (hs : ∀ j, P.specialistCost j = c)
    (h0 : P.nearCost = α * c) :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal /
    (BatchOptimum.optimum limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal =
        (z : ℝ) / min (z : ℝ) (α + 1) := by
  have hsum : 0 ≤ ∑ j, P.specialistCost j :=
    Finset.sum_nonneg (fun j _ => (P.specialist_pos j).le)
  have hmean : 0 ≤ P.missing.mean P.specialistCost :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (P.missing.nonneg j) (P.specialist_pos j).le)
  rw [native_one_optimum_conditional T points candidates P ν hν hz,
    native_optimum_conditional T points candidates P ν hν hz,
    ENNReal.toReal_ofReal hsum,
    ENNReal.toReal_ofReal (le_min hsum (add_nonneg P.near_pos.le hmean))]
  exact homogeneous_ratio P c α hc hs h0

/-- The linear branch of the source ratio, with its threshold explicit. -/
theorem native_linear_ratio_conditional (P : Parameters z)
    (ν : NativeResidualConditionalInvoice.Kernel z)
    (hν : NativeResidualConditionalInvoice.HasMean P ν) (hz : 3 ≤ z)
    (c α : ℝ) (hc : 0 < c) (hs : ∀ j, P.specialistCost j = c)
    (h0 : P.nearCost = α * c) (hgap : α + 1 < (z : ℝ)) :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal /
    (BatchOptimum.optimum limits (NativeResidualConditionalInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal =
        (z : ℝ) / (α + 1) := by
  simpa only [min_eq_right hgap.le] using
    native_ratio_conditional T points candidates P ν hν hz c α hc hs h0

/-- The fixed-law native result is a constant-kernel specialization. -/
theorem native_optimum (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) :
    BatchOptimum.optimum limits (NativeResidualInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (min (∑ j, P.specialistCost j)
          (P.nearCost + P.missing.mean P.specialistCost)) := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_optimum_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz

/-- The fixed-law native result is a constant-kernel specialization. -/
theorem native_one_optimum (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z) :
    BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1 =
        ENNReal.ofReal (∑ j, P.specialistCost j) := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_one_optimum_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz

/-- The fixed-law native result is a constant-kernel specialization. -/
theorem native_ratio (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z)
    (c α : ℝ) (hc : 0 < c) (hs : ∀ j, P.specialistCost j = c)
    (h0 : P.nearCost = α * c) :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal /
    (BatchOptimum.optimum limits (NativeResidualInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal =
        (z : ℝ) / min (z : ℝ) (α + 1) := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_ratio_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz c α hc hs h0

/-- The fixed-law native result is a constant-kernel specialization. -/
theorem native_linear_ratio (P : Parameters z)
    (ν : PMF (Fin (z + 1) → ℕ)) (hν : NativeResidualInvoice.HasMean P ν) (hz : 3 ≤ z)
    (c α : ℝ) (hc : 0 < c) (hs : ∀ j, P.specialistCost j = c)
    (h0 : P.nearCost = α * c) (hgap : α + 1 < (z : ℝ)) :
    (BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal /
    (BatchOptimum.optimum limits (NativeResidualInvoice.sample T points candidates P ν)
      (input T points candidates) () (valid T points candidates (by omega)) 1).toReal =
        (z : ℝ) / (α + 1) := by
  simpa only [NativeResidualConditionalInvoice.sample_const] using
    native_linear_ratio_conditional T points candidates P (fun _ _ _ => ν)
      (NativeResidualConditionalInvoice.hasMean_const hν) hz c α hc hs h0 hgap


end Cslib.Probability.StochasticOracle.NativeResidualRealMinima
