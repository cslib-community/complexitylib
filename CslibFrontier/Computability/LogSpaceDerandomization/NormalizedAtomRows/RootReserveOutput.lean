/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.ReserveOutput
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.ChildRootReserve

/-!
# Actual finite output from lower-child rooted errors

This discharges the conditional cost premise of `ReserveOutput` using bounded normalized
lower-child rooted moments on their own source and full terminal rank. The finite sufficient
allocation displays its vertex width, call-count, bin, rate and density costs.
There is no environment-cardinality or minimum-atom-probability payment.
It does not prove recursive accuracy, copy routing, parameter/workspace growth or RL=L.
The finite geometric, routing and cutoff hypotheses are supplied in `ReserveOutputContext`,
with the independent raw, preparation and maximum families in `ReserveOutputChildren`.
Their named constructions are defined in `OutputContext`; the error premise and output bound
remain explicit in the theorem statement.
The output constant is chosen after HP, ζ, scale and the positive floor, before the
prime, environment width, horizon, prefix length or child families. Child accuracies may
therefore be chosen using that constant without depending circularly on those families.
This uniformity concerns the final output coefficient only; the displayed allocation and
walk lengths still retain their P, rate, bin and finite-horizon factors.
The underlying row/normalization assembly is adapted from Samuel Schlesinger.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- Actual finite output from explicit per-request rooted-error budgets on bounded
normalized children. The lower-child conditional cost reserve is discharged. The allocation
is finite and conservative; recursive accuracy and parameter/workspace closure remain open. -/
theorem actualEstimatedResidual_output_from_root_budgets
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale floor : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hsmall : ζ ≤ scale / 2) (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000)
    (hfloor : 0 < floor) (hfloors : floor ≤ scale) (hfloor1 : floor ≤ 1) (hfloorθ : floor ≤ HP.θ) :
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ (P J : ℕ) [Fact P.Prime] (ctx : ReserveOutputContext HP P J)
    (children : ReserveOutputChildren HP P J) (ε : ℝ), 0 < ε →
    let amplification := ctx.amplification ζ
    let tolerance := ctx.tolerance ε
    (∀ j < ctx.prefixLength, ∀ i r,
      (i, r) ∈ HierarchyTask.residualErrorCalls (k := HP.k) (range (ctx.lastBin + 1)) ctx.level
        ctx.source ctx.midpoint ctx.terminal (fun i => rate (ctx.binExponent i)) →
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains ctx.channelsV σ x)
        (fun σ y => r.terminal.retains ctx.channelsV σ y)
        (fun σ => (ctx.estimated children) (j + 1) i σ r) (fun σ => ctx.canonical i σ r) ≤
      ((tolerance ^ 4 / (1 + (rate ctx.terminalExponent)⁻¹ ^ 4 + amplification)) /
        (1 + (Fintype.card (ZMod P) : ℝ) ^ 2 / ((P : ℝ) * rate ctx.sourceExponent) *
          HierarchyTask.residualCostCoefficient (k := HP.k) ctx.channelsV (range (ctx.lastBin +
            1)) ctx.level
            ctx.source ctx.midpoint ctx.terminal (fun i => rate (ctx.binExponent i))
            (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max ctx.densityCap 16))) /
        (1 + (4 * (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max ctx.densityCap 16)) ^
          ((3 : ℝ) / 4)) ^ 4 * ((P : ℝ) * r.source.rate)) /
        (1 + #(HierarchyTask.residualErrorCalls (k := HP.k) (range (ctx.lastBin + 1)) ctx.level
          ctx.source ctx.midpoint ctx.terminal (fun i => rate (ctx.binExponent i))))) →
    rowNormPow 4 P (rate ctx.sourceExponent) (retainedMask ctx.roles.source (side P
      ctx.sourceExponent) ctx.direction ctx.sourceSuffix)
      (retainedMask ctx.roles.terminal (side P ctx.usageExponent) ctx.direction ctx.terminalSuffix)
      (fun σ x y => actualNormalizedCompatible HP ζ floor ctx.roles.terminal (side P
        ctx.usageExponent) ctx.direction ctx.terminalSuffix ctx.terminalExponent ctx.prefixLength
        (ctx.increment children ζ ε) (fun _ _ _ _ => 0) σ x y ^ (4⁻¹ : ℝ) -
        genuineNormalizedRecipe HP ctx.roles.source ctx.roles.terminal (side P ctx.sourceExponent)
          (side P ctx.usageExponent) ctx.direction ctx.sourceSuffix ctx.terminalSuffix
          ctx.terminalExponent ctx.residual σ x y ^
          (4⁻¹ : ℝ)) ≤ Cbound * ε ^ 4 := by
  obtain ⟨Cbound, hCbound, hout⟩ := actualEstimatedResidual_output_from_cost_reserves
    HP hζ hs hmargin hsmall hcapscale hfloor hfloors hfloor1 hfloorθ
  refine ⟨Cbound, hCbound, ?_⟩
  intro P J inst ctx children ε hε
  dsimp only
  intro hroot
  apply hout P J ctx children ε hε
  intro j hj
  have hp := actual_conditionalChildCost_le_of_root_budgets HP ctx.direction ctx.roles ctx.level
    ctx.sourceExponent ctx.midpointExponent ctx.terminalExponent ctx.lastBin ctx.sourceSuffix
    ctx.midpointSuffix ctx.terminalSuffix ctx.binExponent
    ctx.kernel ctx.kernel_nonneg ctx.binCutoff ctx.cutoff_one ctx.preparationCutoff
      ctx.requestGate ctx.requestRank (fun v => ⟨ctx.requestGate_nonneg v, ctx.requestGate_le_one
      v⟩) ctx.cutoff_monotone ctx.cutoff_zero ctx.cutoff_range ctx.rates_antitone ctx.rate_ratio
      ctx.densityCap_nonneg ctx.kernel_cap
    ctx.correctionRank (children.raw (j + 1)) (children.prep (j + 1)) (children.maximum (j + 1))
    (δ := (ctx.tolerance ε) ^ 4 / (1 + (rate ctx.terminalExponent)⁻¹ ^ 4 + (ctx.amplification ζ)))
    (by dsimp only [ReserveOutputContext.amplification]; positivity)
    (hroot j hj)
  unfold ReserveOutputContext.cost ReserveOutputContext.channelsV
  unfold HierarchyTask.conditionalChildCost at hp ⊢
  unfold retainedMask
  convert hp using 1;
    simp only [rowSliceMean, CorrectionRowTask.Channel.retains, channels, gridChannel,
      semanticSide_grid, id_eq]
  congr!

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
