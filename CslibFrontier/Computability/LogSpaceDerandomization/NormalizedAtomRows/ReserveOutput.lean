/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.OutputContext
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.ActualMoment
import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.FiniteEnvelopePayment

/-!
# Conditional finite output from actual lower-child cost reserves

Completed full-terminal RAW walking precedes selected preparation and the narrower
preparation walk. Both signals enter the actual compatible-capacity compression iterate.
Only actual lower-child conditional-error-cost row moments are reserved. The finite
allocation retains visible horizon dependence and full B1 width/rate amplification.
This is an original finite assembly of the existing conditional output theorem.
Recursive reserve induction, copy routing and parameter/workspace growth remain open.
The finite geometric, routing and cutoff hypotheses are supplied in `ReserveOutputContext`,
with the independent raw, preparation and maximum families in `ReserveOutputChildren`.
Their named constructions are defined in `OutputContext`; the error premise and output bound
remain explicit in the theorem statement.
The output constant is chosen after HP, ζ, scale and the positive floor, before the
prime, environment width, horizon, prefix length or child families. Child accuracies may
therefore be chosen using that constant without depending circularly on those families.
This uniformity concerns the final output coefficient only; the displayed allocation and
walk lengths still retain their P, rate, bin and finite-horizon factors.
The row/normalization proof patterns are adapted from Samuel Schlesinger.

## Main results

* `actualEstimatedResidual_output_from_cost_reserves`: finite output fourth-root error
  bound from conditional lower-child cost moments, with both walk lengths chosen.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

private lemma allocation_max_le (m : ℕ) {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) :
    let d := (ε / (2 * (m + 1))) ^ 4
    (m : ℝ) * max (a * (d / (1 + a + b)))
      (b * (8 * (d / (1 + b) + d / (1 + a + b)))) ≤ ε ^ 4 := by
  dsimp only
  let d := (ε / (2 * (m + 1))) ^ 4
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have ha' : a * (d / (1 + a + b)) ≤ d := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb' : b * (d / (1 + a + b)) ≤ d := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb'' : b * (d / (1 + b)) ≤ d := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hp : max (a * (d / (1 + a + b)))
      (b * (8 * (d / (1 + b) + d / (1 + a + b)))) ≤ 16 * d :=
    max_le (by linarith) (by nlinarith only [hb', hb''])
  apply (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg m)).trans
  change (m : ℝ) * (16 * (ε / (2 * (m + 1))) ^ 4) ≤ ε ^ 4
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm2 : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hm4 : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 4 := by nlinarith [sq_nonneg (((m : ℝ) + 1) ^ 2 - 1)]
  calc
    _ = (m : ℝ) * ε ^ 4 / ((m : ℝ) + 1) ^ 4 := by
      rw [div_pow, mul_pow]
      field_simp
      ring
    _ ≤ ε ^ 4 := (div_le_iff₀ (by positivity)).mpr
      (by nlinarith [mul_le_mul_of_nonneg_right hm4 (pow_nonneg hε 4)])

set_option backward.isDefEq.respectTransparency false in
/-- Actual finite output at the genuine canonical residual, under explicit conditional
lower-child cost reserves. Common B, both endpoint ROW noises, nonnegativity, row mass
and zero extension are derived. No recursive growth or native RL=L endpoint is claimed. -/
theorem actualEstimatedResidual_output_from_cost_reserves
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale floor : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hsmall : ζ ≤ scale / 2) (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000)
    (hfloor : 0 < floor) (hfloors : floor ≤ scale) (hfloor1 : floor ≤ 1) (hfloorθ : floor ≤ HP.θ) :
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ (P J : ℕ) [Fact P.Prime] (ctx : ReserveOutputContext HP P J)
    (children : ReserveOutputChildren HP P J) (ε : ℝ), 0 < ε →
    let amplification := ctx.amplification ζ
    let tolerance := ctx.tolerance ε
    (∀ i < ctx.prefixLength, rowNormPow 4 P (rate ctx.sourceExponent) (retainedMask
      ctx.roles.source (side P ctx.sourceExponent) ctx.direction ctx.sourceSuffix)
      (retainedMask ctx.roles.terminal (side P ctx.terminalExponent) ctx.direction
        ctx.terminalSuffix) (fun _ => (ctx.cost children) i) ≤
        tolerance ^ 4 / (1 + (rate ctx.terminalExponent)⁻¹ ^ 4 + amplification)) →
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
  obtain ⟨_, _, hfloorbound⟩ := actual_normalized_fourth_moment_compatible HP hζ hs hmargin
    hsmall hcapscale
  obtain ⟨Cbound, hCbound, hout⟩ := hfloorbound floor hfloor hfloors hfloor1 hfloorθ
  refine ⟨Cbound, hCbound, ?_⟩
  intro P J inst ctx children ε hε
  dsimp only
  intro hreserve
  have hHPK : 0 < HP.K := by
    have hg := HP.gate
    have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
      div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
    have hk : (0 : ℝ) < HP.K := by linarith
    exact_mod_cast hk
  have htol : 0 < (ctx.tolerance ε) := by dsimp only [ReserveOutputContext.tolerance]; positivity
  have hamp : 0 ≤ (ctx.amplification ζ) := by
    dsimp only [ReserveOutputContext.amplification]
    positivity
  have hden : (1 : ℝ) < 155648 * (J + 1) * (4 : ℝ) ^ 4 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hr : 0 < (reserveOutputContraction J) := sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hr1 : (reserveOutputContraction J) < 1 := sub_lt_self _ (by positivity)
  have hG : ∀ x y, 0 ≤ ctx.residual x y := HP.toHierarchyParams.residual_nonneg (rate_pos
    ctx.midpointExponent) ctx.kernel_nonneg
  let B := commonMeanEnvelope ctx.roles ctx.direction ctx.sourceSuffix ctx.terminalSuffix
    ctx.sourceExponent ctx.terminalExponent ctx.usageExponent ctx.prefixLength
    ctx.preparationLipschitz ctx.gateLipschitz ζ (ctx.input children) (ctx.rawWalk children ζ ε)
    ctx.residual
  have hrawpay (i : ℕ) (_hi : i < ctx.prefixLength) : 32 * (reserveOutputContraction J) ^ (2 *
    (ctx.rawSteps ζ ε) (i + 1)) * ctx.payment ≤
      (ctx.tolerance ε) ^ 4 / (1 + (ctx.amplification ζ)) := by
    have hp := spectralWalkLength_payment hr hr1
      (by dsimp only [ReserveOutputContext.payment]; positivity : 0 ≤ (1 + (ctx.amplification ζ))
        * 32 * ctx.payment)
      htol 0 ((ctx.rawSteps ζ ε) (i + 1)) (Nat.le_max_right _ _)
    simp only [pow_zero, mul_one] at hp
    apply (le_div_iff₀ (by positivity : 0 < 1 + (ctx.amplification ζ))).mpr
    nlinarith only [hp]
  have hBrow (ν : Fin 2) : rowNormPow 4 P (rate ctx.sourceExponent)
      (retainedMask ctx.roles.source (side P ctx.sourceExponent) ctx.direction ctx.sourceSuffix)
      (retainedMask ctx.roles.terminal (if ν = 0 then side P ctx.terminalExponent else side P
        ctx.usageExponent) ctx.direction ctx.terminalSuffix) (fun _ => B ν)
        ≤ ε ^ 4 := by
    have hp := actualEstimatedResidual_common_envelope_payment HP ctx.direction
      ctx.direction_ne_zero ctx.horizon ctx.roles ctx.level ctx.sourceExponent
      ctx.midpointExponent ctx.terminalExponent ctx.lastBin ctx.source_in_horizon
      ctx.midpoint_le_source
      ctx.sourceSuffix ctx.midpointSuffix ctx.terminalSuffix ctx.binExponent ctx.bins_in_horizon
        ctx.kernel ctx.kernel_nonneg ctx.kernel_row_mass ctx.kernel_rate ctx.binCutoff
        ctx.cutoff_one ctx.preparationCutoff ctx.requestGate ctx.requestRank ctx.preparation_one
        ctx.requestGate_nonneg ctx.requestGate_le_one ctx.gateThreshold_pos ctx.gate_one
        ctx.rank_bound
      ctx.cutoff_monotone ctx.cutoff_zero ctx.cutoff_range ctx.rates_antitone ctx.rate_ratio
        ctx.densityCap_nonneg ctx.kernel_cap ctx.correctionRank children.raw children.prep
        children.maximum ctx.kernel_cover (ctx.rawSteps ζ ε) ctx.usageExponent ctx.terminal_le_usage
      ctx.preparationLipschitz_nonneg ctx.gateLipschitz_nonneg ζ ctx.prefixLength ((ctx.tolerance
        ε) ^ 4 / (1 + (rate ctx.terminalExponent)⁻¹ ^ 4 + (ctx.amplification ζ)))
      ((ctx.tolerance ε) ^ 4 / (1 + (ctx.amplification ζ))) hreserve hrawpay ν
    change rowNormPow 4 P (rate ctx.sourceExponent) _ _ (fun _ => B ν) ≤ _ at hp
    have hnum := allocation_max_le (m := ctx.prefixLength) (a := (rate ctx.terminalExponent)⁻¹ ^
      4) (b := (ctx.amplification ζ))
      (by positivity) hamp hε.le
    simpa only [apply_ite] using hp.trans hnum
  apply hout P J ctx.roles.source ctx.roles.terminal ctx.roles.source_terminal.symm (side P
    ctx.sourceExponent) (side P ctx.usageExponent) ctx.direction ctx.direction_ne_zero
    ctx.sourceSuffix
    ctx.terminalSuffix ctx.horizon ctx.terminalExponent ctx.terminal_in_horizon
    (by
      rw [side_eq_ceil, side_eq_ceil]
      exact Nat.ceil_mono (mul_le_mul_of_nonneg_left
        (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) ctx.terminal_le_usage)) (by
          positivity)))
    ctx.residual hG (fun x => (HP.toHierarchyParams.residual_sum_le_one _ _ (rate_pos
      ctx.midpointExponent) ctx.kernel_row_mass x).trans
      (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)) P (rate ctx.sourceExponent) ε
    (mul_nonneg (Nat.cast_nonneg P) (rate_pos ctx.sourceExponent).le) hε.le ctx.prefixLength
      ctx.prefixLength_pos (ctx.increment children ζ ε) (fun _ _ _ _ => 0) B
    (commonMeanEnvelope_nonneg ctx.roles ctx.direction ctx.sourceSuffix ctx.terminalSuffix
      ctx.sourceExponent ctx.terminalExponent ctx.usageExponent ctx.prefixLength
      ctx.preparationLipschitz ctx.gateLipschitz ζ (ctx.input children) (ctx.rawWalk children ζ ε)
      ctx.residual) ?_ hBrow ?_ ?_
  · exact actualTwoSignal_mean_le_common HP hHPK ctx.direction ctx.roles ctx.sourceExponent
      ctx.terminalExponent ctx.usageExponent ctx.prefixLength ctx.terminal_le_usage
      ctx.sourceSuffix ctx.terminalSuffix (ctx.input children) (ctx.rawSteps ζ ε)
      (ctx.prepSteps ζ ε)
      ctx.gateLipschitz_nonneg ctx.preparation_lipschitz ctx.gate_lipschitz ζ ctx.residual
  · intro ν i hi
    fin_cases ν
    · change rowNormPow 4 P (rate ctx.sourceExponent) (retainedMask ctx.roles.source (side P
      ctx.sourceExponent) ctx.direction ctx.sourceSuffix)
        (retainedMask ctx.roles.terminal (side P ctx.terminalExponent) ctx.direction
          ctx.terminalSuffix)
        (actualNoiseEntry ctx.roles.source ctx.roles.terminal (side P ctx.sourceExponent) (side P
          ctx.terminalExponent) (side P ctx.terminalExponent) ctx.direction ctx.sourceSuffix
          ctx.terminalSuffix ctx.terminalExponent ctx.residual
          (ctx.increment children ζ ε) (fun _ _ _ _ => 0) 0 i) ≤ (ε * (1 / 64 : ℝ) ^ dyadicSlack
            ctx.prefixLength i) ^ 4
      simpa only [one_div] using actualEstimatedFirstSignal_noise_le_dyadic HP hHPK ctx.direction
        ctx.roles ctx.horizon ctx.level
        ctx.sourceExponent ctx.midpointExponent ctx.terminalExponent ctx.lastBin
          ctx.source_in_horizon ctx.sourceSuffix ctx.midpointSuffix ctx.terminalSuffix
          ctx.binExponent ctx.correctionRank
        ctx.bounded (estimatedBinCap ctx.densityCap) (fun i => by
          have hcap := ctx.densityCap_nonneg
          unfold estimatedBinCap
          split_ifs <;> positivity)
        (boundedRoutedBinCutoff_grid_range ctx.binCutoff ctx.binExponent ctx.densityCap_nonneg
          ctx.cutoff_monotone ctx.cutoff_zero ctx.cutoff_one ctx.cutoff_range ctx.rates_antitone
          ctx.rate_ratio)
        children.raw children.prep children.maximum (ctx.rawSteps ζ ε) ctx.residual hG
          (secondSignalIncrement (ctx.prepWalk children ζ ε) ζ) (fun _ _ _ _ => 0)
        (by intros; rfl) i hε ctx.prefixLength (by simpa only [ReserveOutputContext.rawSteps,
          Nat.add_sub_cancel] using (Nat.le_max_left
          (spectralWalkLength (reserveOutputContraction J) ((rate ctx.terminalExponent)⁻¹ ^ 4 * 32
            * ctx.payment) ε (dyadicSlack ctx.prefixLength i))
          (spectralWalkLength (reserveOutputContraction J) ((1 + (ctx.amplification ζ)) * 32 *
            ctx.payment) (ctx.tolerance ε) 0)))
    · change rowNormPow 4 P (rate ctx.sourceExponent) (retainedMask ctx.roles.source (side P
      ctx.sourceExponent) ctx.direction ctx.sourceSuffix)
        (retainedMask ctx.roles.terminal (side P ctx.usageExponent) ctx.direction
          ctx.terminalSuffix)
        (actualNoiseEntry ctx.roles.source ctx.roles.terminal (side P ctx.sourceExponent) (side P
          ctx.terminalExponent) (side P ctx.usageExponent) ctx.direction ctx.sourceSuffix
          ctx.terminalSuffix ctx.terminalExponent ctx.residual
          (ctx.increment children ζ ε) (fun _ _ _ _ => 0) 1 i) ≤ (ε * (1 / 64 : ℝ) ^ dyadicSlack
            ctx.prefixLength i) ^ 4
      simpa only [one_div] using actualSelectedSecondSignal_noise_le_dyadic HP hHPK ctx.direction
        ctx.roles ctx.horizon ctx.sourceExponent
        ctx.terminalExponent ctx.usageExponent ctx.terminal_le_usage ctx.source_in_horizon
          ctx.sourceSuffix ctx.terminalSuffix (ctx.rawWalk children ζ ε) (ctx.rawWalk children ζ ε)
        (ctx.prepSteps ζ ε) ζ ctx.residual i ctx.prefixLength hε (by
          simp only [ReserveOutputContext.prepSteps, Nat.add_sub_cancel]
          exact le_rfl)
  · intro i σ x y hy
    exact (actualTwoSignal_zero_off ctx.roles.source ctx.roles.terminal (side P
      ctx.sourceExponent) (side P ctx.usageExponent) ctx.direction ctx.sourceSuffix
      ctx.terminalSuffix
      (fun _ => graph ctx.roles.source ctx.roles.terminal ctx.roles.source_terminal (side P
        ctx.sourceExponent) (side P ctx.usageExponent)
        (side_le P ctx.sourceExponent) (side_le P ctx.usageExponent) (fun x =>
          CopyPadding.identifier ctx.direction ctx.sourceSuffix x)
        (fun y => CopyPadding.identifier ctx.direction ctx.terminalSuffix y)) (fun j _ _ =>
          (ctx.prepSteps ζ ε) j) (ctx.preparation children ζ ε) (ctx.rawWalk children ζ ε)
          ctx.terminalExponent ζ σ x y hy).1 i

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
