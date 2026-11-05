/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of combined RAW geometric prefix payment)
import Complexity.Foundations.Probability.HierarchyPrefixNoise
import all ComplexityTests.HierarchySemanticNoise
import all ComplexityTests.HierarchyGatedNoise
import all ComplexityTests.HierarchyRawNoiseSplit

/-!
The actual decoder bound holds along growing full horizons with positive precision,
inherited suffixes, genuine canonical references and bounded supplied histories.
The imported genuine nonzero semantic-boundary and centered-transport regressions
remain separate from any claim about post-walk nonzeroness or recursive IH.
The final scalar witness rejects discarding the prefix cube at fixed precision;
it is not an estimator-error lower bound. Adapted fixtures retain Samuel Schlesinger credit.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace PrefixNoiseRegression

-- M is unbounded; this checks the full final production decoder prefix, rather
-- than hiding a fixed terminal index. Endpoint calls are supplied, not recursive IH.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (F : Environment 5 3 → ℝ)
    (hF : ∀ σ, |F σ| ≤ (RawNoiseSplitRegression.data HP).atomCap)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (M : ℕ) (hM : 0 < M) :
    let B := RawNoiseSplitRegression.data HP
    let r := RawNoiseSplitRegression.request HP
    0 < B.requestPrecision M r ∧
    rowNormPow 4 5 r.source.rate
      (retainedMask 0 (side 5 0) B.padding [1])
      (retainedMask 2 (side 5 0) B.padding [2, 3])
      (actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0) B.padding [1] [2, 3] 0 G
        (firstSignalIncrement (B.rawFirstPrefixes (RawNoiseSplitRegression.history F)
          M .residual r) 0 (fun _ _ _ _ => 0)) 0 0 (Nat.log2 M)) ≤
      (1024 / (1 - ((64 : ℝ)⁻¹) ^ 8)) *
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 8 *
        ((Nat.log2 M + 1 : ℕ) : ℝ) ^ 3 * ((64 : ℝ)⁻¹) ^ 8 := by
  dsimp only
  let B := RawNoiseSplitRegression.data HP
  let r := RawNoiseSplitRegression.request HP
  constructor
  · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    simpa [B, r, RawNoiseSplitRegression.data, RawNoiseSplitRegression.request,
      PolynomialBudgetHistory.data, PolynomialBudgetHistory.request,
      requestPrecision, LogSpaceEstimation.precision, gridChannel, rate] using
      (div_pos hMr (by norm_num : (0 : ℝ) < 16))
  have hbound := B.rawFirstPrefixes_decoded_noise_prefix_le
    (RawNoiseSplitRegression.history F) M r 0 2 (by decide) 0 0 [1] [2, 3]
    rfl rfl rfl le_rfl
    (by intro i hi; simp only [show B.bins = ∅ from rfl, notMem_empty] at hi)
    (⟨2, 0, by decide, by decide⟩ : Horizon 5) (by decide) (by
      intro j _ bin hb
      have hbin : bin = none := by
        simpa only [BudgetData.rays, show B.bins = ∅ from rfl, toList_empty,
          List.map_nil, List.nil_append, List.mem_singleton] using hb
      subst bin
      dsimp only
      intro _
      constructor <;> intro _ <;> exact ⟨_, RawNoiseSplitRegression.sample HP F _⟩)
    G hG (fun _ _ _ _ => 0) (Nat.log2 M) (by omega) (by
      intro j _ bin hb m _ _
      have hbin : bin = none := by
        simpa only [BudgetData.rays, show B.bins = ∅ from rfl, toList_empty,
          List.map_nil, List.nil_append, List.mem_singleton] using hb
      subst bin
      exact GatedNoiseRegression.gates HP F hF m)
  simpa only [dyadicSlack_last, pow_one, Nat.cast_ofNat] using hbound

-- Empty-prefix behavior is included by the geometric lemma; no artificial
-- positive-prefix hypothesis is needed to apply the bound.
example (ε : ℝ) (m : ℕ) :
    16 * ((0 : ℝ) ^ 3 * ∑ i ∈ range 0,
      64 * (ε * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 8) ≤
      (1024 / (1 - ((64 : ℝ)⁻¹) ^ 8)) * ε ^ 8 * (0 : ℝ) ^ 3 *
        ((64 : ℝ)⁻¹ ^ dyadicSlack m (0 - 1)) ^ 8 := by
  simpa only [Nat.cast_zero] using combinedNoiseEnvelope_prefix_le ε m 0 (Nat.zero_le m)

-- Positive scalar precision p=1 alone cannot pay this conservative envelope
-- by epsilon^4 on every finite horizon. No large finite sum is evaluated.
example : (1 / 2 : ℝ) ^ 4 <
    16 * ((1048576 : ℝ) ^ 3 * ∑ i ∈ range 1048576,
      64 * ((1 / 2 : ℝ) * (64 : ℝ)⁻¹ ^ dyadicSlack 1048576 i) ^ 8) := by
  have h := combinedNoiseEnvelope_final_lower (1 / 2) 1048575
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
  norm_num at h ⊢
  linarith only [h]

end PrefixNoiseRegression
