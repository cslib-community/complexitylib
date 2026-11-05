/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of actual combined RAW decoder allocation)
import Complexity.Foundations.Probability.HierarchyDecoderAllocation
import all ComplexityTests.HierarchyPrefixNoise
import all ComplexityTests.HierarchySemanticNoise
import all ComplexityTests.HierarchyGatedNoise
import all ComplexityTests.HierarchyRawNoiseSplit

/-!
A common charge precedes the growing budget family and actual positive precision.
The complete production decoder retains inherited nonempty suffixes and arbitrary
bounded correlated supplied histories. Imported semantic-boundary, transport-input,
unequal-endpoint and exhaustion regressions are freshly checked separately.
Supplied histories are not recursive IH; nonzero input is not post-walk nonzero noise.
Adapted production fixtures retain Samuel Schlesinger's credit.
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
namespace DecoderAllocationRegression

-- Every larger charge works; the family is selected only after that charge.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (F : Environment 5 3 → ℝ)
    (_hF : ∀ σ, |F σ| ≤ (RawNoiseSplitRegression.data HP).atomCap)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (_hG : ∀ x y, 0 ≤ G x y),
    let B := RawNoiseSplitRegression.data HP
    let r := RawNoiseSplitRegression.request HP
    let m := Nat.log2 (2 ^ N) + 1
    let a := fun j => rowNormPow 4 5 r.source.rate
      (retainedMask 0 (side 5 0) B.padding [1])
      (retainedMask 2 (side 5 0) B.padding [2, 3])
      (actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0) B.padding [1] [2, 3] 0 G
        (firstSignalIncrement
          (B.rawFirstPrefixes (RawNoiseSplitRegression.history F) (2 ^ N) .residual r)
          0 (fun _ _ _ _ => 0)) 0 0 j)
    0 < B.requestPrecision (2 ^ N) r ∧
    initialSeparatedReserve HP 1 1
      (∑ j ∈ range m, dyadicFloor 1 m j * a j ^ (4⁻¹ : ℝ))
      (a (Nat.log2 (2 ^ N)) ^ (4⁻¹ : ℝ))
      (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ))
      (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) *
        ((2 * max 16 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor 1 m j ^ 4)) * a j) ≤
      ((2 : ℝ) ^ (-B.requestPrecision (2 ^ N) r)) ^ 4 := by
  let B := RawNoiseSplitRegression.data HP
  let r := RawNoiseSplitRegression.request HP
  obtain ⟨A₀, _, halloc⟩ := exists_rawFirstPrefixes_decoded_noise_reserve_charge
    HP 1 16 1 1 (by norm_num) 0
  refine ⟨A₀, ?_⟩
  intro A hA
  obtain ⟨N₀, hfamily⟩ := exists_prefix_budget_family A B 0 0 r
  refine ⟨N₀, ?_⟩
  intro N hN F hF G hG
  dsimp only
  have hb := hfamily N hN
  have hp := B.requestPrecision_prefix_margin A (2 ^ N) 0 0 r rfl rfl hb
  constructor
  · have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hm0 : (0 : ℝ) ≤ (Nat.log2 (2 ^ N) + 1 : ℕ) := Nat.cast_nonneg _
    linarith only [hp, hA0, hm0]
  have hbound := halloc A hA B (RawNoiseSplitRegression.history F) (2 ^ N) r
    0 2 (by decide) 0 0 [1] [2, 3] rfl rfl rfl le_rfl
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
    G hG (fun _ _ _ _ => 0) (by
      intro j _ bin hb m _ _
      have hbin : bin = none := by
        simpa only [BudgetData.rays, show B.bins = ∅ from rfl, toList_empty,
          List.map_nil, List.nil_append, List.mem_singleton] using hb
      subst bin
      exact GatedNoiseRegression.gates HP F hF m) hb
  exact hbound

-- The excluded positive-precision envelope witness does not satisfy the margin.
example (A : ℕ) : ¬ ((A : ℝ) + (Nat.log2 1048576 + 1 : ℕ) + 3 ≤ 1) := by
  norm_num
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  linarith

-- The fixed-precision obstruction concerns the envelope, not actual estimator error.
example (p T : ℝ) : ¬ ∀ m : ℕ, 0 < m →
    16 * ((m : ℝ) ^ 3 * ∑ i ∈ range m,
      64 * ((2 : ℝ) ^ (-p) * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 8) ≤ T :=
  combinedNoiseEnvelope_not_uniform _ T (by positivity)

end DecoderAllocationRegression
