/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of canonical semantic RAW boundary payment)
import Complexity.Foundations.Probability.HierarchySemanticNoise
import all ComplexityTests.HierarchyRawNoiseSplit
import all ComplexityTests.HierarchyCutoffs
import all ComplexityTests.HierarchyGatedNoise
import all ComplexityTests.HierarchyProductMean

/-!
Genuine nonzero canonical final correction survives an active/exhausted boundary.
The actual decoder consumes both proved budgets with positive precision and unequal
endpoints. Supplied histories do not prove recursive IH; nonzero input does not
assert nonzero post-walk noise. Fixtures preserve Samuel Schlesinger's source credit.
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
namespace SemanticNoiseRegression

-- Own positive endpoint precision is actually positive; the two executed budgets
-- differ. The denominator retains arbitrary nonnegative genuine residual data.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (F : Environment 5 3 → ℝ)
    (hF : ∀ σ, |F σ| ≤ (RawNoiseSplitRegression.data HP).atomCap)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    let B := RawNoiseSplitRegression.data HP
    let r := RawNoiseSplitRegression.request HP
    0 < B.requestPrecision 64 r ∧
    rowNormPow 4 5 r.source.rate
      (retainedMask 0 (side 5 0) B.padding [1])
      (retainedMask 2 (side 5 0) B.padding [2, 3])
      (actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0) B.padding [1] [2, 3] 0 G
        (firstSignalIncrement (B.rawFirstPrefixes (RawNoiseSplitRegression.history F)
          64 .residual r) 0 (fun _ _ _ _ => 0)) 0 0 6) ≤
      16 * ((7 : ℝ) ^ 3 * ∑ i ∈ range 7,
          64 * (((2 : ℝ) ^ (-B.requestPrecision 64 r)) *
            (64 : ℝ)⁻¹ ^ dyadicSlack 7 i) ^ 8) := by
  dsimp only
  let B := RawNoiseSplitRegression.data HP
  let r := RawNoiseSplitRegression.request HP
  constructor
  · norm_num [B, r, RawNoiseSplitRegression.data, RawNoiseSplitRegression.request,
      PolynomialBudgetHistory.data, PolynomialBudgetHistory.request,
      requestPrecision, LogSpaceEstimation.precision, gridChannel, rate]
  have h := B.rawFirstPrefixes_decoded_noise (RawNoiseSplitRegression.history F) 64 r
    0 2 (by decide) 0 0 [1] [2, 3] rfl rfl rfl (by
      intro j _ bin hb
      have hbin : bin = none := by
        simpa only [BudgetData.rays, show B.bins = ∅ from rfl, toList_empty,
          List.map_nil, List.nil_append, List.mem_singleton] using hb
      subst bin
      dsimp only
      intro _
      constructor <;> intro _ <;> exact ⟨_, RawNoiseSplitRegression.sample HP F _⟩)
    G hG (fun _ _ _ _ => 0) 6 (by decide)
  apply h.trans
  apply B.rawRelativeNoiseBudget_residual_le_of_gates (RawNoiseSplitRegression.history F)
    64 r 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl le_rfl
    (by intro i hi; simp only [show B.bins = ∅ from rfl, notMem_empty] at hi)
    (⟨2, 0, by decide, by decide⟩ : Horizon 5) (by decide) G hG 7
  intro i hi bin hb m _ _
  have hbin : bin = none := by
    simpa only [BudgetData.rays, show B.bins = ∅ from rfl, toList_empty,
      List.map_nil, List.nil_append, List.mem_singleton] using hb
  subst bin
  exact GatedNoiseRegression.gates HP F hF m

-- The actual canonical final correction is nonzero, independently of histories.
-- At the active/exhausted boundary it survives, rather than cancelling.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x : ZMod 5) :
    let B : BudgetData HP 5 := { ProductMeanRegression.data HP with bins := ∅ }
    let r := ProductMeanRegression.request HP
    (B.residualSemanticGroupInput 64 32 r = B.residualCanonicalRay r none) ∧
      B.residualSemanticGroupInput 64 32 r ≠ 0 ∧
      B.residualSemanticGroupInput 64 64 r = 0 := by
  dsimp only
  let B : BudgetData HP 5 := { ProductMeanRegression.data HP with bins := ∅ }
  let r := ProductMeanRegression.request HP
  have hb : B.residualSemanticGroupInput 64 32 r = B.residualCanonicalRay r none := by
    funext σ a b
    simp only [residualSemanticGroupInput, rays, show B.bins = ∅ from rfl,
      toList_empty, List.map_nil, List.nil_append, List.map_cons, List.sum_cons,
      List.sum_nil, add_zero, B.sampleScale_none_eq_zero]
    change (if (32 : ℕ) = 0 then 0 else _) - (if (0 : ℕ) = 0 then 0 else _) = _
    simp
  refine ⟨hb, ?_, ?_⟩
  · rw [hb]
    intro hz
    have hray : B.residualCanonicalRay r none = -ProductMeanRegression.negative HP := rfl
    rw [hray, neg_eq_zero] at hz
    have hm := ProductMeanRegression.negative_mean HP x x
    rw [hz] at hm
    have hp := ProductMeanRegression.correction_pos HP x
    simp only [rowSliceMean, Pi.zero_apply, Matrix.zero_apply, expect_const_zero] at hm
    linarith only [hm, hp]
  · exact B.residualSemanticGroupInput_eq_zero_of_le 64 64 r le_rfl

-- The genuine two-bin family is paid on the rounded, small-P*f horizon, retaining
-- the actual nonnegative residual in the denominator and arbitrary inherited suffixes.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    let B := PolynomialBudgetHistory.data HP
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
      ⟨.residual 0, gridChannel 0 2 [1], gridChannel 2 2 [2, 3], gridChannel 2 2 [2, 3]⟩
    B.rawRelativeNoiseBudget 64 r 0 2 (by decide) 2 2 [1] [2, 3]
      (fun i => B.residualSemanticGroupInput 64 (dyadicSlack 7 i) r) G 7 ≤
      (7 : ℝ) ^ 3 * ∑ i ∈ range 7,
        64 * (((2 : ℝ) ^ (-B.requestPrecision 64 r)) * (64 : ℝ)⁻¹ ^ dyadicSlack 7 i) ^ 8 := by
  dsimp only
  apply (PolynomialBudgetHistory.data HP).rawRelativeNoiseBudget_semantic_le
    64 _ 0 2 (by decide) 2 2 [1] [2, 3] rfl rfl le_rfl
    (by intro i _; rfl) (⟨2, 0, by decide, by decide⟩ : Horizon 5) le_rfl G hG

end SemanticNoiseRegression
