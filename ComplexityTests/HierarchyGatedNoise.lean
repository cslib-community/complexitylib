/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of grid-gated transported RAW noise)
import Complexity.Foundations.Probability.HierarchyGatedNoise
import all ComplexityTests.HierarchyRawNoiseSplit
import all ComplexityTests.HierarchyCutoffs

/-!
Actual unequal positive endpoints consume gated range payment against the genuine
canonical correction, with inherited suffixes and the actual decoder denominator.
The history adapts Samuel Schlesinger's whole-environment execution fixture; it is
not asserted to satisfy recursive IH. Nonzero transport does not imply nonzero
completed noise. Exact arithmetic guards cover both grid-rounding directions.
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
namespace GatedNoiseRegression

example : gridMass 5 1 = 81 / 625 ∧ (1 : ℝ) / 16 < gridMass 5 1 := by
  norm_num [gridMass, show side 5 1 = 3 from rfl]

example : ∃ H : Horizon 5, 2 ≤ H.maxExponent ∧
    (5 : ℝ) * rate 2 = 5 / 256 ∧ (5 : ℝ) * rate 2 < 1 ∧
    1 ≤ (5 : ℝ) ^ 4 * rate 2 := by
  refine ⟨⟨2, 0, by decide, by decide⟩, le_rfl, ?_⟩
  norm_num [rate]

private lemma gates (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (F : Environment 5 3 → ℝ)
    (hF : ∀ σ, |F σ| ≤ (RawNoiseSplitRegression.data HP).atomCap) (m : ℕ) :
    (RawNoiseSplitRegression.data HP).ResidualEndpointGates
      (RawNoiseSplitRegression.history F) m (RawNoiseSplitRegression.request HP) none := by
  refine ⟨(fun σ _ _ => if m = 63 then F σ else 0), ?_, ?_⟩
  · rfl
  · intro σ x y
    split_ifs
    · exact hF σ
    · rw [abs_zero]
      exact mul_nonneg (by norm_num) (HP.Q_nonneg _)

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
      8 * (B.rawRelativeNoiseBudget 64 r 0 2 (by decide) 0 0 [1] [2, 3]
        (fun i => B.residualSemanticGroupInput 64 (dyadicSlack 7 i) r) G 7 +
        (7 : ℝ) ^ 3 * ∑ i ∈ range 7,
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
  apply (h.trans (B.rawRelativeNoiseBudget_residual_split_le
    (RawNoiseSplitRegression.history F) 64 r 0 2 (by decide) 0 0 [1] [2, 3] rfl G 7)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add le_rfl
  apply B.rawRelativeNoiseGroup_transported_le_of_gates (RawNoiseSplitRegression.history F)
    64 r 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl le_rfl
    (by intro i hi; simp only [show B.bins = ∅ from rfl, notMem_empty] at hi)
    (⟨2, 0, by decide, by decide⟩ : Horizon 5) (by decide) G hG 7
  intro i hi bin hb m _ _
  have hbin : bin = none := by
    simpa only [BudgetData.rays, show B.bins = ∅ from rfl, toList_empty,
      List.map_nil, List.nil_append, List.mem_singleton] using hb
  subst bin
  exact gates HP F hF m

-- A nonconstant bounded history gives nonzero actual centered transported input.
-- The reference remains canonical; this history is not recursive IH.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ F : Environment 5 3 → ℝ,
      (∀ σ, |F σ| ≤ (RawNoiseSplitRegression.data HP).atomCap) ∧
      (fun σ x y =>
        (RawNoiseSplitRegression.data HP).residualTransportedGroupInput
          (RawNoiseSplitRegression.history F) 64 1 (RawNoiseSplitRegression.request HP) σ x y -
        rowSliceMean (retainedMask 0 (side 5 0) (1 : ZMod 5) [1])
          (retainedMask 2 (side 5 0) (1 : ZMod 5) [2, 3])
          ((RawNoiseSplitRegression.data HP).residualTransportedGroupInput
            (RawNoiseSplitRegression.history F) 64 1
            (RawNoiseSplitRegression.request HP)) x y) ≠ 0 := by
  let c := HP.Q 1
  have hc : 0 < c := CutoffRegression.Q_one_pos HP
  have hcap : c ≤ (RawNoiseSplitRegression.data HP).atomCap := by
    have ha := HP.toHierarchyParams.atomCap_gt
    have h1 : 1 ≤ HP.toHierarchyParams.atomCap := by
      have hn : 0 ≤ (HP.k : ℝ) := Nat.cast_nonneg _
      linarith [le_max_left ((HP.k : ℝ) + 1) HP.θ₂]
    have hh := HP.Q_mono h1
    change c ≤ 2 * HP.Q HP.toHierarchyParams.atomCap
    linarith [HP.Q_nonneg HP.toHierarchyParams.atomCap]
  let F : Environment 5 3 → ℝ := fun σ => if (σ 1).1 0 = 0 then c else 0
  refine ⟨F, ?_, ?_⟩
  · intro σ
    dsimp only [F]
    split_ifs
    · rwa [abs_of_pos hc]
    · rw [abs_zero]; exact hc.le.trans hcap
  · have hframe : Nonempty (Frame 5 4 1) := Frame.nonempty (by decide)
    let frame : Frame 5 4 1 := Classical.choice hframe
    let σ₀ : Environment 5 3 := fun _ => (fun _ => 0, frame)
    let σ₁ : Environment 5 3 := fun _ => (fun _ => 1, frame)
    have hin := (RawNoiseSplitRegression.data HP).decodedGroupInput_eq_transported_of_two_mul_lt
      (RawNoiseSplitRegression.history F) 64 1 (RawNoiseSplitRegression.request HP) (by decide)
    rw [← hin, RawNoiseSplitRegression.actual_input]
    intro hz
    have h₀ := congrFun (congrFun (congrFun hz σ₀) 0) 0
    have h₁ := congrFun (congrFun (congrFun hz σ₁) 0) 0
    norm_num only [F, σ₀, σ₁, one_ne_zero, ↓reduceIte, neg_zero,
      Pi.zero_apply] at h₀ h₁
    linarith

-- A successful positive-bin call uses three actual row lookups. The reference
-- is the genuine dense/correction family, even though this supplied history is zero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    let B := PolynomialBudgetHistory.data HP
    let r := RawNoiseSplitRegression.request HP
    rowNormPow 4 5 (rate 0)
      (retainedMask 0 (side 5 0) B.padding [1])
      (retainedMask 2 (side 5 0) B.padding [2, 3])
      (fun σ x y => ((B.sample (fun _ _ => some (.row 0)) 63 .residual r (some 1)).getD 0
        σ x y - B.residualCanonicalRay r (some 1) σ x y) / (rate 0 + G x y)) ≤
      4096 * 5 * B.positiveCharge r 1 0 ^ 4 / rate 0 ^ 3 := by
  dsimp only
  let B := PolynomialBudgetHistory.data HP
  let r := RawNoiseSplitRegression.request HP
  apply B.residualSample_relative_fourth_le_of_gates (fun _ _ => some (.row 0))
    63 (by decide) r 0 2 (by decide) 0 0 [1] [2, 3] rfl (fun _ => rfl)
    (⟨2, 0, by decide, by decide⟩ : Horizon 5) (by decide) (by decide) (some 1) ?_ G hG
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro q _; rfl
  · intro σ x y; change |(0 : ℝ)| ≤ 2 * B.binCap
    rw [abs_zero]; exact mul_nonneg (by norm_num) B.binCap_nonneg
  · intro σ x z; change |(0 : ℝ)| ≤ B.atomCap
    rw [abs_zero]; exact mul_nonneg (by norm_num) (HP.Q_nonneg _)
  · intro σ z y; change |(0 : ℝ)| ≤ 2 * B.binCap
    rw [abs_zero]; exact mul_nonneg (by norm_num) B.binCap_nonneg

-- Actual production steps are paid on the admissible Pf<1 horizon as well.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := PolynomialBudgetHistory.data HP
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
      ⟨.residual 0, gridChannel 0 2 [1], gridChannel 2 2 [2, 3], gridChannel 2 2 [2, 3]⟩
    (131072 * B.magnitude r ^ 4 / ((5 : ℝ) ^ 3 * rate 2 ^ 3)) *
      (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)) ^ (2 * B.steps 64 r 1) ≤
      64 * (((2 : ℝ) ^ (-B.requestPrecision 64 r)) * (64 : ℝ)⁻¹) ^ 8 := by
  dsimp only
  simpa only [pow_one, Nat.cast_ofNat] using
    (PolynomialBudgetHistory.data HP).transported_range_spectral_payment
    64 1 _ 2 2 rfl le_rfl (⟨2, 0, by decide, by decide⟩ : Horizon 5) le_rfl

-- The all-vertex identity includes two positive bins and the negative ray once.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := PolynomialBudgetHistory.data HP
    let r := RawNoiseSplitRegression.request HP
    10 * (B.positiveCharge r 0 0 + B.positiveCharge r 1 0 + B.atomCap) =
      B.magnitude r - 1 - B.atomCap := by
  dsimp only
  have hh := (PolynomialBudgetHistory.data HP).magnitude_grid_eq
    (RawNoiseSplitRegression.request HP) 0 rfl (by intro i _; rfl)
  simpa only [show (PolynomialBudgetHistory.data HP).bins = {0, 1} from rfl,
    sum_pair (by decide : (0 : ℕ) ≠ 1), rate, pow_zero, inv_one, one_pow,
    one_mul, Nat.cast_ofNat, show (2 : ℝ) * 5 = 10 by norm_num] using hh

end GatedNoiseRegression
