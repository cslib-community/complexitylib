/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of unaveraged endpoint noise transport)
import Complexity.Foundations.Probability.HierarchyEndpointNoise
import all ComplexityTests.HierarchyRawNoiseSplit
import all ComplexityTests.HierarchyProductTransport

/-!
Actual positive execution consumes the unaveraged product transport with nonzero
child errors. The supplied reference in that test is a constant table, not a
claimed canonical hierarchy. The separate genuine-reference residual test retains
two positive unequal endpoints, a nonconstant H4 environment and the original
denominator. Neither supplied history asserts recursive availability or accuracy.
The fixtures adapt Samuel Schlesinger's whole-environment execution pattern.
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
namespace EndpointNoiseRegression

private def residualRequest (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  { ProductTransportRegression.request HP with task := .residual 0 }

private lemma fourth_root_sixteen : (16 : ℝ) ^ (4⁻¹ : ℝ) = 2 := by
  convert Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 4)
    (by norm_num) (by decide) using 1
  norm_num

-- This bound is on the UNAVERAGED executed sample. All direct, left and right
-- own-root errors are nonzero (each equals five); reset source identity is kept.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := ProductTransportRegression.data HP
    let r := residualRequest HP
    let H := fun (_ : ℕ) (_ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) =>
      some (BudgetValue.row (fun _ _ _ => 16))
    ∃ A, B.positiveSample H 63 0 .residual r = some A ∧
      rowNormPow 4 5 r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun _ _ => True) (fun σ x y => A σ x y - 6) ≤
      8 * ((4 * (16 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 * 5 +
        (4 * (1280 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 *
          (16384 * (16 * 5 * 5 + 16 * 5 * 5))) ∧
      ∀ σ x y, A σ x y = 1296 := by
  dsimp only
  let B := ProductTransportRegression.data HP
  let r := residualRequest HP
  let child := fun (_ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
    (_ : Environment 5 3) (_ _ : ZMod 5) => (16 : ℝ)
  let canonical := fun (_ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
    (_ : Environment 5 3) (_ _ : ZMod 5) => (1 : ℝ)
  have hf (σ : Environment 5 3) (role : Fin 3) (suffix : List (ZMod 5)) (v : ZMod 5) :
      (⟨role, 1, suffix⟩ : CorrectionRowTask.Channel (Fin 3) (List (ZMod 5))).retains
        (channels (1 : ZMod 5)) σ v := by
    simpa only [gridChannel, rate, pow_zero, inv_one, one_pow] using
      PolynomialBudgetHistory.full σ role suffix v
  have hall (q : CorrectionRowTask.Channel (Fin 3) (List (ZMod 5))) (hq : q.rate = 1)
      (σ : Environment 5 3) (v : ZMod 5) : q.retains (channels (1 : ZMod 5)) σ v := by
    obtain ⟨role, b, suffix⟩ := q
    change b = 1 at hq
    subst b
    exact hf σ role suffix v
  have h := B.positiveSample_residual_fourth_le
    (fun _ _ => some (.row (fun _ _ _ => 16))) 63 0 r child canonical
    (fun _ _ => True) 16 16 16 (by norm_num) (by norm_num) 5 5 5
    (by norm_num [r, residualRequest, ProductTransportRegression.request,
      PolynomialBudgetHistory.request,
      gridChannel, rate])
    (by norm_num [BudgetData.midpoint, r, residualRequest, ProductTransportRegression.request,
      PolynomialBudgetHistory.request, gridChannel, rate])
    (by intros; rfl)
    (by intros; exact ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, by norm_num⟩⟩)
    (by intros; exact ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, by norm_num⟩⟩)
    (by intros; exact ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, by norm_num⟩⟩)
    (by
      dsimp only
      intro σ x y hy
      exact (hy (hall _ (by norm_num [B, r, ProductTransportRegression.data,
        residualRequest, ProductTransportRegression.request, PolynomialBudgetHistory.data,
        PolynomialBudgetHistory.request, HierarchyTask.rawRequests, BudgetData.midpoint,
        gridChannel, rate]) σ y)).elim)
    (by
      dsimp only
      intro σ x y hy
      exact (hy (hall _ (by norm_num [B, r, ProductTransportRegression.data,
        residualRequest, ProductTransportRegression.request, PolynomialBudgetHistory.data,
        PolynomialBudgetHistory.request, HierarchyTask.rawRequests, BudgetData.midpoint,
        gridChannel, rate]) σ y)).elim)
    (by
      dsimp only
      intro σ x z hz
      exact (hz (hall _ (by norm_num [B, r, ProductTransportRegression.data,
        residualRequest, ProductTransportRegression.request, PolynomialBudgetHistory.data,
        PolynomialBudgetHistory.request, HierarchyTask.rawRequests, BudgetData.midpoint,
        gridChannel, rate]) σ z)).elim)
    (by dsimp only; intro σ x; exact ⟨card_le_univ _, card_le_univ _⟩)
    (by dsimp only; intro σ z _; exact card_le_univ _)
    (by dsimp only; intro σ z _; exact card_le_univ _)
  obtain ⟨A, ha, hb⟩ := h
  refine ⟨A, ha, ?_, ?_⟩
  · have hroot : rootDistPow 4 5 1 (fun (_ : Environment 5 3) (_ : ZMod 5) => True)
        (fun _ _ => True) (fun _ _ _ => 16) (fun _ _ _ => 1) = 5 := by
      norm_num [rootDistPow, rowNormPow, fourth_root_sixteen]
    have hmask (σ : Environment 5 3) (role : Fin 3) (suffix : List (ZMod 5)) (v : ZMod 5) :
        ((⟨role, 1, suffix⟩ : CorrectionRowTask.Channel (Fin 3) (List (ZMod 5))).retains
          (channels (1 : ZMod 5)) σ v) = True := propext (iff_true_intro (hf σ role suffix v))
    norm_num [B, r, ProductTransportRegression.data, residualRequest,
      ProductTransportRegression.request,
      PolynomialBudgetHistory.data, PolynomialBudgetHistory.request, gridChannel, rate,
      BudgetData.midpoint, midpointRole, HierarchyTask.rawRequests, HierarchyTask.usageRatio,
      HierarchyTask.rawPositiveSample, child, canonical, hmask, hroot] at hb ⊢
    exact hb
  · intro σ x y
    have hex := B.positiveSample_of_rows (fun _ _ => some (.row (fun _ _ _ => 16)))
      63 0 .residual r child (by intros; rfl)
    rw [ha] at hex
    have hval := congrFun (congrFun (congrFun (Option.some.inj hex) σ) x) y
    norm_num [B, r, residualRequest, ProductTransportRegression.data,
      ProductTransportRegression.request, PolynomialBudgetHistory.data,
      PolynomialBudgetHistory.request, HierarchyTask.rawPositiveSample,
      HierarchyTask.rawRequests, BudgetData.midpoint, gridChannel, rate,
      HierarchyTask.usageRatio, hf, child] at hval
    exact hval

-- The genuine-reference two-endpoint moment consumer on a nonconstant H4
-- history. The finite endpoint allowances below can be supplied by the direct/
-- product and negative transport theorems; no mean-error substitute is used.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (F : Environment 5 3 → ℝ) (G : Matrix (ZMod 5) (ZMod 5) ℝ)
    (q : ℕ → Option ℕ → ℝ)
    (he : ∀ m, 0 < m → rowNormPow 4 5 1
      (retainedMask 0 (side 5 0) (1 : ZMod 5) [1])
      (retainedMask 2 (side 5 0) (1 : ZMod 5) [2, 3])
      (fun σ x y => ((RawNoiseSplitRegression.data HP).sample
        (RawNoiseSplitRegression.history F) m .residual
        (RawNoiseSplitRegression.request HP) none).getD 0 σ x y -
          (RawNoiseSplitRegression.data HP).residualCanonicalRay
            (RawNoiseSplitRegression.request HP) none σ x y) ≤ q m none) :
    let B := RawNoiseSplitRegression.data HP
    let r := RawNoiseSplitRegression.request HP
    rowNormPow 4 5 r.source.rate
      (retainedMask 0 (side 5 0) B.padding [1])
      (retainedMask 2 (side 5 0) B.padding [2, 3])
      (fun σ x y => (B.residualTransportedGroupInput
        (RawNoiseSplitRegression.history F) 64 1 r σ x y - rowSliceMean
          (retainedMask 0 (side 5 0) B.padding [1])
          (retainedMask 2 (side 5 0) B.padding [2, 3])
          (B.residualTransportedGroupInput (RawNoiseSplitRegression.history F) 64 1 r) x y) /
            (rate 0 + G x y)) ≤
      128 * ‖fun xy : ZMod 5 × ZMod 5 => (rate 0 + G xy.1 xy.2)⁻¹‖ ^ 4 *
        (q 63 none + q 62 none) := by
  dsimp only
  have h := (RawNoiseSplitRegression.data HP).residualTransportedGroupInput_centered_fourth_le
    (RawNoiseSplitRegression.history F) 64 1 (RawNoiseSplitRegression.request HP)
    (retainedMask 0 (side 5 0) (1 : ZMod 5) [1])
    (retainedMask 2 (side 5 0) (1 : ZMod 5) [2, 3]) (by norm_num [
      RawNoiseSplitRegression.request, PolynomialBudgetHistory.request, gridChannel, rate])
    (fun x y => rate 0 + G x y) q (by
      intro bin hb m hm
      have hbin : bin = none := by
        simpa only [BudgetData.rays, show (RawNoiseSplitRegression.data HP).bins = ∅ from rfl,
          toList_empty, List.map_nil, List.nil_append, List.mem_singleton] using hb
      subst bin
      simpa only [RawNoiseSplitRegression.request, PolynomialBudgetHistory.request,
        gridChannel, rate, pow_zero, inv_one, one_pow, Nat.cast_ofNat] using he m hm)
  simpa only [show (RawNoiseSplitRegression.data HP).bins = ∅ from rfl,
    show (RawNoiseSplitRegression.data HP).padding = 1 from rfl,
    show (5 : ℕ) = 5 from rfl, Nat.cast_ofNat,
    image_empty, insert_empty_eq, sum_singleton, card_empty, Nat.cast_zero, zero_add,
    one_pow, mul_one, RawNoiseSplitRegression.scale,
    show (RawNoiseSplitRegression.data HP).slack = 1 from rfl,
    show LogSpaceEstimation.lastBudget 64 1 1 0 = 63 from rfl,
    show LogSpaceEstimation.lastBudget 64 (2 * 1) 1 0 = 62 from rfl,
    show ¬(63 : ℕ) = 0 from by decide, show ¬(62 : ℕ) = 0 from by decide, ↓reduceIte] using h

-- The actual full-terminal decoder uses the exact split and the new centered
-- moment-to-budget bridge on production H4 graphs. The allowance is explicitly
-- unpaid; this is a consumer of the actual moment, not a mean-error hypothesis.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (F : Environment 5 3 → ℝ)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (hG : ∀ x y, 0 ≤ G x y) (cost : ℕ → ℝ)
    (hc : ∀ i ∈ range 7,
      rowNormPow 4 5 1 (retainedMask 0 (side 5 0) (1 : ZMod 5) [1])
        (retainedMask 2 (side 5 0) (1 : ZMod 5) [2, 3])
        (fun σ x y => ((RawNoiseSplitRegression.data HP).residualTransportedGroupInput
          (RawNoiseSplitRegression.history F) 64 (dyadicSlack 7 i)
          (RawNoiseSplitRegression.request HP) σ x y - rowSliceMean
            (retainedMask 0 (side 5 0) (1 : ZMod 5) [1])
            (retainedMask 2 (side 5 0) (1 : ZMod 5) [2, 3])
            ((RawNoiseSplitRegression.data HP).residualTransportedGroupInput
              (RawNoiseSplitRegression.history F) 64 (dyadicSlack 7 i)
              (RawNoiseSplitRegression.request HP)) x y) / (rate 0 + G x y)) ≤ cost i) :
    let B := RawNoiseSplitRegression.data HP
    let r := RawNoiseSplitRegression.request HP
    rowNormPow 4 5 r.source.rate
      (retainedMask 0 (side 5 0) B.padding [1])
      (retainedMask 2 (side 5 0) B.padding [2, 3])
      (actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0) B.padding [1] [2, 3] 0 G
        (firstSignalIncrement (B.rawFirstPrefixes (RawNoiseSplitRegression.history F)
          64 .residual r) 0 (fun _ _ _ _ => 0)) 0 0 6) ≤
      8 * (B.rawRelativeNoiseBudget 64 r 0 2 (by decide) 0 0 [1] [2, 3]
        (fun i => B.residualSemanticGroupInput 64 (dyadicSlack 7 i) r) G 7 +
        (7 : ℝ) ^ 3 * ∑ i ∈ range 7,
          ‖fun xy : ZMod 5 × ZMod 5 => 2 *
            (graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0) (side_le 5 0) (side_le 5 0)
              (CopyPadding.identifier B.padding [1]) (CopyPadding.identifier B.padding [2, 3])
              xy.1 xy.2).spectralExpansion ^
                (2 * B.steps 64 r (dyadicSlack 7 i))‖ * cost i) := by
  dsimp only
  let B := RawNoiseSplitRegression.data HP
  let r := RawNoiseSplitRegression.request HP
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
  apply B.rawRelativeNoiseBudget_le_of_centered_fourth
    64 r 0 2 (by decide) 0 0 [1] [2, 3] rfl _ G 7 cost
  intro i hi
  simpa only [r, show B.padding = 1 from rfl,
    show Nat.log2 64 + 1 = 7 from rfl, RawNoiseSplitRegression.request,
    PolynomialBudgetHistory.request, gridChannel, rate, pow_zero, inv_one,
    one_pow, Nat.cast_ofNat] using hc i hi

end EndpointNoiseRegression
