/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of relative literal endpoint noise)
import Complexity.Foundations.Probability.HierarchyRelativeNoise
import all ComplexityTests.HierarchyNoiseAllocation
import all ComplexityTests.HierarchyFineDirect

/-!
Relative endpoint obligations feed the actual decoder statistic on its original
production walks. The supplied genuine-reference history may have nonconstant,
nonzero error, but no recursively accurate or jointly available IH is claimed.
The pairwise-range example shows why a reciprocal norm need not be separated.
Execution fixtures adapt Samuel Schlesinger's whole-environment tests.
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
namespace RelativeNoiseRegression

-- Own usage depends on the same environment as the nonzero error. Off-diagonal
-- denominators can be arbitrarily small, since both tables are zero there.
example (δ : ℝ) :
    let A := fun (σ x y : Bool) => if x = y ∧ y = σ then (1 : ℝ) else 0
    let U := fun (σ y : Bool) => y = σ
    let den := fun (x y : Bool) => if x = y then (1 : ℝ) else δ
    rowNormPow 4 2 1 (fun (_ x : Bool) => x = false) (fun _ _ => True)
      (fun σ x y => A σ x y / den x y) ≤
      256 * rootDistPow 4 2 1 (fun (_ x : Bool) => x = false) U A 0 := by
  dsimp only
  have h := rowNormPow_relative_sub_le_rootDistPow (N := (2 : ℝ)) (u := 1)
    (K := 4) (by norm_num) (fun (_ x : Bool) => x = false) (fun _ _ => True)
    (fun (σ y : Bool) => y = σ)
    (fun (σ x y : Bool) => if x = y ∧ y = σ then (1 : ℝ) else 0) 0 (fun _ => 1)
    (fun (x y : Bool) => if x = y then (1 : ℝ) else δ)
    (fun (x y : Bool) => if x = y then (1 : ℝ) else 0)
    (by intro σ x y; cases σ <;> cases x <;> cases y <;> norm_num)
    (by intro σ x y; by_cases h : x = y <;> simp [h])
    (by intro σ x y h; simp [h])
    (by intro x y; by_cases h : x = y <;> simp [h])
  norm_num only [Pi.zero_apply, sub_zero, one_mul, Nat.reducePow] at h
  exact h

-- This SAME own-mask error has a nonzero centered input.
example :
    let A := fun (σ x y : Bool) => if x = y ∧ y = σ then (1 : ℝ) else 0
    (fun σ x y => A σ x y - rowSliceMean
      (fun (_ x : Bool) => x = false) (fun _ _ => True) A x y) ≠ 0 := by
  dsimp only
  intro h
  have h₀ := congrFun (congrFun (congrFun h false) false) false
  have h₁ := congrFun (congrFun (congrFun h true) false) false
  norm_num only [Bool.false_eq_true, and_self, true_and, ↓reduceIte, Pi.zero_apply] at h₀ h₁
  linarith

-- A nonconstant product error and a nonzero reset-right error share one seed.
-- Their normalization rates differ; the exact reset/source factor is two.
example :
    let L := fun (σ : Bool) (_ _ : Unit) => if σ then (1 : ℝ) else 0
    rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True) L ≤
      256 * (16384 *
        (rootDistPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True) L 0 +
          2 * rootDistPow 4 1 2 (fun (_ : Bool) (_ : Unit) => True)
            (fun _ _ => True) 1 0)) := by
  dsimp only
  have h := rowNormPow_relative_product_sub_le_root
    (N := (1 : ℝ)) (u := 1) (f := 2) (CA := 1) (CB := 1) (K := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => True)
    (fun (σ : Bool) (_ _ : Unit) => if σ then (1 : ℝ) else 0) 0 1 0
    (fun _ => 1) (fun _ _ => 1) (fun _ _ => 1) 1 1
    (by intro σ x z; cases σ <;> norm_num)
    (by intros; norm_num)
    (by intros; norm_num)
    (by intros; norm_num)
    (by intro σ x y; cases σ <;> norm_num)
    (by intros; simp)
    (by intros; simp)
    (by intros; contradiction)
    (by intros; norm_num)
  norm_num only [Finset.filter_true, Finset.univ_unique, Finset.sum_singleton, Pi.one_apply,
    Pi.zero_apply, mul_one, mul_zero, sub_zero, div_one, Nat.reducePow,
    Nat.cast_one, one_mul] at h
  exact h

-- Charge first, then an unbounded listed-bin family under one admissible
-- all-bin/source/terminal horizon and eventually positive parent precision.
-- At d=M the literal relative root sum is zero, including nonzero allowances.
-- This tests exhaustion; it is not a positive-endpoint precision payment.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℝ) (n ks ka : ℕ) :
    ∃ (P : ℕ) (hP : P.Prime),
      let : Fact P.Prime := ⟨hP⟩
      ∃ (H : Horizon P) (D : BudgetData HP P)
        (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
        D.rankCharge = A ∧ D.bins = range (n + 1) ∧
        max n (max ks ka) ≤ H.maxExponent ∧
        Admissible q ∧ q.usage = q.terminal ∧
        ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < D.requestPrecision M q ∧
          D.residualEndpointRootSum M M q (fun _ _ => 1) = 0 := by
  obtain ⟨P, hP, _, _, H, hH, _⟩ :=
    exists_bounded_depth_prime (max n (max ks ka) + 1) 0 (by positivity)
  let : Fact P.Prime := ⟨hP⟩
  let D : BudgetData HP P :=
    {ProductAllocationRegression.data HP P 0 n with rankCharge := A}
  let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.residual 0, gridChannel 0 ks [1], gridChannel 2 ka [2, 3],
      gridChannel 2 ka [2, 3]⟩
  refine ⟨P, hP, H, D, q, rfl, rfl, ?_, ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩, rfl, ?_⟩
  · rw [hH]; omega
  · obtain ⟨M₀, hM⟩ := D.grid_precision_eventually_pos ks ka q rfl rfl
    exact ⟨M₀, fun M h => ⟨hM M h,
      D.residualEndpointRootSum_eq_zero_of_le M M q _ le_rfl⟩⟩

-- Complete actual-noise consumer, retaining semantic payment separately.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (F : Environment 5 3 → ℝ)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (hG : ∀ x y, 0 ≤ G x y) (e : ℕ → ℕ → Option ℕ → ℝ)
    (he0 : ∀ i m bin, 0 ≤ e i m bin)
    (he : ∀ i ∈ range 7, ∀ bin ∈ (RawNoiseSplitRegression.data HP).rays .residual,
      ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget 64 (dyadicSlack 7 i)
        (RawNoiseSplitRegression.data HP).slack
        ((RawNoiseSplitRegression.data HP).sampleScale (RawNoiseSplitRegression.request HP) bin) ∨
      m = LogSpaceEstimation.lastBudget 64 (2 * dyadicSlack 7 i)
        (RawNoiseSplitRegression.data HP).slack
        ((RawNoiseSplitRegression.data HP).sampleScale (RawNoiseSplitRegression.request HP) bin)) →
      rowNormPow 4 5 1 (retainedMask 0 (side 5 0) (1 : ZMod 5) [1])
        (retainedMask 2 (side 5 0) (1 : ZMod 5) [2, 3])
        (fun σ x y => (((RawNoiseSplitRegression.data HP).sample
          (RawNoiseSplitRegression.history F) m .residual
          (RawNoiseSplitRegression.request HP)
            bin).getD 0 σ x y - (RawNoiseSplitRegression.data HP).residualCanonicalRay
              (RawNoiseSplitRegression.request HP) bin σ x y) / (rate 0 + G x y)) ≤
          e i m bin ^ 4) :
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
                (2 * B.steps 64 r (dyadicSlack 7 i))‖ *
                  (16 * B.residualEndpointRootSum 64 (dyadicSlack 7 i) r (e i) ^ 4)) := by
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
  apply B.rawRelativeNoiseBudget_transported_le_of_relative_endpoints
    (RawNoiseSplitRegression.history F) 64 r 0 2 (by decide) 0 0 [1] [2, 3] rfl G 7 e he0
  intro i hi bin hb m hm hmc
  simpa only [r, show B.padding = 1 from rfl, RawNoiseSplitRegression.request,
    PolynomialBudgetHistory.request, gridChannel, rate, pow_zero, inv_one,
    one_pow, Nat.cast_ofNat] using he i hi bin hb m hm hmc

end RelativeNoiseRegression
