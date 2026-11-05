/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of terminal transport for actual residual products)
import Complexity.Foundations.Probability.HierarchyTerminalMean
import all ComplexityTests.HierarchyProductMean
import all ComplexityTests.HierarchyProductAllocation

/-! Correlated factors use the parent's original endpoint x and the reset-right original
y; no independent estimated rows are substituted. The midpoint and usage densities differ
and are nontrivial. The genuine finite hierarchy/positive correction/product clients are
retained. Supplied canonical rows execute a signed finite hierarchy, not recursive compression.
No uniform fixed-charge precision allocation is claimed by these tests. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace TerminalMeanRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private def data := ProductMeanRegression.data HP
private def request : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  ⟨.residual 0, gridChannel 0 2 [1], gridChannel 2 1 [2, 3], gridChannel 2 1 [2, 3]⟩
private def Q := HierarchyTask.rawRequests (k := HP.k) 0 2 .residual
  (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal (rate 2)
private def left (σ : Environment 5 3) (x z : ZMod 5) : ℝ :=
  if (BudgetData.midpoint (request HP)).retains (channels (1 : ZMod 5)) σ z then
    if (request HP).terminal.retains (channels (1 : ZMod 5)) σ x then 3 else 1
  else 0
private def right (σ : Environment 5 3) (z y : ZMod 5) : ℝ :=
  if (Q HP).right.usage.retains (channels (1 : ZMod 5)) σ y then
    if (request HP).source.retains (channels (1 : ZMod 5)) σ y ∧
      (request HP).terminal.retains (channels (1 : ZMod 5)) σ z then 2 else 1
  else 0

-- Literal bin importance and midpoint normalization are both present in this mean.
example (x y : ZMod 5) :
    (data HP).residualProductMean 2 (request HP) (left HP) (right HP) x y =
      (625 / 331776 : ℝ) * conditionalTableMean
        (fun σ x => (request HP).source.retains (channels (1 : ZMod 5)) σ x)
        (fun σ y => (Q HP).right.usage.retains (channels (1 : ZMod 5)) σ y)
        (fun σ x y => ∑ z, left HP σ x z * right HP σ z y) x y := by
  have h := (data HP).residualProduct_parent_mean 2 1 (request HP)
    (by change (0 : Fin 3) ≠ 2; decide) rfl rfl
    (left HP) (right HP) (by
      dsimp only
      intro σ z y hy
      change ¬ (Q HP).right.usage.retains (channels (1 : ZMod 5)) σ y at hy
      simp only [right, hy, ↓reduceIte]) x y
  change (data HP).residualProductMean 2 (request HP) (left HP) (right HP) x y = _ at h
  convert h using 1
  norm_num [Q, request, data, ProductMeanRegression.data, PolynomialBudgetHistory.data,
    gridChannel, rate, gridMass, side, Nat.ceilDiv_eq_add_pred_div]

-- The reset source is the complete midpoint tuple, while the left keeps [1].
example (x : ZMod 5) :
    (Q HP).left.source.suffix = [1] ∧ (Q HP).right.source.suffix = [] ∧
    (dens {σ : Environment 5 3 |
      (request HP).source.retains (channels (1 : ZMod 5)) σ x} : ℝ) = 16 / 625 ∧
    (dens {σ : Environment 5 3 |
      (BudgetData.midpoint (request HP)).retains (channels (1 : ZMod 5)) σ x} : ℝ) =
      81 / 625 ∧
    (dens {σ : Environment 5 3 |
      (Q HP).right.usage.retains (channels (1 : ZMod 5)) σ x} : ℝ) = 16 / 625 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · rw [channel_density 1 (request HP).source 2 rfl]
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]
  · rw [channel_density 1 (BudgetData.midpoint (request HP)) 1 rfl]
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]
  · rw [channel_density 1 (Q HP).right.usage 2 (by norm_num [Q, request,
      HierarchyTask.rawRequests, gridChannel, rate])]
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]

-- Exact linear root coefficient differs from the fourth-power ordinary coefficient.
example :
    (rate 2 * (rate 1 / gridMass 5 1)) * (gridMass 5 1 / gridMass 5 2) =
      (625 / 65536 : ℝ) ∧
    (rate 2 * (rate 1 / gridMass 5 1)) ^ 4 * (gridMass 5 1 / gridMass 5 2) =
      (625 / 331776 : ℝ) ^ 4 * (81 / 16) := by
  norm_num [rate, gridMass, side, Nat.ceilDiv_eq_add_pred_div]

-- Zero tables have exactly zero transported mean; empty/error-free boundaries are retained.
example : (data HP).residualProductMean 2 (request HP) 0 0 = 0 := by
  funext x y
  simp [BudgetData.residualProductMean, conditionalTableMean]

-- The genuine final correction and product remain positive in the finite hierarchy.
example (x : ZMod 5) :
    0 < ProductMeanRegression.E HP x x ∧
    0 < ∑ z, ProductMeanRegression.E HP x z * (data HP).base z x := by
  constructor
  · exact ProductMeanRegression.correction_pos HP x
  · change 0 < (ProductMeanRegression.E HP * (1 : Matrix (ZMod 5) (ZMod 5) ℝ)) x x
    rw [Matrix.mul_one]
    exact ProductMeanRegression.correction_pos HP x

-- A genuine finite hierarchy at nontrivial midpoint density, with unequal source rate.
private def smallData : BudgetData HP 5 :=
  {data HP with base := rate 1 • (1 : Matrix (ZMod 5) (ZMod 5) ℝ)}
private def smallE : Matrix (ZMod 5) (ZMod 5) ℝ :=
  HP.toHierarchyParams.correctionIter (canonicalChannel id (rate 1))
    (canonicalChannel id (rate 1)) (rate 1) (smallData HP).base HP.k
private lemma small_nonneg (x y : ZMod 5) : 0 ≤ (smallData HP).base x y := by
  change 0 ≤ rate 1 * (1 : Matrix (ZMod 5) (ZMod 5) ℝ) x y
  exact mul_nonneg (rate_pos 1).le (by by_cases h : x = y <;> simp [Matrix.one_apply, h])
private lemma small_mass : (smallData HP).base *ᵥ 1 ≤ 1 := by
  intro x
  simp only [smallData, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
    mul_one]
  norm_num [rate]
private lemma small_stage (x y : ZMod 5) : (smallData HP).base x y ≤ rate 1 := by
  change rate 1 * (1 : Matrix (ZMod 5) (ZMod 5) ℝ) x y ≤ rate 1
  by_cases h : x = y <;> simp [Matrix.one_apply, h, (rate_pos 1).le]
private lemma small_correction_pos (x : ZMod 5) : 0 < smallE HP x x := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt HP.k_pos)
  unfold smallE
  rw [hj, HP.toHierarchyParams.correctionIter_succ_apply]
  have hm := PilotTask.value_maximum_eq_zero HP.toHierarchyParams
    (canonicalChannel id (rate 1)) (canonicalChannel id (rate 1)) (rate 1)
    (smallData HP).base (by simpa only [ZMod.card] using ProductMeanRegression.detector_rank HP)
    HP.k
  erw [PilotTask.value_maximum_last] at hm
  rw [hm]
  simp only [Pi.zero_apply, HP.γ_one 0 (by norm_num), mul_one]
  have hn := (HP.toHierarchyParams.isCorrectionSeq_correctionIter
    (X := canonicalChannel id (rate 1)) (Y := canonicalChannel id (rate 1))
    (rate_pos 1) (small_nonneg HP)).nonneg j x x
  have hinput : 1 ≤ HP.toHierarchyParams.correctionInput
      (canonicalChannel id (rate 1)) (canonicalChannel id (rate 1)) (rate 1)
      (smallData HP).base j x x / rate 1 := by
    rw [one_le_div (rate_pos 1)]
    change rate 1 ≤ ((smallData HP).base +
      HP.toHierarchyParams.correctionIter (canonicalChannel id (rate 1))
        (canonicalChannel id (rate 1)) (rate 1) (smallData HP).base j * (smallData HP).base) x x
    simp only [smallData, Matrix.mul_smul, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact le_add_of_nonneg_right (mul_nonneg (rate_pos 1).le hn)
  exact mul_pos (rate_pos 1) ((CutoffRegression.Q_one_pos HP).trans_le (HP.Q_mono hinput))

example (x : ZMod 5) :
    0 < smallE HP x x ∧ 0 < ∑ z, smallE HP x z * (smallData HP).base z x ∧
    rowSliceMean
      (fun σ x => (request HP).source.retains (channels (smallData HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (smallData HP).padding) σ y)
      ((smallData HP).residualCanonicalInput (request HP)) x x =
        rate 1 + rate 1 * smallE HP x x - smallE HP x x := by
  have hmean := (smallData HP).residualCanonicalInput_mean 1
    (by ext i; simp [smallData, data, ProductMeanRegression.data,
      PolynomialBudgetHistory.data]; omega) rfl rfl rfl (by norm_num [smallData, data,
        ProductMeanRegression.data, PolynomialBudgetHistory.data])
    SourceRegression.horizon (by decide) (request HP) 0 2 (by decide) 2 1 [1] [2, 3]
    rfl rfl (by decide) (by decide) (small_nonneg HP) (small_mass HP) (small_stage HP) x x
    (by intro z; by_cases h : z = x
        · subst z; right; simp [smallData]
        · left; simp [smallData, Matrix.one_apply_ne h])
  rw [HierarchyParams.residual_eq, ← HierarchyParams.correctionIter_last] at hmean
  have hp : 0 < ∑ z, smallE HP x z * (smallData HP).base z x := by
    change 0 < (smallE HP * (rate 1 • (1 : Matrix (ZMod 5) (ZMod 5) ℝ))) x x
    rw [Matrix.mul_smul, Matrix.mul_one]
    exact mul_pos (rate_pos 1) (small_correction_pos HP x)
  refine ⟨small_correction_pos HP x, hp, ?_⟩
  change _ = (smallData HP).base x x - smallE HP x x +
    (smallE HP * (smallData HP).base) x x at hmean
  have hscale : (smallE HP * (smallData HP).base) x x = rate 1 * smallE HP x x := by
    simp only [smallData, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]
  rw [hscale] at hmean
  -- Retain the genuine C + EC - E target at the non-unit scale.
  have hbase : (smallData HP).base x x = rate 1 := by
    simp only [smallData, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rw [hbase] at hmean
  linarith only [hmean]

-- Signed finite Minkowski is consumed by an actually executed supplied canonical history.
-- Its bin budgets and once-negative budget remain distinct in the program.
example (M : ℕ) :
    ∃ A, (data HP).finiteInput (ProductMeanRegression.history HP) M .residual
      (ProductMeanRegression.request HP) = some A ∧
      rowNormPow 4 5 (ProductMeanRegression.request HP).source.rate
        (fun σ x => (ProductMeanRegression.request HP).source.retains
          (channels (data HP).padding) σ x)
        (fun σ y => (ProductMeanRegression.request HP).terminal.retains
          (channels (data HP).padding) σ y)
        (fun _ x y => rowSliceMean
          (fun σ x => (ProductMeanRegression.request HP).source.retains
            (channels (data HP).padding) σ x)
          (fun σ y => (ProductMeanRegression.request HP).terminal.retains
            (channels (data HP).padding) σ y)
          (fun σ x y => A σ x y - (data HP).residualCanonicalInput
            (ProductMeanRegression.request HP) σ x y) x y) ≤ 0 := by
  have h := (data HP).finiteInput_residual_mean_minkowski (ProductMeanRegression.history HP)
    M (ProductMeanRegression.request HP) (rate_pos 1).le
    (data HP).residualCanonicalChild ?_ ?_ (fun _ => 0) (fun _ => le_rfl) ?_ ?_
  · simpa only [sum_const_zero, add_zero, zero_pow (by decide : 4 ≠ 0),
      Nat.cast_ofNat] using h
  · intro i _ q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    all_goals
      simp only [BudgetData.row, ProductMeanRegression.history, HierarchyTask.rawRequests,
        HierarchyTask.correctionAtomTask_last HP.k_pos, Option.bind_some, BudgetValue.row?]
    all_goals rfl
  · dsimp only
    simp only [BudgetData.row, ProductMeanRegression.history,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Option.bind_some, BudgetValue.row?]
    rfl
  · intro i _
    simp [rowSliceMean, rowNormPow]
  · simp [rowSliceMean, rowNormPow]
end TerminalMeanRegression
