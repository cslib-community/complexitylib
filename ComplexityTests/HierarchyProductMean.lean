/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of actual finite hierarchy product means)
import Complexity.Foundations.Probability.HierarchyProductMean
import all ComplexityTests.PolynomialBudgetHistory
import all ComplexityTests.HierarchySignedMean

/-! A genuine nonzero correction and two actual bounded polynomial bins. The canonical
history supplied below executes finiteInput; it does not assert recursive compressed
availability. The conditional consumer retains that separate premise and scalar child IH.
The existing unequal-rate correlated signed-mean client is imported as a relevant client. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace ProductMeanRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private def data := PolynomialBudgetHistory.data HP
private def request : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  {PolynomialBudgetHistory.request HP with source := gridChannel 0 1 [1], task := .residual 0}
private def E : Matrix (ZMod 5) (ZMod 5) ℝ :=
  HP.toHierarchyParams.correctionIter (canonicalChannel id (rate 0))
    (canonicalChannel id (rate 0)) (rate 0) (data HP).base HP.k
private lemma nonneg (x y : ZMod 5) : 0 ≤ (data HP).base x y :=
  by
    change 0 ≤ (1 : Matrix (ZMod 5) (ZMod 5) ℝ) x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
private lemma mass : (data HP).base *ᵥ 1 ≤ 1 := by
  simp only [data, PolynomialBudgetHistory.data, PolynomialBudgetHistory.base, one_mulVec]
  exact le_rfl
private lemma stage_bound (x y : ZMod 5) : (data HP).base x y ≤ rate 0 := by
  by_cases h : x = y
  · subst y; norm_num [data, PolynomialBudgetHistory.data, PolynomialBudgetHistory.base, rate]
  · norm_num [data, PolynomialBudgetHistory.data, PolynomialBudgetHistory.base,
      Matrix.one_apply_ne h, rate]
private lemma cover (y z : ZMod 5) : (data HP).base z y = 0 ∨ rate 1 ≤ (data HP).base z y := by
  by_cases h : z = y
  · subst y; right
    norm_num [data, PolynomialBudgetHistory.data, PolynomialBudgetHistory.base, rate]
  · left
    exact Matrix.one_apply_ne h
private lemma actual_mean (x y : ZMod 5) :
    rowSliceMean
      (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
      ((data HP).residualCanonicalInput (request HP)) x y = (data HP).base x y := by
  have hm := (data HP).residualCanonicalInput_mean 1
    (by ext i; simp [data, PolynomialBudgetHistory.data]; omega) rfl rfl rfl
    (by change (1 : ZMod 5) ≠ 0; norm_num)
    SourceRegression.horizon (by decide) (request HP) 0 2 (by decide) 1 0 [1] [2, 3]
    rfl rfl (by decide) (by decide) (nonneg HP) (mass HP) (stage_bound HP) x y (cover HP y)
  rw [HierarchyParams.residual_eq] at hm
  simpa only [data, PolynomialBudgetHistory.data, PolynomialBudgetHistory.base,
    Matrix.mul_one, Matrix.add_apply, Matrix.sub_apply, sub_add_cancel] using hm

-- The genuine final correction is positive, so the product and once-negative terms matter.
private lemma detector_rank : 5 < HP.J := by
  have hk : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
  have hm : (1 : ℝ) ≤ HP.m := by
    have hc := HP.copies_strict
    nlinarith
  have hp : 1 ≤ (HP.m : ℝ) * HP.k * ((HP.k : ℝ) + 1) := by
    calc
      1 = (1 : ℝ) * 1 * 1 := by norm_num
      _ ≤ (HP.m : ℝ) * HP.k * ((HP.k : ℝ) + 1) := by gcongr; linarith
  have hd : HP.δ₀ < 1 := by
    linarith [HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂, HP.θ₂_lt]
  by_contra hh
  have hj : (HP.J : ℝ) ≤ 5 := by exact_mod_cast (not_lt.mp hh)
  have hr := HP.rank
  norm_num at hr
  nlinarith [mul_le_mul_of_nonneg_left hj HP.δ₀_pos.le]
private lemma correction_pos (x : ZMod 5) : 0 < E HP x x := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt HP.k_pos)
  unfold E
  rw [hj, HP.toHierarchyParams.correctionIter_succ_apply]
  have hm := PilotTask.value_maximum_eq_zero HP.toHierarchyParams
    (canonicalChannel id (rate 0)) (canonicalChannel id (rate 0)) (rate 0) (data HP).base
    (by simpa only [ZMod.card] using detector_rank HP) HP.k
  erw [PilotTask.value_maximum_last] at hm
  rw [hm]
  simp only [Pi.zero_apply, HP.γ_one 0 (by norm_num), mul_one]
  have hn := (HP.toHierarchyParams.isCorrectionSeq_correctionIter
    (X := canonicalChannel id (rate 0)) (Y := canonicalChannel id (rate 0))
    (rate_pos 0) (nonneg HP)).nonneg j x x
  have hi : 1 ≤ HP.toHierarchyParams.correctionInput
      (canonicalChannel id (rate 0)) (canonicalChannel id (rate 0)) (rate 0)
      (data HP).base j x x / rate 0 := by
    change 1 ≤ ((data HP).base x x +
      ((HP.toHierarchyParams.correctionIter (canonicalChannel id (rate 0))
        (canonicalChannel id (rate 0)) (rate 0) (data HP).base j) * (data HP).base) x x) / rate 0
    rw [show (data HP).base x x = 1 from Matrix.one_apply_eq x]
    rw [show rate 0 = 1 by norm_num [rate], div_one]
    simpa only [data, PolynomialBudgetHistory.data, PolynomialBudgetHistory.base,
      Matrix.mul_one, le_add_iff_nonneg_right,
      show rate 0 = 1 by norm_num [rate]] using hn
  exact mul_pos (rate_pos 0) ((CutoffRegression.Q_one_pos HP).trans_le (HP.Q_mono hi))

-- The actual hierarchy product E*C is nonzero, with the same finite base as the mean client.
example (x : ZMod 5) : 0 < ∑ z, E HP x z * (data HP).base z x := by
  change 0 < (E HP * (1 : Matrix (ZMod 5) (ZMod 5) ℝ)) x x
  rw [Matrix.mul_one]
  exact correction_pos HP x

private def negative (σ : Environment 5 3) (x y : ZMod 5) : ℝ :=
  HierarchyTask.rawNegativeSample (channels (data HP).padding) 0 0 .residual
    (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
    ((data HP).binRate 0) (fun q => (data HP).residualCanonicalChild 0 q σ) x y
private lemma negative_mean (x y : ZMod 5) :
    rowSliceMean
      (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
      (negative HP) x y = E HP x y := by
  have hm := canonical_rawNegativeSample_mean HP (1 : ZMod 5) id (by norm_num)
    Function.injective_id SourceRegression.horizon threeRoles 0 0 1 0 0 0
    (by decide) (by decide) [1] [] [2, 3] (data HP).base
    (nonneg HP) (mass HP) (stage_bound HP) ((data HP).cutoff 0)
    ((data HP).auxiliary 0) HP.ρ HP.K x y
  simpa [rowSliceMean, negative, BudgetData.residualCanonicalChild, request,
    PolynomialBudgetHistory.request, BudgetData.midpoint, BudgetData.midpointRole,
    threeRoles, gridChannel, data, PolynomialBudgetHistory.data, E, id_eq] using hm

-- Both signed endpoints are nonzero; two positives minus one negative have mean one.
example (x : ZMod 5) :
    0 < rowSliceMean
      (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
      (negative HP) x x ∧
    rowSliceMean
      (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
      ((data HP).residualCanonicalInput (request HP)) x x = 1 := by
  rw [negative_mean HP, actual_mean HP]
  exact ⟨correction_pos HP x, Matrix.one_apply_eq x⟩

-- The actual sum of positive endpoints has mean 1+E; the single negative has mean E.
example (x : ZMod 5) :
    rowSliceMean
      (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
      (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
      (fun σ x y => ∑ i ∈ (data HP).bins,
        HierarchyTask.rawPositiveSample (channels (data HP).padding) 0 i .residual
          (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
          ((data HP).binRate i) (fun q => (data HP).residualCanonicalChild i q σ) x y)
      x x = 1 + E HP x x := by
  have hm := actual_mean HP x x
  have hn := negative_mean HP x x
  simp only [BudgetData.residualCanonicalInput, rowSliceMean, expect_sub_distrib] at hm
  change (𝔼 σ ∈ _, _) = _ at hn ⊢
  simp only [negative] at hn
  rw [hn] at hm
  have hb : (data HP).base x x = 1 := Matrix.one_apply_eq x
  linarith only [hm, hb]

private def history (_M : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :
    Option (BudgetValue 5) :=
  some (.row ((data HP).residualCanonicalChild
    (match q.task with | .baseNormalized _ i => i | _ => 0) q))

-- Genuine canonical requests execute a supplied finite history with the actual budgets.
-- This is not successful recursive compressed evaluation of the final correction.
example (M : ℕ) :
    ∃ A, (data HP).finiteInput (history HP) M .residual (request HP) = some A ∧
      ∀ x y, rowSliceMean
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
        A x y = (data HP).base x y := by
  refine ⟨_, (data HP).finiteInput_residual_of_rows (history HP) M (request HP)
    (data HP).residualCanonicalChild ?_ ?_, actual_mean HP⟩
  · intro i _ q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    all_goals
      simp only [BudgetData.row, history, HierarchyTask.rawRequests,
        HierarchyTask.correctionAtomTask_last HP.k_pos, Option.bind_some, BudgetValue.row?]
    all_goals rfl
  · dsimp only
    simp only [BudgetData.row, history, HierarchyTask.correctionAtomTask_last HP.k_pos,
      Option.bind_some, BudgetValue.row?]

-- Reset source and suffix differ, while both child budgets strictly decrease.
example (M : ℕ) (hM : 0 < M) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 0 .residual
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal (rate 0)
    Q.right.source.rate = rate 0 ∧ Q.direct.source.rate = rate 1 ∧
      Q.right.source.suffix = [] ∧ Q.direct.source.suffix = [1] ∧
      (data HP).binBudget M 0 (request HP) < M ∧ (data HP).childBudget M < M :=
  ⟨rfl, rfl, rfl, rfl, (data HP).binBudget_lt hM 0 _, (data HP).childBudget_lt hM⟩

-- Source and reset-source events have different actual densities on one shared environment.
example (x : ZMod 5) :
    (dens {σ : Environment 5 3 | (request HP).source.retains (channels (1 : ZMod 5)) σ x}
      : ℝ) = 81 / 625 ∧
    (dens {σ : Environment 5 3 |
      (BudgetData.midpoint (request HP)).retains (channels (1 : ZMod 5)) σ x} : ℝ) = 1 := by
  rw [channel_density 1 (request HP).source 1 rfl,
    channel_density 1 (BudgetData.midpoint (request HP)) 0 rfl]
  norm_num [side, Nat.ceilDiv_eq_add_pred_div]

-- Zero entries are included in the coverage condition and have exact zero signed mean.
example : rowSliceMean
    (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
    (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
    ((data HP).residualCanonicalInput (request HP)) 0 1 = 0 := by
  rw [actual_mean HP]
  exact Matrix.one_apply_ne (by decide)

end ProductMeanRegression
