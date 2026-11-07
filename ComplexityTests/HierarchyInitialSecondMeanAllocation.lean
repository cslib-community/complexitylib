/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests of actual second-mean allocation)

import Complexity.Foundations.Probability.HierarchyInitialSecondMeanAllocation
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import all ComplexityTests.PolynomialBudgetHistory

/-! A charge chosen after the fixed preparation constants serves every growing budget.
The field/horizon assumptions are realized and the omitted canonical mass is positive. -/

set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment PolynomialBudgetHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

-- The fixed charge serves actual admissible prime grids at every growing budget.
-- Nonzero omitted mass remains, so the semantic payment is not a zero-error fixture.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (coefficient ζ Lh Lρ floor cap C Cpre : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ k : ℕ, ∃ P, ∃ _ : Fact P.Prime, ∃ H : Horizon P,
      let M := 16 * (k + A * 36 + 1)
      let B : BudgetData HP P := { uniformData HP P M with
        rankCharge := A, base := (rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ) }
      let r := uniformRequest HP P
      H.maxExponent = M ∧ (∀ bin ∈ B.bins, bin ≤ H.maxExponent) ∧
      0 < B.requestPrecision M r ∧
      0 < B.base 0 0 * (1 - polynomialSwitch4 (1 / 2) 1 (B.base 0 0 / rate M)) ∧
      B.initialComputedSecondMeanReserve M M r threeRoles 0 0 [1] [2, 3]
        coefficient ζ Lh Lρ floor cap C Cpre ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  obtain ⟨A, hA1, hA⟩ := BudgetData.initialComputedSecondMeanReserve_exists_charge
    HP 16 coefficient ζ Lh Lρ floor cap C Cpre hf
  refine ⟨A, hA1, ?_⟩
  intro k
  let M := 16 * (k + A * 36 + 1)
  obtain ⟨P, hprime, _, _, H, he, _⟩ := exists_bounded_depth_prime M 0 (by positivity)
  let : Fact P.Prime := ⟨hprime⟩
  let B : BudgetData HP P := { uniformData HP P M with
    rankCharge := A, base := (rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ) }
  let r := uniformRequest HP P
  have hp : 0 < B.requestPrecision M r := by
    rw [B.requestPrecision_grid M 0 0 r rfl rfl]
    norm_num [B, r, M, uniformData, uniformRequest, HierarchyTask.rank,
      BoundedRowTask.localTask, CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpos : 0 < B.base 0 0 *
      (1 - polynomialSwitch4 (1 / 2) 1 (B.base 0 0 / rate M)) := by
    have hv : B.base 0 0 = rate M / 4 := by simp [B]
    have he : (rate M / 4) / rate M = (1 / 4 : ℝ) := by field_simp [(rate_pos M).ne']
    rw [hv, he, polynomialSwitch4_of_le (by norm_num) (by norm_num)]
    simpa only [sub_zero, mul_one] using div_pos (rate_pos M) (by norm_num : (0 : ℝ) < 4)
  have hC (x y : ZMod P) : 0 ≤ B.base x y := by
    change 0 ≤ (rate M / 4) * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
    exact mul_nonneg (div_nonneg (rate_pos M).le (by norm_num))
      (by simp only [Matrix.one_apply]; split_ifs <;> norm_num)
  have hC1 : B.base *ᵥ 1 ≤ 1 := by
    intro x
    change (((rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ)) *ᵥ 1) x ≤ 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hr : rate M ≤ 1 := by simpa [rate] using rate_antitone (Nat.zero_le M)
    simpa only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] using
      (by linarith : rate M / 4 ≤ (1 : ℝ))
  refine ⟨P, inferInstance, H, he, ?_, hp, hpos, ?_⟩
  · intro bin hb
    change bin ∈ range (M + 1) at hb
    rw [he]
    exact Nat.le_of_lt_succ (mem_range.mp hb)
  · exact hA B rfl rfl rfl rfl M M 0 0 rfl
      (by dsimp only [B, uniformData]; omega) H (by omega) (by omega) (by omega)
      r threeRoles [1] [2, 3] rfl rfl rfl hp hC hC1
