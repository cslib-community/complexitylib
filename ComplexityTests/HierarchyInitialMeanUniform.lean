/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of uniform true-mass first-mean payments)
import Complexity.Foundations.Probability.HierarchyInitialMeanUniform
import all ComplexityTests.PolynomialBudgetHistory

/-! Positive-precision identity-base families exercise the actual computed budgets.
The first family has retained scale cutoffs exceeding the budget. The second has terminal
exponent beyond half the retained depth. Neither needs an upper bound on field width. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open NormalizedMoments
open PolynomialBudgetHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix

-- Depth grows faster than budget, leaving many fine bins genuinely inactive.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P : ℕ) [Fact P.Prime] (H : Horizon P) (k : ℕ)
    (hn : 16 * (k + 257) ≤ H.maxExponent) :
    let M := 16 * (k + 257)
    let B : BudgetData HP P := { uniformData HP P M with
      rankCharge := 7, base := (rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ) }
    let r := uniformRequest HP P
    let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
    let S := 4 * (1 + 2 * B.binCap) * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge)
    let x := 2 * (K * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) + S)
    0 < B.requestPrecision M r ∧
      ¬ B.slack * (1 + 4 * (M + 0)) < M ∧
      0 < B.base 0 0 * (1 - polynomialSwitch4 (1 / 2) 1 (B.base 0 0 / rate M)) ∧
      B.initialComputedFirstFinalBudget M M r threeRoles 0 0 [1] [2, 3] 1 ≤
        (8 : ℝ) ^ (4⁻¹ : ℝ) * x := by
  dsimp only
  let M := 16 * (k + 257)
  let B : BudgetData HP P := { uniformData HP P M with
      rankCharge := 7, base := (rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ) }
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
  refine ⟨hp, by dsimp only [B, uniformData]; omega, hpos, ?_⟩
  have hbound := B.initialComputedFirstBudgets_uniform (by norm_num [B, uniformData])
    M M 0 0 rfl rfl rfl (by dsimp only [B, uniformData]; omega) H
    ((Nat.zero_le M).trans hn) ((Nat.zero_le M).trans hn) r
    (by norm_num [r, uniformRequest, HierarchyTask.rank, BoundedRowTask.localTask,
      CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]) rfl rfl hp
    (by intro x y
        change 0 ≤ (rate M / 4) * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
        exact mul_nonneg (div_nonneg (rate_pos M).le (by norm_num))
          (by simp only [Matrix.one_apply]; split_ifs <;> norm_num))
    (by intro x
        change (((rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ)) *ᵥ 1) x ≤ 1
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        have hr : rate M ≤ 1 := by simpa [rate] using rate_antitone (Nat.zero_le M)
        simpa only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] using
          (by linarith : rate M / 4 ≤ (1 : ℝ)))
    threeRoles [1] [2, 3] 1 1 1 (by norm_num)
  simpa only [abs_one, mul_one] using hbound.2.1

-- Activity allows terminal exponents approaching retained depth, rather than half-depth.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P : ℕ) [Fact P.Prime] (H : Horizon P) (k : ℕ) (hk : 0 < k)
    (hn : k + 400 ≤ H.maxExponent) (j : ℕ) :
    let n := k + 400
    let ka := k + 200
    let B : BudgetData HP P := { uniformData HP P n with rankCharge := 7 }
    let r := { uniformRequest HP P with terminal := gridChannel 2 ka [2, 3] }
    ¬ 2 * ka ≤ n ∧ 0 < B.requestPrecision (32 * n) r ∧
      rowNormPow 4 P r.source.rate
        (retainedMask threeRoles.source (side P 0) B.padding [1])
        (retainedMask threeRoles.terminal (side P ka) B.padding [2, 3])
        (fun _ x y => min 1 (|B.initialPolynomialLoss (32 * n) n j r x y| /
          (rate ka + B.base x y))) ^ (4⁻¹ : ℝ) ≤
        (4 * (1 + 2 * B.binCap) * (2 : ℝ) ^ (-B.requestPrecision (32 * n) r) *
          (2 : ℝ) ^ (-B.rankCharge)) * (2 : ℝ) ^ dyadicSlack (Nat.log2 (32 * n) + 1) j := by
  dsimp only
  let n := k + 400
  let ka := k + 200
  let B : BudgetData HP P := { uniformData HP P n with rankCharge := 7 }
  let r := { uniformRequest HP P with terminal := gridChannel 2 ka [2, 3] }
  have hp : 0 < B.requestPrecision (32 * n) r := by
    rw [B.requestPrecision_grid (32 * n) 0 ka r rfl rfl]
    norm_num [B, r, n, ka, uniformData, uniformRequest, HierarchyTask.rank,
      BoundedRowTask.localTask, CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]
    linarith
  refine ⟨by omega, hp, ?_⟩
  apply B.initialPolynomialLoss_root_uniform_le (by norm_num [B, uniformData])
    (32 * n) n j 0 ka rfl rfl rfl (by dsimp only [B, uniformData]; omega) H
    (Nat.zero_le _) (by dsimp only [ka, n] at *; omega) r
    (by norm_num [r, uniformRequest, HierarchyTask.rank, BoundedRowTask.localTask,
      CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]) rfl rfl hp
    (by intro x y; change 0 ≤ (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
        simp only [Matrix.one_apply]; split_ifs <;> norm_num)
    (by simp [B, uniformData]) threeRoles [1] [2, 3]

-- The fixed charge serves actual admissible prime grids at every growing budget.
-- Nonzero omitted mass remains, so the semantic payment is not a zero-error fixture.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (coefficient floor cap C Cpre : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ k : ℕ, ∃ P, ∃ _ : Fact P.Prime, ∃ H : Horizon P,
      let M := 16 * (k + A * 36 + 1)
      let B : BudgetData HP P := { uniformData HP P M with
        rankCharge := A, base := (rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ) }
      let r := uniformRequest HP P
      H.maxExponent = M ∧ (∀ bin ∈ B.bins, bin ≤ H.maxExponent) ∧
      0 < B.requestPrecision M r ∧
      0 < B.base 0 0 * (1 - polynomialSwitch4 (1 / 2) 1 (B.base 0 0 / rate M)) ∧
      ∀ ζ Lh Lρ : ℝ,
      B.initialComputedFirstCoordinateReserve M M r threeRoles 0 0 [1] [2, 3]
        coefficient ζ Lh Lρ floor cap C Cpre ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  obtain ⟨A, hA1, hA⟩ := BudgetData.initialComputedFirstCoordinateReserve_uniform_exists_charge
    HP 16 coefficient floor cap C Cpre hf
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
  · intro ζ Lh Lρ
    exact hA B rfl rfl rfl rfl M M 0 0 rfl
      (by dsimp only [B, uniformData]; omega) H (by omega) (by omega) (by omega)
      r threeRoles [1] [2, 3] rfl rfl rfl hp hC hC1 ζ Lh Lρ
