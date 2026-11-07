/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of four-statistic initial reserve allocation)
import Complexity.Foundations.Probability.HierarchyInitialReserveAssembly
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import all ComplexityTests.PolynomialBudgetHistory

/-! The common charge precedes every growing budget and field. The constructed prime
horizons satisfy sparse-noise coverage and admit every bin; the semantic deficit is positive.
No successful recursive children or native-space implementation is assumed to follow. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment PolynomialBudgetHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (coefficient ζ Lh Lρ floor cap C Cpre : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ k : ℕ, ∃ P, ∃ _ : Fact P.Prime, ∃ H : Horizon P,
      let M := 16 * (k + A * 36 + 1)
      let B : BudgetData HP P := { uniformData HP P M with
        rankCharge := A, base := (rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ) }
      let r := { uniformRequest HP P with usage := gridChannel 2 0 [2, 3] }
      (512 * HP.K + 1) * 2 ^ (2 * A) ≤ P ∧ M ≤ H.maxExponent ∧
      (∀ bin ∈ B.bins, bin ≤ H.maxExponent) ∧ 0 < B.requestPrecision M r ∧
      0 < B.base 0 0 * (1 - polynomialSwitch4 (1 / 2) 1 (B.base 0 0 / rate M)) ∧
      B.initialComputedFourStatisticReserve M M r threeRoles 0 0 [1] [2, 3]
        coefficient ζ Lh Lρ floor cap C Cpre ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  obtain ⟨A, hA1, hA⟩ := BudgetData.initialComputedFourStatisticReserve_exists_charge
    HP 16 coefficient ζ Lh Lρ floor cap C Cpre hf
  refine ⟨A, hA1, ?_⟩
  intro k
  let M := 16 * (k + A * 36 + 1)
  let cover := (512 * HP.K + 1) * 2 ^ (2 * A)
  let depth := M + cover
  obtain ⟨P, hprime, hPlo, _, H, he, _⟩ :=
    exists_bounded_depth_prime depth 0 (by positivity)
  let : Fact P.Prime := ⟨hprime⟩
  have hfield : cover ≤ P := by
    have hh := Nat.lt_two_pow_self (n := depth)
    dsimp only [depth] at hh hPlo
    omega
  have hM : M ≤ H.maxExponent := by rw [he]; dsimp only [depth]; omega
  let B : BudgetData HP P := { uniformData HP P M with
    rankCharge := A, base := (rate M / 4) • (1 : Matrix (ZMod P) (ZMod P) ℝ) }
  let r := { uniformRequest HP P with usage := gridChannel 2 0 [2, 3] }
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
  refine ⟨P, inferInstance, H, hfield, hM, ?_, hp, hpos, ?_⟩
  · intro bin hb
    change bin ∈ range (M + 1) at hb
    have hi := Nat.le_of_lt_succ (mem_range.mp hb)
    exact hi.trans hM
  · exact hA B rfl rfl rfl rfl rfl hfield M M 0 0 0 rfl
      (by dsimp only [B, uniformData]; omega) H hM (Nat.zero_le _) (Nat.zero_le _)
      r threeRoles [1] [2, 3] rfl rfl (by omega) rfl rfl hp hC hC1
