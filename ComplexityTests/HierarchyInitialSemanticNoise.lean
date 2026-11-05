/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of semantic initial group support and uniform noise)
import Complexity.Foundations.Probability.HierarchyInitialSemanticNoise
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import all ComplexityTests.PolynomialBudgetHistory

/-! Nonzero canonical samples cancel at two positive endpoint budgets. A growing full-bin
family instantiates the original budget's uniform payment with positive parent precision. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open PolynomialBudgetHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

section Small
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Fine budget63 and coarse budget62 both carry the same nonzero semantic sample.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    (data HP).initialSample (request HP) 0 σ 0 0 = 1 ∧
      (data HP).initialGroupInput 64 1 (request HP) σ 0 0 = 0 := by
  constructor
  · rw [initial HP 0 (by simp [data])]
    norm_num [base]
  · rw [(data HP).initialGroupInput_eq_zero_of_two_mul_lt 64 1 (request HP) (by decide)]
    rfl

end Small

example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P : ℕ) [Fact P.Prime] (H : Horizon P) (n : ℕ) (hn : n ≤ H.maxExponent)
    (j : ℕ) (hj : j ≤ Nat.log2 (16 * (n + 257)) + 1) :
    let B : BudgetData HP P := { uniformData HP P n with rankCharge := 7 }
    let r := uniformRequest HP P
    0 < B.requestPrecision (16 * (n + 257)) r ∧
      B.initialRelativeNoiseBudget (16 * (n + 257)) r 0 2 (by decide)
        0 0 [1] [2, 3] B.base j ≤
        (256 * B.binCap * (2 : ℝ) ^ (-B.requestPrecision (16 * (n + 257))
          {r with usage := r.terminal}) * (2 : ℝ) ^ (-B.rankCharge) *
          (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 (16 * (n + 257)) + 1) (j - 1)) ^ 4 := by
  dsimp only
  let B : BudgetData HP P := { uniformData HP P n with rankCharge := 7 }
  let r := uniformRequest HP P
  have hp : 0 < B.requestPrecision (16 * (n + 257)) r := by
    rw [B.requestPrecision_grid (16 * (n + 257)) 0 0 r rfl rfl]
    norm_num [B, r, uniformData, uniformRequest, HierarchyTask.rank,
      BoundedRowTask.localTask, CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨hp, ?_⟩
  apply B.initialRelativeNoiseBudget_polynomial_uniform_le
    (by norm_num [B, uniformData]) rfl rfl H
    (by intro i hi; have hlt : i < n + 1 := by simpa [B, uniformData] using hi
        omega)
    (16 * (n + 257)) (by positivity) r 0 2 (by decide) 0 0 [1] [2, 3]
    rfl rfl rfl (Nat.zero_le _) hp.le
    (by intro x y; change 0 ≤ (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
        simp only [Matrix.one_apply]; split_ifs <;> norm_num)
    (by simp [B, uniformData]) j hj
