/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of complete initial first-noise allocation)
import Complexity.Foundations.Probability.HierarchyTransportedPreparation
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import all ComplexityTests.PolynomialBudgetHistory

/-! A charge chosen before every field and growing full-bin family pays the actual
computed first-noise minimum, including semantic noise. This numerical regression
keeps the distinction from constructing successful recursive children. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment PolynomialBudgetHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

example (HP : FourthRootHierarchyParams 16 1 16 32 8) (coefficient : ℝ) :
    ∃ A : ℕ, ∀ (P : ℕ) [Fact P.Prime] (n p : ℕ) (H : Horizon P),
      n + 2 ≤ H.maxExponent →
      let B : BudgetData HP P := { uniformData HP P (n + 2) with rankCharge := A }
      let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
        ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 n [1],
          gridChannel 2 (n + 1) [2, 3], gridChannel 2 (n + 1) [2, 3]⟩
      let M := 16 * (A * r.task.rank + p + 4 * n + 4)
      B.requestPrecision M r = p + 2 ∧ 0 < B.requestPrecision M r ∧
      ∀ j < Nat.log2 M + 1,
        B.initialComputedPrecisionMoment M n r threeRoles n (n + 1) [1] [2, 3]
          coefficient 0 0 0 j true 0 ≤
          ((2 : ℝ) ^ (-((p : ℝ) + 2)) *
            (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  obtain ⟨A, hA⟩ := BudgetData.initialComputedPrecisionMoment_firstNoise_polynomial_paid
    (HP := HP) 16 coefficient
  refine ⟨A, ?_⟩
  intro P _ n p H hn
  dsimp only
  let B : BudgetData HP P := { uniformData HP P (n + 2) with rankCharge := A }
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 n [1],
      gridChannel 2 (n + 1) [2, 3], gridChannel 2 (n + 1) [2, 3]⟩
  let M := 16 * (A * r.task.rank + p + 4 * n + 4)
  have hp : B.requestPrecision M r = p + 2 := by
    rw [B.requestPrecision_grid M n (n + 1) r rfl rfl]
    dsimp only [B, uniformData]
    dsimp only [M]
    push_cast
    ring
  refine ⟨hp, by rw [hp]; positivity, ?_⟩
  intro j hj
  have h := hA B rfl rfl rfl rfl H M j n (n + 1) (by dsimp only [M]; positivity)
    hj (by omega) (by
      intro i hi
      have hlt : i < n + 3 := by simpa [B, uniformData, Nat.add_assoc] using hi
      omega) r threeRoles [1] [2, 3] rfl rfl rfl
    (by rw [hp]; positivity)
    (by intro x y; change 0 ≤ (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
        simp only [Matrix.one_apply]; split_ifs <;> norm_num)
    (by simp [B, uniformData]) n 0 0 0
  simpa only [hp] using h

-- The field and horizon hypotheses of the growing family are jointly satisfiable.
example (n : ℕ) :
    ∃ P, P.Prime ∧ ∃ H : Horizon P, H.maxExponent = n := by
  obtain ⟨P, hP, _, _, H, hn, _⟩ := exists_bounded_depth_prime n 0 (by positivity)
  exact ⟨P, hP, H, hn⟩
