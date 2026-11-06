/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of terminal-rate PREP salary)
import Complexity.Foundations.Probability.HierarchyPreparationRateSalary
import all ComplexityTests.HierarchyPreparationPayment

/-!
The imported complete client checks genuine nonconstant RAW33/PREP34, positive own
error and the original root decoder, separately from exhaustive production-bin algebra.
These tests add exact numerical salary boundaries for both rank gaps, a nontrivial
terminal-rate cost, zero coefficient, and the surviving rate obstruction. They do not
claim recursive execution of the growing joint guard family. The inherited execution
fixture has charge zero; its numerical salary guard is not asserted.
-/
set_option linter.privateModule false
noncomputable section
open Cslib Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.BudgetData

example : (rate 0)⁻¹ ^ 4 = 1 := by norm_num [rate]
example : (rate 1)⁻¹ ^ 4 = 65536 := by norm_num [rate]
example : (rate 2)⁻¹ ^ 4 = 4294967296 := by norm_num [rate]

-- One fixed charge pays a bounded rate family before fields or requests exist.
example (c : ℝ) : ∃ A₀ : ℕ, 7 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ (ka : ℕ), ka ≤ 3 → ∀ pilot : Bool,
    Real.logb 2 c + 16 * (ka : ℝ) + 1 / 4 ≤
      4 * (A : ℝ) * (if pilot then 40 else 4) :=
  exists_preparation_bounded_rate_charge c 3 7

-- At coefficient one and charge one, actual gap four pays exponent zero but
-- fails at exponent two. Pilot gap forty still pays exponent two.
example : Real.logb 2 (1 : ℝ) + 16 * (0 : ℝ) + 1 / 4 ≤ 4 * 1 * 4 := by norm_num
example : 4 * (1 : ℝ) * 4 < Real.logb 2 (1 : ℝ) + 16 * 2 := by norm_num
example : Real.logb 2 (1 : ℝ) + 16 * 2 + 1 / 4 ≤ 4 * 1 * 40 := by norm_num

section
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}
variable (B : BudgetData HP P) (M : ℕ) (pilot : Bool) (i : Fin HP.k)
variable (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
variable (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))

-- Zero cost is always paid, including a zero/truncated budget and arbitrary rates.
example :
    let q := {r with task := .row 0 (if pilot then .pilotInput i else .input i)}
    0 * r.terminal.rate⁻¹ ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  dsimp only
  simp only [zero_mul]
  positivity

-- At slack one and positive budget, the exact boundary retains loss 1/4 in
-- the fourth-moment exponent. It is equality, not the relaxed guard's 1/4 bound.
example (hslack : B.slack = 1) (hM : 0 < M) :
    let q := {r with task := .row 0 (if pilot then .pilotInput i else .input i)}
    (2 : ℝ) ^ (4 * B.rankCharge * (if pilot then 40 else 4) - 1 / 4) *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 =
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  have hm : B.childBudget M = M - 1 := by
    simp [BudgetData.childBudget, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff, hslack]
  have hcast : (B.childBudget M : ℝ) = (M : ℝ) - 1 := by
    rw [hm, Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
  have hd := B.requestPrecision_preparation_input M (B.childBudget M) pilot i r hr
  dsimp only at hd ⊢
  rw [hcast, hslack] at hd
  have hp (x : ℝ) : ((2 : ℝ) ^ x) ^ 4 = (2 : ℝ) ^ (4 * x) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  rw [hp, hp, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  linarith

-- Both channels are inherited unchanged, so neither of their precision penalties
-- can provide a terminal-rate salary. This checks positive precision separately.
example (hslack : B.slack = 1) (hcharge : 1 ≤ B.rankCharge) (hM : 0 < M)
    (hp : 0 < B.requestPrecision M r) :
    0 < B.requestPrecision (B.childBudget M)
      {r with task := .row 0 (if pilot then .pilotInput i else .input i)} :=
  B.requestPrecision_preparation_input_pos hslack hcharge M hM pilot i r hr hp

end

-- The same actual task and own channels give honest full-rate payment; the
-- terminal exponent two counterexample does not disappear at a larger budget.
example {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (B : BudgetData HP P) (M : ℕ) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (.preparation i)) (hcharge : B.rankCharge = 1)
    (ht : r.terminal.rate = rate 0) :
    let q := {r with task := .row 0 (.input i)}
    1 * r.terminal.rate⁻¹ ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  apply B.preparation_rate_salary_le M false i r hr 0 ht 1 (by norm_num)
  norm_num [hcharge]

example {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (B : BudgetData HP P) (M : ℕ) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (.preparation i)) (hcharge : B.rankCharge = 1)
    (ht : r.terminal.rate = rate 2) :
    let q := {r with task := .row 0 (.input i)}
    ¬ 1 * r.terminal.rate⁻¹ ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  apply B.preparation_rate_envelope_unpaid M false i r hr 2 ht 1 (by norm_num)
  norm_num [hcharge]
