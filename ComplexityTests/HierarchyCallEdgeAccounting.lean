/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual evaluator call-edge accounting)
import Complexity.Foundations.Probability.HierarchyCallEdgeAccounting
import all ComplexityTests.HierarchyDecoderRateObstruction

/-!
The imported clients retain executed RAW33/PREP34, nonzero own error, production-bin
algebra, joint guards and the actual own-support decoder rate regression. Here success
extracts the literal input and completion; separate pilot/actual accounting checks
include exhausted budgets, unequal source rates and inherited suffixes. The rejected
budget boost is tested against the actual strict history and normalized consumer.
No growing recursive family or changed precision policy is asserted.
-/
set_option linter.privateModule false
noncomputable section
open Cslib Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open InitialPilotScoreRegression IncomingPreparationBiasRegression
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The hypotheses are inhabited, and success recovers a real own-input child.
example : ∃ (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (A : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ),
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    B.evaluate (B.childBudget 34)
        { r with task := .row 0 (.pilotInput ⟨0, HP.k_pos⟩) } = some (.row A) ∧
      B.complete 34 r (B.incomingPreparation r A) = some completedTable := by
  obtain ⟨HP⟩ := FourthRootHierarchyParams.nonempty
    (q := 16) (cπ := 1) (Cπ := 16) (Cpair := 32) (Cvar := 8) (by norm_num) (by norm_num)
  obtain ⟨A, hA, hW⟩ := (halfData HP).evaluate_preparation_child 34 true ⟨0, HP.k_pos⟩
    (PreparationExecutionRegression.prepRequest HP) rfl (by decide) (prep_active HP)
    completedTable (prep_evaluated HP)
  exact ⟨HP, A, hA, hW⟩

-- Literal loss is one at RAW33/PREP34, but exhausts to zero below slack.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).childBudget 34 = 33 ∧ (halfData HP).childBudget 0 = 0 := by
  norm_num [BudgetData.childBudget, halfData, budgetData,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]

-- Adding 4ka accuracy bits is already rejected at ka=1, despite positive child precision.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := halfData HP
    let q := budgetRequest HP
    0 < B.requestPrecision 97 q ∧
    (if B.childBudget 34 + 64 * B.slack * 1 < 34 then
      B.evaluate (B.childBudget 34 + 64 * B.slack * 1) q else none) = none := by
  refine ⟨?_, (halfData HP).preparation_augmented_history_rejected 34 1
    (by norm_num [halfData, budgetData]) (by decide) _⟩
  rw [precision]
  norm_num

-- The exact proposed accuracy gain uses the current precision and literal integer budget.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).requestPrecision 97 (budgetRequest HP) -
      (halfData HP).requestPrecision 33 (budgetRequest HP) = 4 := by
  have h := (halfData HP).requestPrecision_budget_boost 33 1 (budgetRequest HP)
  simpa only [halfData, budgetData, Nat.mul_one, Nat.one_mul, Nat.reduceAdd,
    Nat.cast_one, mul_one] using h

-- The actual normalized assembly cannot replace its unavailable PREP with successful RAW.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (pilot : Bool) :
    let i : Fin HP.k := ⟨0, HP.k_pos⟩
    let B := halfData HP
    let r := budgetRequest HP
    let history := fun (_ : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) =>
      if q.task = .row 0 (if pilot then .pilotInput i else .input i)
      then some (BudgetValue.row halfTable) else none
    BudgetData.row history (B.childBudget 34)
      { r with task := .row 0 (if pilot then .pilotInput i else .input i) } =
      some halfTable ∧ B.normalized history 34 r pilot i = none := by
  dsimp only
  constructor
  · simp [BudgetData.row, BudgetValue.row?]
  · apply BudgetData.normalized_preparation_rejected
    cases pilot <;> simp [BudgetData.row]

-- A successful PREP34 is not the PREP33 demanded by normalized34. RAW33 succeeds,
-- but RAW32 is inactive; the literal PREP33 call therefore fails.
private lemma adjacent_preparation_boundary
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    B.evaluate 33 (budgetRequest HP) = some (.row halfTable) ∧
      B.evaluate 34 r = some (.row completedTable) ∧ B.evaluate 33 r = none := by
  refine ⟨half_evaluated HP, prep_evaluated HP, ?_⟩
  have hraw : (halfData HP).evaluate 32 (budgetRequest HP) = none := by
    rw [BudgetData.evaluate_eq]
    have hp : (halfData HP).requestPrecision 32 (budgetRequest HP) = 0 := by
      rw [precision]; norm_num
    simp only [BudgetData.step,
      show (budgetRequest HP).task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) from rfl,
      hp, lt_self_iff_false, ↓reduceIte]
  have hp : 0 < (halfData HP).requestPrecision 33
      (PreparationExecutionRegression.prepRequest HP) := by
    rw [BudgetData.requestPrecision_grid _ 33 1 0 _ rfl rfl]
    norm_num [halfData, budgetData]
  have hm : (halfData HP).childBudget 33 = 32 := by
    norm_num [BudgetData.childBudget, halfData, budgetData,
      LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  have hrow : BudgetData.row
      (fun m r => if m < 33 then (halfData HP).evaluate m r else none)
      ((halfData HP).childBudget 33)
      { PreparationExecutionRegression.prepRequest HP with
        task := .row 0 (.pilotInput ⟨0, HP.k_pos⟩) } = none := by
    rw [hm]
    change ((if 32 < 33 then (halfData HP).evaluate 32 (budgetRequest HP) else none).bind
      BudgetValue.row?) = none
    rw [ite_eq_left (by decide), hraw]
    rfl
  rw [BudgetData.evaluate_eq]
  simp only [BudgetData.step,
    show (PreparationExecutionRegression.prepRequest HP).task =
      .row 0 (.pilotPreparation ⟨0, HP.k_pos⟩) from rfl,
    hp, ↓reduceIte, hrow]
  rfl

-- This is the actual active normalized evaluator, not merely an injected history.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let r := { budgetRequest HP with task := .row 0 (.pilotNormalized ⟨0, HP.k_pos⟩) }
    0 < (halfData HP).requestPrecision 34 r ∧ (halfData HP).evaluate 34 r = none := by
  intro r
  have hp : 0 < (halfData HP).requestPrecision 34 r := by
    rw [BudgetData.requestPrecision_grid _ 34 1 0 _ rfl rfl]
    norm_num [halfData, budgetData]
  refine ⟨hp, ?_⟩
  have hrow : BudgetData.row
      (fun m q => if m < 34 then (halfData HP).evaluate m q else none)
      ((halfData HP).childBudget 34)
      { r with task := .row 0 (.pilotPreparation ⟨0, HP.k_pos⟩) } = none := by
    have hm : (halfData HP).childBudget 34 = 33 := by
      norm_num [BudgetData.childBudget, halfData, budgetData,
        LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
    rw [hm]
    change ((if 33 < 34 then (halfData HP).evaluate 33
      (PreparationExecutionRegression.prepRequest HP) else none).bind BudgetValue.row?) = none
    rw [ite_eq_left (by decide), (adjacent_preparation_boundary HP).2.2]
    rfl
  have hn := (halfData HP).normalized_preparation_rejected _ 34 r true ⟨0, HP.k_pos⟩ hrow
  rw [BudgetData.evaluate_eq]
  simp only [BudgetData.step,
    show r.task = .row 0 (.pilotNormalized ⟨0, HP.k_pos⟩) from rfl,
    hp, ↓reduceIte, hn, Option.map_none]

section Accounting
variable {HP : FourthRootHierarchyParams 16 1 16 32 8} (B : BudgetData HP 5)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) (i : Fin HP.k)

-- The normalized parent's PREP child keeps literal channels at the next budget.
-- This checks both constructor families through the public unchanged-channel API.
example (M : ℕ) (pilot : Bool)
    (hr : r.task = .row 0 (if pilot then .pilotNormalized i else .normalized i)) :
    let q := { r with task := .row 0 (if pilot then .pilotPreparation i else .preparation i) }
    q.source = r.source ∧ q.terminal = r.terminal ∧ q.usage = r.usage ∧
      B.requestPrecision (B.childBudget M) q - B.requestPrecision M r =
        ((B.childBudget M : ℝ) - M) / (16 * B.slack) + 4 * B.rankCharge := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [B.requestPrecision_task_sub]
  cases pilot <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
  all_goals
    simp only [hr, HierarchyTask.rank, CorrectionRowTask.rank, PilotRowTask.rank,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_zero, zero_add]
    ring

-- Actual gap four and pilot gap forty have the same remaining ordinary rate cost.
example (M : ℕ) (pilot : Bool)
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (ht : r.terminal.rate = rate 1) :
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    1 * r.terminal.rate⁻¹ ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      (1 / 2) * ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 ↔
    17 / 4 ≤ B.rankCharge * (if pilot then 40 else 4) -
      ((M : ℝ) - B.childBudget M) / (16 * B.slack) := by
  have h := B.preparation_edge_log_requirement M pilot i r hr 1 ht 1 (1 / 2)
    (by norm_num) (by norm_num)
  dsimp only
  norm_num at h ⊢
  exact h

-- INPUT-only extra precision is visible even at zero budget: the zero boundary changes.
example (pilot : Bool)
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i)) :
    (B.requestPrecision (B.childBudget 0)
        { r with task := .row 0 (if pilot then .pilotInput i else .input i) } -
        (-1 : ℝ) * (4 * 3)) -
      (B.requestPrecision 0 r - 0 * (4 * 3)) =
      B.rankCharge * (if pilot then 40 else 4) + 12 := by
  have h := B.preparation_reweighted_difference 0 pilot i r hr 3 0 (-1)
  norm_num [BudgetData.childBudget, LogSpaceEstimation.lastBudget] at h ⊢
  exact h

-- Detector reset changes source RATE only; the rank salary is twelve.
example (M : ℕ) (hr : r.task = .row 0 (.detector i))
    (hs : r.source.rate = rate 1) (ht : r.terminal.rate = rate 0) :
    let q := { r with
      task := .row 0 (.score i)
      source := { r.source with rate := r.terminal.rate } }
    q.source.role = r.source.role ∧ q.source.suffix = r.source.suffix ∧
      q.terminal = r.terminal ∧ q.usage = r.usage ∧
      B.requestPrecision (B.childBudget M) q - B.requestPrecision M r =
        ((B.childBudget M : ℝ) - M) / (16 * B.slack) + 2 + 12 * B.rankCharge := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [B.requestPrecision_detector_score M (B.childBudget M) r i hr, hs, ht]
  have hlog : Real.logb 2 (rate 1) = -4 := by
    simp only [rate, pow_one]
    rw [Real.logb_pow, Real.logb_inv]
    norm_num
  norm_num [hlog, show rate 0 = 1 by norm_num [rate]]

-- Actual PREP has enough rank that the geometry-rank workaround breaks activity.
example (M n : ℕ) (hM : M ≤ 32 * B.slack * n)
    (hr : r.task = .row 0 (.preparation i)) (hcharge : 0 ≤ B.rankCharge)
    (ht : r.terminal.rate = rate 0) (hs : r.source.rate = rate 1) :
    B.requestPrecision M r - (n : ℝ) * r.task.rank ≤ 0 := by
  apply B.geometry_rank_surcharge_nonpos M n r hM _ hcharge
    (ht ▸ rate_pos 0) (by rw [ht]; norm_num [rate])
    (hs ▸ rate_pos 1) (by rw [hs]; norm_num [rate])
  simp only [hr, HierarchyTask.rank, CorrectionRowTask.rank]
  omega
end Accounting
