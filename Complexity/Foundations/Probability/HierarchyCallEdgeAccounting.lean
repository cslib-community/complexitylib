/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPreparationRateSalary

/-!
# Accounting at actual statistical-budget call edges

These original certificates expose the requests consumed by the existing PREP and
normalized evaluator branches. They keep the literal budget loss, channels and suffixes.
The logarithmic PREP requirement is for the sufficient field-free ordinary RAW
fourth-moment envelope. It is not a necessary condition on actual estimator error.
The normalized consumer measures fourth powers of fourth-root differences instead;
`evaluate_preparation_bounded_rate_paid_root` remains the guarded bridge between them.

Adding `64 * slack * ka` integer budget would buy `4 * ka` precision bits, but violates
the actual recursive history guard. A geometry times rank surcharge conflicts with
positive precision under the existing omission guard. Neither alternative is installed.
There is no new call graph or policy, no cycle claim and no joint recursive availability.
RAW scale edges, correction metric transport, copy and cross-stage closure remain separate.

## Main results

* `preparation_edge_log_requirement`: exact ordinary fourth-moment payment in precision bits.
* `preparation_augmented_history_rejected`: the actual history rejects the proposed budget boost.
* `normalized_preparation_rejected`: the normalized consumer cannot skip its PREP call.
* `geometry_rank_surcharge_nonpos`: the omission guard excludes positive surcharged precision.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Cslib
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- A task replacement at unchanged channels has only budget and rank contributions.
This applies to all three literal children in `normalized`, without identifying them. -/
theorem requestPrecision_task_sub (B : BudgetData HP P) (M m : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (t : HierarchyTask HP.k) :
    B.requestPrecision m { r with task := t } - B.requestPrecision M r =
      ((m : ℝ) - M) / (16 * B.slack) + B.rankCharge * ((r.task.rank : ℝ) - t.rank) := by
  unfold requestPrecision LogSpaceEstimation.precision
  ring

/-- The detector's actual score child resets only the source rate. Source role and
suffix, terminal and usage remain literal structure fields, even when the rates differ. -/
theorem requestPrecision_detector_score (B : BudgetData HP P) (M m : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : Fin HP.k)
    (hr : r.task = .row 0 (.detector i)) :
    B.requestPrecision m
        { r with task := .row 0 (.score i), source := { r.source with rate := r.terminal.rate } } -
      B.requestPrecision M r =
      ((m : ℝ) - M) / (16 * B.slack) +
        (Real.logb 2 r.terminal.rate - Real.logb 2 r.source.rate) / 2 +
        12 * B.rankCharge := by
  simp only [requestPrecision, LogSpaceEstimation.precision, hr, HierarchyTask.rank,
    CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_zero, zero_add]
  ring

/-- Exact bit requirement for the ordinary RAW envelope, with fraction `eta` of the
parent fourth-moment allowance. The input is the literal PREP child, with both own
masks unchanged. `c` includes all proved transfer constants; it is not an error IH. -/
theorem preparation_edge_log_requirement (B : BudgetData HP P) (M : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (ka : ℕ) (ht : r.terminal.rate = rate ka) (c eta : ℝ)
    (hc : 0 < c) (heta : 0 < eta) :
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    c * r.terminal.rate⁻¹ ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      eta * ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 ↔
    4 * (ka : ℝ) + Real.logb 2 (c / eta) / 4 ≤
      B.rankCharge * (if pilot then 40 else 4) -
        ((M : ℝ) - B.childBudget M) / (16 * B.slack) := by
  dsimp only
  have hdiv : c / eta * r.terminal.rate⁻¹ ^ 4 *
      ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M)
        { r with task := .row 0 (if pilot then .pilotInput i else .input i) })) ^ 4 =
      (c * r.terminal.rate⁻¹ ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M)
          { r with task := .row 0 (if pilot then .pilotInput i else .input i) })) ^ 4) / eta := by
    ring
  have hsalary := B.preparation_rate_salary_iff M pilot i r hr ka ht (c / eta)
  dsimp only at hsalary
  rw [← div_le_iff₀' heta, ← hdiv, hsalary,
    ← Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (mul_pos (div_pos hc heta) (Real.rpow_pos_of_pos (by norm_num) _)),
    Real.logb_mul (div_pos hc heta).ne' (Real.rpow_pos_of_pos (by norm_num) _).ne',
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  ring_nf
  constructor <;> intro h <;> linarith

/-- Candidate terminal-rate weights at the literal PREP/input edge. These are
expressions for a feasibility calculation, not a replacement precision definition.
A coefficient gap one contributes exactly the `4 * ka` ordinary-RAW cost. -/
theorem preparation_reweighted_difference (B : BudgetData HP P) (M : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (ka : ℕ) (betaPrep betaInput : ℝ) :
    (B.requestPrecision (B.childBudget M)
        { r with task := .row 0 (if pilot then .pilotInput i else .input i) } -
        betaInput * (4 * ka)) -
      (B.requestPrecision M r - betaPrep * (4 * ka)) =
      ((B.childBudget M : ℝ) - M) / (16 * B.slack) +
        B.rankCharge * (if pilot then 40 else 4) + (betaPrep - betaInput) * (4 * ka) := by
  have h := B.requestPrecision_preparation_input M (B.childBudget M) pilot i r hr
  dsimp only at h
  linarith

/-- At zero scale the actual slack loss is `min M slack`, including exhaustion. -/
theorem childBudget_eq_sub_slack (B : BudgetData HP P) (M : ℕ) :
    B.childBudget M = M - B.slack := by
  have hs : 1 ≤ B.slack := B.slack_pos
  simp [childBudget, LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
    max_eq_right hs]

/-- The rejected integer boost really would buy four bits per terminal exponent
at this same request. No task rank, channel, mask or allocator is replaced. -/
theorem requestPrecision_budget_boost (B : BudgetData HP P) (m ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.requestPrecision (m + 64 * B.slack * ka) r - B.requestPrecision m r = 4 * ka := by
  have hs : (B.slack : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt B.slack_pos
  simp only [requestPrecision, LogSpaceEstimation.precision, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

/-- The proposed four-exponent accuracy boost costs `64 * slack * ka` budget.
Already at exponent one it is outside the existing strictly earlier history. -/
theorem preparation_augmented_budget_not_lt (B : BudgetData HP P) (M ka : ℕ)
    (hM : B.slack ≤ M) (hka : 1 ≤ ka) :
    ¬ B.childBudget M + 64 * B.slack * ka < M := by
  rw [B.childBudget_eq_sub_slack]
  have hmul : B.slack ≤ 64 * B.slack * ka := by nlinarith [B.slack_pos]
  omega

variable [Fact P.Prime]

/-- Success exposes the actual PREP child and completion, without assuming a
successful recursive family. This is the converse of `evaluate_preparation`. -/
theorem evaluate_preparation_child (B : BudgetData HP P) (M : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (hM : 0 < M) (hp : 0 < B.requestPrecision M r)
    (W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hW : B.evaluate M r = some (.row W)) :
    ∃ A, B.evaluate (B.childBudget M)
        { r with task := .row 0 (if pilot then .pilotInput i else .input i) } = some (.row A) ∧
      B.complete M r (B.incomingPreparation r A) = some W := by
  have hm := B.childBudget_lt hM
  have hstep := hW
  rw [evaluate_eq] at hstep
  cases pilot <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
  all_goals
    simp only [step, hr, hp, ↓reduceIte, row, hm] at hstep
    cases hchild : B.evaluate (B.childBudget M) _ with
    | none => simp [hchild] at hstep
    | some v =>
      cases v with
      | vector v => simp [hchild, BudgetValue.row?] at hstep
      | row A =>
        refine ⟨A, rfl, ?_⟩
        simp only [hchild, BudgetValue.row?, Option.bind_some] at hstep
        change (B.complete M r (B.incomingPreparation r A)).map BudgetValue.row =
          some (.row W) at hstep
        cases hc : B.complete M r (B.incomingPreparation r A) with
        | none => simp [hc] at hstep
        | some V =>
          simp only [hc, Option.map_some, Option.some.injEq, BudgetValue.row.injEq] at hstep
          exact congrArg some hstep

/-- Rejection is by the production history guard, even if the augmented child's
precision would be positive. This does not change the evaluator or its recursion. -/
theorem preparation_augmented_history_rejected (B : BudgetData HP P) (M ka : ℕ)
    (hM : B.slack ≤ M) (hka : 1 ≤ ka)
    (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    (if B.childBudget M + 64 * B.slack * ka < M then
      B.evaluate (B.childBudget M + 64 * B.slack * ka) q else none) = none :=
  ite_eq_right (B.preparation_augmented_budget_not_lt M ka hM hka)

/-- An actual normalized branch consumes exactly this PREP request at childBudget.
Failure propagates even when its separately budgeted RAW call succeeds. -/
theorem normalized_preparation_rejected (B : BudgetData HP P)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (pilot : Bool) (i : Fin HP.k)
    (hprep : row history (B.childBudget M)
      { r with task := .row 0 (if pilot then .pilotPreparation i else .preparation i) } = none) :
    B.normalized history M r pilot i = none := by
  unfold normalized
  cases hraw : row history (B.childBudget M)
      { r with task := .row 0 (if pilot then .pilotInput i else .input i) } <;>
    simp [hprep]

omit [Fact P.Prime] in
/-- Even before paying rate penalties, a geometry times rank surcharge excludes
positive precision when rank is at least two and `M ≤ 32 * slack * n`.
Actual PREP ranks are larger. This is a guard conflict, not an impossibility theorem. -/
theorem geometry_rank_surcharge_nonpos (B : BudgetData HP P)
    (M n : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hM : M ≤ 32 * B.slack * n) (hrank : 2 ≤ r.task.rank)
    (hcharge : 0 ≤ B.rankCharge)
    (ht : 0 < r.terminal.rate) (ht1 : r.terminal.rate ≤ 1)
    (hs : 0 < r.source.rate) (hs1 : r.source.rate ≤ 1) :
    B.requestPrecision M r - (n : ℝ) * r.task.rank ≤ 0 := by
  have hden : 0 < (16 * B.slack : ℝ) := by exact_mod_cast Nat.mul_pos (by decide) B.slack_pos
  have hm : (M : ℝ) / (16 * B.slack) ≤ 2 * n := by
    apply (div_le_iff₀ hden).2
    have hc : (M : ℝ) ≤ 32 * B.slack * n := by exact_mod_cast hM
    nlinarith
  have hr : (2 : ℝ) ≤ r.task.rank := by exact_mod_cast hrank
  have hn := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hlogt := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) ht.le ht1
  have hlogs := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hs.le hs1
  have hcost := mul_nonneg hcharge (Nat.cast_nonneg r.task.rank : (0 : ℝ) ≤ r.task.rank)
  unfold requestPrecision LogSpaceEstimation.precision
  linarith

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
