/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of weighted incoming PREP transfer)
import Complexity.Foundations.Probability.HierarchyWeightedPreparation
import all ComplexityTests.HierarchyCallEdgeAccounting

/-!
The actual nonconstant RAW33/PREP34 fixture consumes the relative transfer with its
canonical reference and nonzero ordinary own error. Imported complete tests retain
one-open/both-closed gate boundaries, joint guards and literal normalized failure.
The one-entry family below computes the new relative cost rather than assuming it
is supplied for free. These histories are supplied executions, not a recursive IH.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open InitialPilotScoreRegression IncomingPreparationBiasRegression
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
namespace WeightedPreparationRegression

example : ∃ HP : FourthRootHierarchyParams 16 1 16 32 8, 0 < HP.θ := by
  obtain ⟨HP⟩ := FourthRootHierarchyParams.nonempty
    (q := 16) (cπ := 1) (Cπ := 16) (Cpair := 32) (Cvar := 8) (by norm_num) (by norm_num)
  exact ⟨HP, HP.θ_pos⟩

-- Endpoint and interior values exercise the proved derivative coefficient.
example : |(1 / 2 : ℝ) ^ (-(4⁻¹ : ℝ)) - 1 ^ (-(4⁻¹ : ℝ))| ^ 4 ≤ (1 / 2) ^ 4 / 8 := by
  convert FourthRootHierarchyParams.inverse_fourth_root_fourth_le
    (a := (1 / 2 : ℝ)) (b := 1) (by norm_num) (by norm_num) using 1; norm_num

section Five
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma relative_accuracy (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 5 r.source.rate X U
      (fun σ x y => (halfTable σ x y - base x y) / (1 + base x y)) ≤
      ((2 : ℝ) ^ (-B.requestPrecision 33 (budgetRequest HP))) ^ 4 := by
  have hX : (fun σ x => (PreparationExecutionRegression.prepRequest HP).source.retains
      (channels (halfData HP).padding) σ x) = source := by
    funext σ x
    simp only [PreparationExecutionRegression.prepRequest, budgetRequest, request,
      gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
      source, X, roles, halfData, budgetData]
  dsimp only
  simp only [hX]
  apply le_trans _ (own_accuracy HP)
  apply (rowNormPow_le_mul (N := 5) (u := rate 1) (c := 1)
    (mul_nonneg (by norm_num) (rate_pos 1).le) ?_).trans_eq (one_mul _)
  intro σ x y _ _
  have hb : 0 ≤ base x y := by
    by_cases hxy : x = y <;> norm_num [base, Matrix.one_apply, hxy]
  have hp : |(halfTable σ x y - base x y) / (1 + base x y)| ≤
      |halfTable σ x y - base x y| := by
    rw [abs_div, abs_of_pos (by linarith : 0 < 1 + base x y)]
    exact div_le_self (abs_nonneg _) (by linarith)
  simpa only [one_mul] using pow_le_pow_left₀ (abs_nonneg _) hp 4

-- Ordinary and relative accuracies hold simultaneously on the same actual masks.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let U := fun σ y => (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ y
    rowNormPow 4 5 (rate 1) source U (fun σ x y => halfTable σ x y - base x y) = 81 / 625 ∧
    (halfData HP).evaluate 33 (budgetRequest HP) = some (.row halfTable) ∧
    (halfData HP).evaluate 34 (PreparationExecutionRegression.prepRequest HP) =
      some (.row completedTable) :=
  ⟨own_moment HP, half_evaluated HP, prep_evaluated HP⟩

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ halfTable prep (fun _ _ => 0)
    let V := B.incomingPreparation r (fun _ => base)
    rowNormPow 4 5 r.source.rate X U (fun σ x y =>
      correctionNumerator HP B.padding id r halfTable (fun _ _ => 0) σ x y ^ (4⁻¹ : ℝ) *
        (FourthRootHierarchyParams.NormalizedRow.clip (rowSliceMean X U completedTable x y) -
          FourthRootHierarchyParams.NormalizedRow.clip (rowSliceMean X U V x y))) ≤
      HP.Q HP.toHierarchyParams.atomCap * (L * 2) ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision 33 (budgetRequest HP))) ^ 4 ∧
    rootDistPow 4 5 r.source.rate X U (output completedTable) (output V) ≤
      HP.Q HP.toHierarchyParams.atomCap / 8 * (L * 2) ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision 33 (budgetRequest HP))) ^ 4 := by
  obtain ⟨L, hL, h⟩ := BudgetData.evaluate_preparation_relative_root (HP := HP)
  refine ⟨L, hL, ?_⟩
  have ht : (PreparationExecutionRegression.prepRequest HP).terminal.rate = 1 := by
    norm_num [PreparationExecutionRegression.prepRequest, budgetRequest, request,
      gridChannel, rate]
  have hg : ∀ x y, (halfData HP).canonicalPreparationInput true ⟨0, HP.k_pos⟩
      (PreparationExecutionRegression.prepRequest HP) x y ∈ Set.Icc 0 (1 * (1 : ℝ)) := by
    intro x y
    rw [canonical_zero]
    by_cases hxy : x = y <;> norm_num [base, Matrix.one_apply, hxy]
  have hp : 0 < (halfData HP).requestPrecision 33 (budgetRequest HP) := by
    rw [precision]; norm_num
  have hr := h 5 (halfData HP) 34 true ⟨0, HP.k_pos⟩
    (PreparationExecutionRegression.prepRequest HP) rfl (admissible HP) (prep_active HP)
    ((halfData HP).childBudget_lt (by decide)) rfl (rate_pos 1).le (rate_pos 0)
    halfTable completedTable hp (half_evaluated HP) (prep_evaluated HP)
    1 ((2 : ℝ) ^ (-(halfData HP).requestPrecision 33 (budgetRequest HP))) (by norm_num)
  rw [ht] at hr
  have hr' := hr hg
  simp only [canonical_zero] at hr'
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num, Nat.cast_ofNat] using
    (hr' (relative_accuracy HP) 0 2 (by decide) 1 0 [1] [2, 3] rfl rfl
      halfTable (fun _ _ => 0))

-- The normalized parent consumes PREP one budget below itself, which consumes
-- its own RAW one more budget below. Rate penalties cancel on these unchanged
-- channels; both literal budget losses remain. No salary or availability follows.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (B : BudgetData HP 5)
    (M : ℕ) (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
    (hr : r.task = .row 0 (if pilot then .pilotNormalized i else .normalized i)) :
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    B.requestPrecision (B.childBudget (B.childBudget M)) q - B.requestPrecision M r =
      ((B.childBudget (B.childBudget M) : ℝ) - M) / (16 * B.slack) +
        B.rankCharge * (if pilot then 44 else 8) := by
  dsimp only
  rw [B.requestPrecision_task_sub]
  cases pilot <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
  all_goals
    simp only [hr, HierarchyTask.rank, CorrectionRowTask.rank, PilotRowTask.rank,
      PilotTask.rank, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_zero, zero_add]
    ring

end Five
section RateFamily
open Matrix.DecoderRateObstruction
variable {P : ℕ} [Fact P.Prime]

-- The reference range d=1 is genuinely inhabited throughout the rate family.
example (ka : ℕ) (x y : ZMod P) :
    single 0 0 (rate ka) x y ∈ Set.Icc 0 (1 * rate ka) := by
  simp only [single_apply]
  split_ifs <;> simp only [one_mul, Set.mem_Icc, le_refl, and_true, true_and]
  · exact (rate_pos ka).le
  · exact (rate_pos ka).le

-- Both denominators and masks are literal. Relative error is constant in RAW units
-- after division by f+G, while ordinary error shrinks as f^4. The actual rounded
-- density is retained in both quantities; no nominal-rate substitution occurs.
private lemma relative_moment (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    rowNormPow 4 P (request (P := P) HP ka).source.rate
      (fun σ x => (request (P := P) HP ka).source.retains (channels (1 : ZMod P)) σ x)
      (fun σ y => (request (P := P) HP ka).usage.retains (channels (1 : ZMod P)) σ y)
      (fun _ x y => (single 0 0 (5 * HP.θ * rate ka / 8) x y -
        single 0 0 (rate ka) x y) / (rate ka + single 0 0 (rate ka) x y)) =
      densityFactor (P := P) ka * (1 - 5 * HP.θ / 8) ^ 4 / 16 := by
  have hf : rate ka ≠ 0 := (rate_pos ka).ne'
  have he : (fun (_ : Environment P 3) (x y : ZMod P) =>
      (single 0 0 (5 * HP.θ * rate ka / 8) x y - single 0 0 (rate ka) x y) /
        (rate ka + single 0 0 (rate ka) x y)) =
      fun _ => single 0 0 ((5 * HP.θ / 8 - 1) / 2) := by
    funext σ x y
    simp only [single_apply]
    split_ifs <;> field_simp [hf] <;> ring
  rw [he, entry_moment, (by decide : Even 4).pow_abs]
  ring

-- This exact relation displays the extra relative allowance's rate cost. At
-- exponent ka the norm conversion is 1/(2f), i.e. 4ka-1 accuracy bits. It is
-- compatible with the existing f^-4 decoder obstruction, not its cancellation.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ka : ℕ) :
    let X := fun σ x => (request (P := P) HP ka).source.retains (channels 1) σ x
    let U := fun σ y => (request (P := P) HP ka).usage.retains (channels 1) σ y
    let A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
      fun _ => single 0 0 (5 * HP.θ * rate ka / 8)
    let G : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ := fun _ => single 0 0 (rate ka)
    rowNormPow 4 P (request (P := P) HP ka).source.rate X U
        (fun σ x y => A σ x y - G σ x y) =
      (2 * rate ka) ^ 4 * rowNormPow 4 P (request (P := P) HP ka).source.rate X U
        (fun σ x y => (A σ x y - G σ x y) / (rate ka + G σ x y)) ∧
    0 < rowNormPow 4 P (request (P := P) HP ka).source.rate X U
        (fun σ x y => (A σ x y - G σ x y) / (rate ka + G σ x y)) := by
  dsimp only
  rw [input_moment, relative_moment]
  constructor
  · ring
  · have hθ : 0 < 1 - 5 * HP.θ / 8 := by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
    exact div_pos (mul_pos (densityFactor_pos ka) (pow_pos hθ 4)) (by norm_num)

end RateFamily
end WeightedPreparationRegression
