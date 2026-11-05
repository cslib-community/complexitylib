/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual incoming PREP execution)
import Complexity.Foundations.Probability.HierarchyPreparationExecution
import Complexity.Foundations.Probability.HierarchyCorrectionStability
import all ComplexityTests.InitialPilotScore
import all ComplexityTests.PolynomialBudgetHistory

/-!
Actual PREP at budget 65 consumes the evaluated nonconstant completed pilot input at budget 64.
The original source/terminal roles and different nonempty suffixes remain intact; the incoming
gate is proved open from its actual rank. The fixture is stationary on retained slices, not a
nonzero mixing-error or general recursive-availability example. Separate tests retain inactive
and invalid-frame rejection and distinguish incoming-gated PREP from dense preparation.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open InitialPilotScoreRegression
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace PreparationExecutionRegression

private def prepRequest (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  { budgetRequest HP with task := .row 0 (.pilotPreparation ⟨0, HP.k_pos⟩) }

private lemma raw_evaluated (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).evaluate 64 (budgetRequest HP) = some (.row completedTable) := by
  have hlog : Real.logb 2 (rate 1) = -4 := by
    simp only [rate, pow_one]
    rw [Real.logb_pow, Real.logb_inv]
    norm_num
  have hactive : 0 < (budgetData HP).requestPrecision 64 (budgetRequest HP) := by
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, budgetData,
      budgetRequest, request, gridChannel, hlog, show rate 0 = 1 by norm_num [rate]]
  rw [BudgetData.evaluate_eq]
  simp only [BudgetData.step,
    show (budgetRequest HP).task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) from rfl,
    hactive, ↓reduceIte]
  rw [shared_scheduled HP]
  rfl

private lemma active (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    0 < (budgetData HP).requestPrecision 65 (prepRequest HP) := by
  have hlog : Real.logb 2 (rate 1) = -4 := by
    simp only [rate, pow_one]
    rw [Real.logb_pow, Real.logb_inv]
    norm_num
  norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, budgetData,
    prepRequest, budgetRequest, request, gridChannel, hlog,
    show rate 0 = 1 by norm_num [rate]]

private lemma incoming (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).incomingPreparation (prepRequest HP) completedTable = completedTable := by
  funext σ x y
  unfold BudgetData.incomingPreparation correctionPrep rowGate incomingGate
  rw [kthLargest_eq_zero_of_card_lt
    ((card_filter_le _ _).trans_lt (by simpa using large_K HP)),
    kthLargest_eq_zero_of_card_lt
      ((card_filter_le _ _).trans_lt (by simpa using large_Kc HP))]
  rw [HP.ρ_one 0 HP.η_pos.le,
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)]
  simp only [mul_one]
  have hθ : HP.θ < 1 := by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
  change polynomialPrepCutoff4 HP.θ (completedTable σ x y / rate 0) = completedTable σ x y
  rw [show rate 0 = 1 by norm_num [rate], div_one]
  by_cases hs : source σ x
  · rw [show completedTable σ x y = base x y from ite_eq_left hs]
    by_cases hxy : x = y
    · subst y
      simp only [base, Matrix.one_apply_eq]
      exact polynomialPrepCutoff4_eq_one HP.θ_pos (by linarith)
    · simp only [base, Matrix.one_apply_ne hxy]
      exact polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos])
  · rw [show completedTable σ x y = 0 from ite_eq_right hs]
    exact polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos])

private lemma completed (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).complete 65 (prepRequest HP) completedTable = some completedTable := by
  rw [BudgetData.complete_grid _ 65 _ 0 2 (by decide) 1 0 [1] [2, 3] rfl rfl]
  apply congrArg some
  funext σ x y
  dsimp only [budgetData]
  unfold conditionalWalk
  have ht (τ : Environment 5 3) (w : ZMod 5) :
      Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier 1 [2, 3]) τ w := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using full_retains (τ 2) _
  simp only [mem_filter, mem_univ, true_and, ht, and_true]
  change (if _h : source σ x then _ else 0) = completedTable σ x y
  split_ifs with hs
  · have he : (fun τ : RetainedPairSlice
        (X (0 : Fin 3) (side 5 1) (CopyPadding.identifier 1 [1]))
        (Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier 1 [2, 3])) x y =>
        completedTable τ.val x y) = fun _ => base x y := by
      funext τ
      exact ite_eq_left (retainedPairSlice_source _ _ τ)
    rw [he, RotationMap.walk_pow_const]
    exact (ite_eq_left hs).symm
  · exact (ite_eq_right hs).symm

private lemma prep_evaluated (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).evaluate 65 (prepRequest HP) = some (.row completedTable) := by
  have hm : (budgetData HP).childBudget 65 = 64 := by
    norm_num [BudgetData.childBudget, budgetData, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff]
  have hc : (budgetData HP).evaluate ((budgetData HP).childBudget 65)
      { prepRequest HP with task := .row 0 (.pilotInput ⟨0, HP.k_pos⟩) } =
      some (.row completedTable) := by
    rw [hm]
    exact raw_evaluated HP
  rw [BudgetData.evaluate_preparation _ 65 true ⟨0, HP.k_pos⟩ _ rfl (active HP)
    (by rw [hm]; decide) _ hc, incoming HP, completed HP]
  rfl

-- Both the completed RAW child and returned PREP depend on the same source environment.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).evaluate 64 (budgetRequest HP) = some (.row completedTable) ∧
    (budgetData HP).evaluate 65 (prepRequest HP) = some (.row completedTable) ∧
    completedTable (seed 0) 0 0 = 1 ∧ completedTable (seed 4) 0 0 = 0 ∧
    (∀ j : Fin 3, j ≠ roles.source → seed 0 j = seed 4 j) ∧
    (prepRequest HP).source.suffix = [1] ∧ (prepRequest HP).usage.suffix = [2, 3] := by
  refine ⟨raw_evaluated HP, prep_evaluated HP, ?_, ?_, seed_agree 0 4, rfl, rfl⟩
  · rw [show completedTable (seed 0) 0 0 = base 0 0 from ite_eq_left source_both.1]
    simp [base]
  · exact ite_eq_right source_both.2

-- A real successful returned PREP feeds the generic same-slice normalizer identity.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (x y : ZMod 5) :
    rowSliceMean (fun σ x => (prepRequest HP).source.retains (channels 1) σ x)
      (fun σ y => (prepRequest HP).usage.retains (channels 1) σ y) completedTable x y =
    rowSliceMean (fun σ x => (prepRequest HP).source.retains (channels 1) σ x)
      (fun σ y => (prepRequest HP).usage.retains (channels 1) σ y)
      ((budgetData HP).incomingPreparation (prepRequest HP) completedTable) x y := by
  apply BudgetData.evaluate_preparation_mean (budgetData HP) 65 true ⟨0, HP.k_pos⟩
    (prepRequest HP) rfl (active HP) ((budgetData HP).childBudget_lt (by decide))
    completedTable completedTable _ (prep_evaluated HP) 0 2 (by decide) 1 0 [1] [2, 3]
    rfl rfl x y
  change (budgetData HP).evaluate 64 (budgetRequest HP) = _
  exact raw_evaluated HP

-- Normalizer congruence consumes stationarity in the actual correction formula.
-- This does not identify the separately budgeted children of an evaluated normalized parent.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (maximum : Environment 5 3 → ZMod 5 → ℝ) (σ : Environment 5 3) (x y : ZMod 5) :
    correctionRequest 1 id (prepRequest HP) (polynomialAuxCutoff4 HP.θ)
      HP.incomingCutoff HP.ρ HP.Q HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      completedTable completedTable maximum σ x y =
    correctionRequest 1 id (prepRequest HP) (polynomialAuxCutoff4 HP.θ)
      HP.incomingCutoff HP.ρ HP.Q HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      completedTable ((budgetData HP).incomingPreparation (prepRequest HP) completedTable)
      maximum σ x y := by
  apply correctionRequest_congr_normalizer 1 id (prepRequest HP)
    (admissible HP) _ _ _ _ _ _ _ _ _ _ maximum x y _ σ
  apply BudgetData.preparationWalk_mean (budgetData HP) 65 (prepRequest HP)
    0 2 (by decide) 1 0 [1] [2, 3] rfl rfl completedTable completedTable _ x y
  rw [incoming HP]
  exact completed HP

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    0 < (budgetData HP).steps 65 (prepRequest HP) 0 :=
  BudgetData.steps_pos _ _ _

-- Zero budget and inactive positive budgets reject before any child is requested.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).evaluate 0 (prepRequest HP) = none ∧
    (budgetData HP).evaluate 1 (prepRequest HP) = none := by
  constructor <;> apply BudgetData.evaluate_preparation_inactive _ _ true ⟨0, HP.k_pos⟩ _ rfl
  all_goals
    have hlog : Real.logb 2 (rate 1) = -4 := by
      simp only [rate, pow_one]
      rw [Real.logb_pow, Real.logb_inv]
      norm_num
    norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, budgetData,
      prepRequest, budgetRequest, request, gridChannel, hlog,
      show rate 0 = 1 by norm_num [rate]]

-- The actual-input counterpart uses its own child request, without a pilot substitution.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := PolynomialBudgetHistory.data HP
    let r := { PolynomialBudgetHistory.request HP with
      task := .row 0 (.preparation ⟨0, HP.k_pos⟩) }
    B.evaluate 3 r = (B.complete 3 r
      (B.incomingPreparation r (fun _ => PolynomialBudgetHistory.base))).map .row := by
  dsimp only
  apply BudgetData.evaluate_preparation _ 3 false ⟨0, HP.k_pos⟩ _ rfl
  · norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision,
      PolynomialBudgetHistory.data, PolynomialBudgetHistory.request, gridChannel, rate]
  · exact BudgetData.childBudget_lt _ (by decide)
  · change (PolynomialBudgetHistory.data HP).evaluate 2
      { PolynomialBudgetHistory.request HP with task := .row 0 (.input ⟨0, HP.k_pos⟩) } = _
    simpa only [show Nat.log2 2 + 1 = 2 by decide, le_refl, ↓reduceIte] using
      BudgetData.evaluate_initial_prefix (PolynomialBudgetHistory.data HP) 2
        { PolynomialBudgetHistory.request HP with task := .row 0 (.input ⟨0, HP.k_pos⟩) }
        false rfl rfl
        (by norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision,
          PolynomialBudgetHistory.data, PolynomialBudgetHistory.request, gridChannel, rate]) _
        (PolynomialBudgetHistory.prefixes_task HP (.row 0 (.input ⟨0, HP.k_pos⟩)))

-- Completion itself admits budget zero; evaluator inactivity is a separate boundary.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (PolynomialBudgetHistory.data HP).complete 0 (PolynomialBudgetHistory.request HP)
      (fun _ => PolynomialBudgetHistory.base) 0 = some (fun _ => PolynomialBudgetHistory.base) :=
  PolynomialBudgetHistory.complete_const HP 0 0 _

-- Literal zero samples and exhausted equal-budget pairs need no recursive child success.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).sample (fun _ _ => none) 0 (.pilotInput ⟨0, HP.k_pos⟩)
      (prepRequest HP) (some 0) = some 0 ∧
    (budgetData HP).pairedSample (fun _ _ => none) 1 1 (.pilotInput ⟨0, HP.k_pos⟩)
      (prepRequest HP) (some 0) = some 0 := by
  constructor
  · simp only [BudgetData.sample, ↓reduceIte]
  · have hf : LogSpaceEstimation.lastBudget 1 1 (budgetData HP).slack
        ((budgetData HP).sampleScale (prepRequest HP) (some 0)) = 0 := by
      unfold LogSpaceEstimation.lastBudget
      omega
    have hc : LogSpaceEstimation.lastBudget 1 2 (budgetData HP).slack
        ((budgetData HP).sampleScale (prepRequest HP) (some 0)) = 0 := by
      unfold LogSpaceEstimation.lastBudget
      omega
    simp only [BudgetData.pairedSample, hf, hc, ↓reduceIte]

-- Invalid graph frames reject, including zero-side and over-field-side boundaries.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (budgetData HP).completeAt 0 0 5 5 [1] [2, 3] 0 completedTable = none ∧
    (budgetData HP).completeAt 0 2 0 5 [1] [2, 3] 0 completedTable = none ∧
    (budgetData HP).completeAt 0 2 5 6 [1] [2, 3] 1 completedTable = none := by
  norm_num [BudgetData.completeAt]

-- This finite gate boundary deliberately uses an empty rank set. It is not an admissible
-- grid request. Even with the SAME h/rho/raw/rank set, incoming PREP can be zero while
-- dense atomPrep is one; the selected-preparation payments cannot identify these formulas.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let Kc := ⌈4 * (1 + 32 * HP.R)⌉₊
    let V := Fin (Kc + 1)
    let G : Matrix V V ℝ := fun _ _ => 1
    let z : V := 0
    correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc 1 G
      (polynomialPrepCutoff4 HP.θ) HP.ρ univ ∅ z z = 0 ∧
    atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1 G ∅ z z = 1 := by
  dsimp only
  let Kc := ⌈4 * (1 + 32 * HP.R)⌉₊
  let V := Fin (Kc + 1)
  let G : Matrix V V ℝ := fun _ _ => 1
  have hk : 0 < HP.K := (large_K HP).trans' (by decide)
  have hc : 0 < Kc := (large_Kc HP).trans' (by decide)
  have hrank (x : V) : kthLargest HP.K (∅ : Finset V) (fun w => G x w / 1) = 0 :=
    kthLargest_eq_zero_of_card_lt (by simpa using hk) _
  have haux (x y : V) : auxScore (polynomialAuxCutoff4 HP.θ) HP.K 1 G ∅ x y = 1 := by
    rw [auxScore, hrank x]
    apply polynomialAuxCutoff4_eq_one HP.θ_pos
    · simp only [G, div_one]
      linarith [HP.θ_lt_θ₂, HP.θ₂_lt]
    · linarith [HP.θ_pos]
  have hgate (y : V) : incomingGate (polynomialAuxCutoff4 HP.θ)
      HP.incomingCutoff HP.K Kc 1 G univ ∅ y = 0 := by
    apply incomingGate_eq_zero hc (g := HP.τ₁)
      (by rw [HP.τ₁_eq]; norm_num) (fun r hr => HP.incomingCutoff_zero hr)
    simp only [haux, le_refl, filter_true, card_univ]
    change Kc ≤ Fintype.card (Fin (Kc + 1))
    rw [Fintype.card_fin]
    omega
  constructor
  · rw [correctionPrep, hgate, mul_zero]
  · rw [atomPrep, rowGate, hrank (0 : V), HP.ρ_one 0 HP.η_pos.le, mul_one]
    apply polynomialPrepCutoff4_eq_one HP.θ_pos
    norm_num only [div_one]
    linarith [HP.θ_lt_θ₂, HP.θ₂_lt]

end PreparationExecutionRegression
