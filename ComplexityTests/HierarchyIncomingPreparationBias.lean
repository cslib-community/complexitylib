/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of incoming PREP normalizer bias)
import Complexity.Foundations.Probability.HierarchyIncomingPreparationBias
import all ComplexityTests.HierarchyPreparationExecution

/-!
A singleton half-bin produces an actually evaluated nonconstant RAW child with a positive
error against its nonzero canonical input. PREP uses that literal child. The supplied finite
bin configuration is not the exhaustive polynomial-bin family of the joint depth theorem;
these execution and own-error tests do not establish a recursively available IH.
-/
set_option linter.privateModule false
noncomputable section
open scoped BigOperators
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open InitialPilotScoreRegression
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace IncomingPreparationBiasRegression

private def halfData (HP : FourthRootHierarchyParams 16 1 16 32 8) : BudgetData HP 5 :=
  { budgetData HP with bins := {0} }

private lemma half_initial (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin : ℕ) :
    (halfData HP).initialSample (budgetRequest HP) bin = fun _ x y => base x y / 2 :=
  shared_initial HP bin

private lemma half_complete_const (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M : ℕ) (A : Matrix (ZMod 5) (ZMod 5) ℝ) (slack : ℕ := 0) :
    (halfData HP).complete M (budgetRequest HP) (fun _ => A) slack =
      some (fun σ x y => if source σ x then A x y else 0) :=
by
  rw [BudgetData.complete_grid _ M _ 0 2 (by decide) 1 0 [1] [2, 3] rfl rfl _ slack]
  apply congrArg some
  funext σ x y
  rw [conditionalWalk_const]
  have ht : Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier (1 : ZMod 5) [2, 3]) σ y := by
    simpa only [Y, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 2) _
  simp only [show (halfData HP).padding = 1 from rfl, ht, and_true]
  rfl

private def halfTable : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ :=
  fun σ x y => if source σ x then base x y / 2 else 0

private lemma precision (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) :
    (halfData HP).requestPrecision M (budgetRequest HP) = (M : ℝ) / 16 - 2 := by
  rw [BudgetData.requestPrecision_grid _ M 1 0 _ rfl rfl]
  norm_num [halfData, budgetData]

private lemma half_scheduled (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).raw
      (fun m r => if m < 33 then (halfData HP).evaluate m r else none)
      33 (.pilotInput ⟨0, HP.k_pos⟩) (budgetRequest HP) =
      some (fun σ x y => if source σ x then base x y / 2 else 0) := by
  have hs (bin : ℕ) :
      (halfData HP).sampleScale (budgetRequest HP) (some bin) = 0 := by
    norm_num [BudgetData.sampleScale, budgetData, budgetRequest, request, gridChannel, rate,
      halfData]
  have hc (a b : ℕ) :
      ((if a = 0 then 0 else fun (_ : Environment 5 3) x y => base x y / 2) -
        (if b = 0 then 0 else fun (_ : Environment 5 3) x y => base x y / 2)) =
      fun (_ : Environment 5 3) x y =>
        (if a = 0 then 0 else base x y / 2) - (if b = 0 then 0 else base x y / 2) := by
    funext σ x y
    split_ifs <;> rfl
  have hm (l : List ℕ) (f : ℕ → Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) :
      l.mapM (fun x => some (f x)) = some (l.map f) := List.mapM_pure
  have he : ((halfData HP).rays (.pilotInput ⟨0, HP.k_pos⟩)).isEmpty = false := by
    simp [BudgetData.rays, halfData]
  unfold BudgetData.raw BudgetData.completedGroup
  simp only [he]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [BudgetData.rays, List.append_nil, List.mapM_map]
  dsimp only [Function.comp_def]
  simp_rw [BudgetData.pairedSample_initial _ 33 _ (by decide), half_initial, hs]
  simp_rw [hc]
  simp only [bind, pure]
  simp_rw [hm]
  simp only [Option.bind_some]
  simp_rw [List.map_map]
  dsimp only [Function.comp_def]
  simp_rw [half_complete_const]
  simp_rw [hm]
  simp only [Option.bind_some]
  norm_num [List.range_succ, Cslib.RowCompression.dyadicSlack, bind, pure, budgetData,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, halfData]

private lemma half_evaluated (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).evaluate 33 (budgetRequest HP) = some (.row halfTable) := by
  rw [BudgetData.evaluate_eq]
  have hp : 0 < (halfData HP).requestPrecision 33 (budgetRequest HP) := by
    rw [precision]; norm_num
  simp only [BudgetData.step,
    show (budgetRequest HP).task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) from rfl,
    hp, ↓reduceIte]
  rw [half_scheduled HP]
  rfl


private lemma canonical_zero (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (pilot : Bool) :
    (halfData HP).canonicalPreparationInput pilot ⟨0, HP.k_pos⟩
      (PreparationExecutionRegression.prepRequest HP) = base := by
  cases pilot
  · simp [BudgetData.canonicalPreparationInput, HierarchyParams.correctionInput,
      HierarchyParams.correctionIter, cutoffCorrectionIter, halfData, budgetData]
  · simp [BudgetData.canonicalPreparationInput, PilotTask.value, pilotInput,
      pilotCorrection_zero, halfData, budgetData]

private lemma own_moment (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rowNormPow 4 5 (rate 1) source
      (fun σ y => (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ y)
      (fun σ x y => halfTable σ x y - base x y) = 81 / 625 := by
  let U := fun σ y => (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ y
  have ht (σ : Environment 5 3) (y : ZMod 5) : U σ y := by
    simp only [U, budgetRequest, request, gridChannel, CorrectionRowTask.Channel.retains,
      channels, semanticSide_grid]
    simpa only [show side 5 0 = 5 by norm_num [side]] using full_retains (σ 2) _
  have he (σ : Environment 5 3) :
      (∑ x ∈ ({x | source σ x} : Finset (ZMod 5)), ∑ y ∈ ({y | U σ y} : Finset _),
        |halfTable σ x y - base x y| ^ 4) =
      (1 / 16 : ℝ) * ∑ x ∈ ({x | source σ x} : Finset (ZMod 5)), (1 : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    simp only [ht, filter_true, halfTable, (mem_filter.mp hx).2, ↓reduceIte]
    simp only [base, Matrix.one_apply]
    have hv (y : ZMod 5) :
        |(if x = y then (1 : ℝ) else 0) / 2 - (if x = y then 1 else 0)| ^ 4 =
          if x = y then (1 / 16 : ℝ) else 0 := by
      split_ifs <;> norm_num
    simp_rw [hv]
    simp
  have hd (x : ZMod 5) :
      (dens {σ : Environment 5 3 | source σ x} : ℝ) = 81 / 625 := by
    have h := density (P := 5) (0 : Fin 3) (side 5 1) (side_le 5 1)
      (CopyPadding.identifier (1 : ZMod 5) [1] x)
    norm_num [source, X, roles, show side 5 1 = 3 by decide] at h ⊢
    exact h
  change (5 * rate 1)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | source σ x} : Finset (ZMod 5)),
    ∑ y ∈ ({y | U σ y} : Finset _), |halfTable σ x y - base x y| ^ 4 = _
  simp_rw [he]
  rw [← mul_expect]
  simp only [sum_filter]
  rw [expect_sum_comm]
  have hm (x : ZMod 5) :
      (𝔼 σ : Environment 5 3, if source σ x then (1 : ℝ) else 0) = 81 / 625 := by
    have h := expect_mask_const ({σ : Environment 5 3 | source σ x} : Finset _) (1 : ℝ)
    simpa only [mem_filter, mem_univ, true_and, hd, mul_one] using h
  simp only [hm, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  norm_num [rate]

private lemma own_accuracy (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rowNormPow 4 5 (rate 1) source
      (fun σ y => (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ y)
      (fun σ x y => halfTable σ x y - base x y) ≤
      ((2 : ℝ) ^ (-(halfData HP).requestPrecision 33 (budgetRequest HP))) ^ 4 := by
  rw [own_moment, precision]
  norm_num only [Nat.cast_ofNat]
  have hp : (1 / 2 : ℝ) ≤ ((2 : ℝ) ^ (-(33 / 16 - 2 : ℝ))) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact (by norm_num : (81 / 625 : ℝ) ≤ 1 / 2).trans (by norm_num at hp ⊢; exact hp)

-- Positive error is measured on the child's OWN retained source and usage masks.
-- Outside source, the approximate table is zero while its canonical reference is nonzero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).evaluate 33 (budgetRequest HP) = some (.row halfTable) ∧
    halfTable (seed 0) 0 0 = 1 / 2 ∧ halfTable (seed 4) 0 0 = 0 ∧
    base 0 0 = 1 ∧ 0 < (81 / 625 : ℝ) ∧
    rowNormPow 4 5 (rate 1) source
      (fun σ y => (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ y)
      (fun σ x y => halfTable σ x y - base x y) = 81 / 625 := by
  refine ⟨half_evaluated HP, ?_, ?_, ?_, by norm_num, own_moment HP⟩
  · simp [halfTable, source_both.1, base]
  · simp only [halfTable, source_both.2, ↓reduceIte]
  · simp [base]

private lemma prep_completed (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).complete 34 (PreparationExecutionRegression.prepRequest HP) completedTable =
      some completedTable := by
  rw [BudgetData.complete_grid _ 34 _ 0 2 (by decide) 1 0 [1] [2, 3] rfl rfl]
  apply congrArg some
  funext σ x y
  dsimp only [halfData, budgetData]
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


private lemma half_incoming (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).incomingPreparation (PreparationExecutionRegression.prepRequest HP)
      halfTable = completedTable := by
  funext σ x y
  unfold BudgetData.incomingPreparation correctionPrep rowGate incomingGate
  rw [kthLargest_eq_zero_of_card_lt
    ((card_filter_le _ _).trans_lt (by simpa using large_K HP)),
    kthLargest_eq_zero_of_card_lt
      ((card_filter_le _ _).trans_lt (by simpa using large_Kc HP))]
  rw [HP.ρ_one 0 HP.η_pos.le,
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)]
  simp only [mul_one]
  change polynomialPrepCutoff4 HP.θ (halfTable σ x y / rate 0) = completedTable σ x y
  rw [show rate 0 = 1 by norm_num [rate], div_one]
  by_cases hs : source σ x
  · simp only [halfTable, completedTable, hs, ↓reduceIte]
    by_cases hxy : x = y
    · subst y
      simp only [base, Matrix.one_apply_eq]
      exact polynomialPrepCutoff4_eq_one HP.θ_pos
        (by linarith [HP.θ_lt_θ₂, HP.θ₂_lt])
    · simp only [base, Matrix.one_apply_ne hxy, zero_div]
      exact polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos])
  · simp only [halfTable, completedTable, hs, ↓reduceIte]
    exact polynomialPrepCutoff4_eq_zero HP.θ_pos (by linarith [HP.θ_pos])

private lemma prep_active (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    0 < (halfData HP).requestPrecision 34 (PreparationExecutionRegression.prepRequest HP) := by
  rw [BudgetData.requestPrecision_grid _ 34 1 0 _ rfl rfl]
  norm_num [halfData, budgetData]

private lemma prep_evaluated (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).evaluate 34 (PreparationExecutionRegression.prepRequest HP) =
      some (.row completedTable) := by
  rw [BudgetData.evaluate_preparation _ 34 true ⟨0, HP.k_pos⟩ _ rfl (prep_active HP)
    ((halfData HP).childBudget_lt (by decide)) halfTable]
  · rw [half_incoming, prep_completed]
    rfl
  · exact half_evaluated HP

-- This consumer supplies an actual changed-task own IH, not the residual-zero IH.
private lemma bias_accuracy (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 5 r.source.rate X U (fun _ x y => rowSliceMean X U completedTable x y -
      rowSliceMean X U (B.incomingPreparation r
        (fun _ => B.canonicalPreparationInput true ⟨0, HP.k_pos⟩ r)) x y) ≤
      (L / r.terminal.rate) ^ 4 * (5 : ℝ) ^ 2 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget 34) (budgetRequest HP))) ^ 4 := by
  obtain ⟨L, hL, h⟩ := BudgetData.evaluate_preparation_bias (HP := HP)
  refine ⟨L, hL, ?_⟩
  apply h 5 (halfData HP) 34 true ⟨0, HP.k_pos⟩
    (PreparationExecutionRegression.prepRequest HP) rfl (prep_active HP)
    ((halfData HP).childBudget_lt (by decide)) rfl (rate_pos 1).le (rate_pos 0)
    halfTable completedTable _ (half_evaluated HP) (prep_evaluated HP) _
    0 2 (by decide) 1 0 [1] [2, 3] rfl rfl
  · change 0 < (halfData HP).requestPrecision 33 (budgetRequest HP)
    rw [precision]
    norm_num
  · rw [canonical_zero]
    change rowNormPow 4 5 (rate 1)
      (fun σ x => (budgetRequest HP).source.retains (channels (1 : ZMod 5)) σ x)
      (fun σ y => (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ y)
      (fun σ x y => halfTable σ x y - base x y) ≤
        ((2 : ℝ) ^ (-(halfData HP).requestPrecision 33 (budgetRequest HP))) ^ 4
    have hmask : (fun σ x => (budgetRequest HP).source.retains
        (channels (1 : ZMod 5)) σ x) = source := by
      funext σ x
      simp only [budgetRequest, request, gridChannel, CorrectionRowTask.Channel.retains,
        channels, semanticSide_grid, source, X, roles]
    simpa only [hmask] using own_accuracy HP

-- Actual normalizer sensitivity is applied to the returned PREP, with the same RAW
-- and maximum held fixed. It makes no claim about a separately budgeted normalized parent.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : Environment 5 3) (x y : ZMod 5),
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let V := B.incomingPreparation r
      (fun _ => B.canonicalPreparationInput true ⟨0, HP.k_pos⟩ r)
    |correctionRequest B.padding id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        halfTable completedTable (fun _ _ => 0) σ x y ^ (4⁻¹ : ℝ) -
      correctionRequest B.padding id r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        halfTable V (fun _ _ => 0) σ x y ^ (4⁻¹ : ℝ)| ≤
    C * |rowSliceMean (fun τ z => r.source.retains (channels B.padding) τ z)
        (fun τ z => r.usage.retains (channels B.padding) τ z) completedTable x y -
      rowSliceMean (fun τ z => r.source.retains (channels B.padding) τ z)
        (fun τ z => r.usage.retains (channels B.padding) τ z) V x y| := by
  obtain ⟨C, hC, h⟩ := BudgetData.correctionRequest_normalizer_root_le (HP := HP)
  refine ⟨C, hC, ?_⟩
  intro σ x y
  exact h 5 (halfData HP) (PreparationExecutionRegression.prepRequest HP)
    (admissible HP) (rate_pos 0) halfTable completedTable _ (fun _ _ => 0) σ x y

-- The rooted normalized consumer combines actual RAW33/PREP34 execution, own
-- positive error and stationarity. RAW and maximum are held fixed throughout.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let V := B.incomingPreparation r
      (fun _ => B.canonicalPreparationInput true ⟨0, HP.k_pos⟩ r)
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      halfTable prep (fun _ _ => 0)
    rootDistPow 4 5 r.source.rate X U (output completedTable) (output V) ≤
      C ^ 4 * ((L / r.terminal.rate) ^ 4 * (5 : ℝ) ^ 2 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget 34) (budgetRequest HP))) ^ 4) := by
  obtain ⟨C, hC, hc⟩ := BudgetData.correctionRequest_normalizer_root_moment_le (HP := HP)
  obtain ⟨L, hL, hb⟩ := bias_accuracy HP
  refine ⟨C, L, hC, hL, ?_⟩
  exact (hc 5 (halfData HP) (PreparationExecutionRegression.prepRequest HP)
    (admissible HP) (rate_pos 1).le (rate_pos 0) halfTable completedTable _
    (fun _ _ => 0)).trans (mul_le_mul_of_nonneg_left hb (pow_nonneg hC 4))

-- Both task changes retain the exact budget loss and have different computed rank gaps.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (B : BudgetData HP 5)
    (M : ℕ) (pilot : Bool) :
    let r := { (budgetRequest HP) with task := (.row 0
      (if pilot then .pilotPreparation ⟨0, HP.k_pos⟩ else .preparation ⟨0, HP.k_pos⟩)) }
    let q := { r with task := (.row 0
      (if pilot then .pilotInput ⟨0, HP.k_pos⟩ else .input ⟨0, HP.k_pos⟩)) }
    B.requestPrecision (B.childBudget M) q - B.requestPrecision M r =
      ((B.childBudget M : ℕ) - (M : ℝ)) / (16 * B.slack) +
        B.rankCharge * (if pilot then 40 else 4) :=
  B.requestPrecision_preparation_input M (B.childBudget M) pilot ⟨0, HP.k_pos⟩ _ rfl

-- The retained conservative coefficient does NOT fit this legitimate positive fixture's
-- nominal salary. This disproves that sufficient payment, not the actual PREP bias bound.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ¬ ((5 : ℝ) ^ 2 * ((2 : ℝ) ^
      (-(halfData HP).requestPrecision 33 (budgetRequest HP))) ^ 4 ≤
      ((2 : ℝ) ^ (-(halfData HP).requestPrecision 34
        (PreparationExecutionRegression.prepRequest HP))) ^ 4) := by
  rw [BudgetData.preparation_bias_salary_iff]
  have hd := (halfData HP).requestPrecision_preparation_input 34 33 true
    ⟨0, HP.k_pos⟩ (PreparationExecutionRegression.prepRequest HP) rfl
  change (halfData HP).requestPrecision 33 (budgetRequest HP) -
    (halfData HP).requestPrecision 34 (PreparationExecutionRegression.prepRequest HP) = _ at hd
  rw [hd]
  norm_num only [halfData, budgetData, Nat.cast_ofNat, Nat.cast_one, mul_one,
    div_one, zero_mul, add_zero, sub_self, zero_add]
  have hh : (2 : ℝ) ^ (4 * ((33 : ℝ) - 34) / 16) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  norm_num at hh ⊢
  linarith

end IncomingPreparationBiasRegression
