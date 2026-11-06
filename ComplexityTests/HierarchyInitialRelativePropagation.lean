/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of executed initial relative propagation)
import Complexity.Foundations.Probability.HierarchyInitialRelativePropagation
import all ComplexityTests.HierarchyCanonicalRange

/-!
The nonconstant RAW33/PREP34 half-bin fixture now derives its relative allowance
from actual lower-budget dense/zero-correction calls and the literal finite payment.
The source rate is 1/16, terminal/usage rate 1, with distinct nonempty suffixes.
The canonical base is the identity, hence aligned. Own error is positive; the
stationary fixture has zero centered completion noise and a persistent mean deficit.
This is a finite initial-edge consumer, not a supplied-history recursive IH.
Imported rate-family and later-range counterexamples preserve both obstructions.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open InitialPilotScoreRegression IncomingPreparationBiasRegression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace InitialRelativePropagationRegression

private def terminal (σ : Environment 5 3) (y : ZMod 5) : Prop :=
  Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier 1 [2, 3]) σ y

private lemma terminal_full (σ : Environment 5 3) (y : ZMod 5) : terminal σ y := by
  simpa only [terminal, Y, show side 5 0 = 5 by norm_num [side]] using full_retains (σ 2) _

private lemma slice_nonempty (x y : ZMod 5) :
    ({σ : Environment 5 3 | source σ x ∧ terminal σ y} : Finset _).Nonempty := by
  have hd := density (P := 5) (0 : Fin 3) (side 5 1) (side_le 5 1)
    (CopyPadding.identifier (1 : ZMod 5) [1] x)
  have hd' : (dens {σ : Environment 5 3 | source σ x} : ℝ) = 81 / 625 := by
    norm_num [source, X, roles, show side 5 1 = 3 by decide] at hd ⊢
    exact hd
  have hn : ({σ : Environment 5 3 | source σ x} : Finset _).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h, dens_empty] at hd'
    norm_num at hd'
  simpa only [terminal_full, and_true] using hn

private lemma mean_const (A : Matrix (ZMod 5) (ZMod 5) ℝ) (x y : ZMod 5) :
    rowSliceMean source terminal (fun _ => A) x y = A x y :=
  Finset.expect_const (slice_nonempty x y) _

private lemma group_const (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M d : ℕ) (σ τ : Environment 5 3) (x y : ZMod 5) :
    (halfData HP).initialGroupInput M d (budgetRequest HP) σ x y =
      (halfData HP).initialGroupInput M d (budgetRequest HP) τ x y := by
  simp only [BudgetData.initialGroupInput, half_initial]

private lemma group_mean (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (M d : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    rowSliceMean source terminal ((halfData HP).initialGroupInput M d (budgetRequest HP)) x y =
      (halfData HP).initialGroupInput M d (budgetRequest HP) σ x y := by
  unfold rowSliceMean
  rw [expect_congr rfl (fun τ _ => group_const HP M d τ σ x y)]
  exact Finset.expect_const (slice_nonempty x y) _

private lemma noise_zero (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).initialRelativeNoiseBudget 33 (budgetRequest HP)
      0 2 (by decide) 1 0 [1] [2, 3] base 6 = 0 := by
  have hu : {budgetRequest HP with usage := (budgetRequest HP).terminal} = budgetRequest HP := rfl
  have hX : retainedMask (0 : Fin 3) (side 5 1) (halfData HP).padding [1] = source := rfl
  have hU : retainedMask (2 : Fin 3) (side 5 0) (halfData HP).padding [2, 3] = terminal := rfl
  simp only [BudgetData.initialRelativeNoiseBudget, hu, hX, hU]
  have hz (d : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
      (halfData HP).initialGroupInput 33 d (budgetRequest HP) σ x y -
        rowSliceMean source terminal ((halfData HP).initialGroupInput 33 d
          (budgetRequest HP)) x y = 0 := by rw [group_mean HP 33 d σ]; exact sub_self _
  simp_rw [hz]
  simp

private lemma final_input (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).initialFinalInput 33 (budgetRequest HP) = fun _ x y => base x y / 2 := by
  have hs : (halfData HP).sampleScale (budgetRequest HP) (some 0) = 0 := by
    norm_num [BudgetData.sampleScale, halfData, budgetData, budgetRequest, request,
      gridChannel, rate]
  funext σ x y
  simp only [BudgetData.initialFinalInput, show (halfData HP).bins = {0} from rfl,
    sum_singleton, hs, half_initial]
  norm_num [Cslib.RowCompression.dyadicSlack, LogSpaceEstimation.lastBudget,
    LogSpaceEstimation.scaleCutoff, halfData, budgetData]

-- This derives the scalar payment from actual bin means, rather than using a
-- relative RAW accuracy hypothesis to pay the same desired conclusion.
private lemma payment_bound (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).initialRawRelativePayment 33 (budgetRequest HP)
      0 2 (by decide) 1 0 [1] [2, 3] ≤ 81 / 1250 := by
  have hm : rowNormPow 4 5 (rate 1) source terminal
      (fun _ x y => (base x y / 2 - base x y) / (1 + base x y)) ≤ 81 / 10000 := by
    have h := rowNormPow_le_mul (s := 4) (N := 5) (u := rate 1) (X := source) (Y := terminal)
      (c := (1 / 16 : ℝ)) (mul_nonneg (by norm_num) (rate_pos 1).le)
      (Z := fun (_ : Environment 5 3) x y =>
        (base x y / 2 - base x y) / (1 + base x y))
      (Z' := fun σ x y => halfTable σ x y - base x y) ?_
    · have ho := own_moment HP
      have hu' : (fun σ y => (budgetRequest HP).usage.retains
          (channels (1 : ZMod 5)) σ y) = terminal := by
        funext σ y
        simp only [budgetRequest, request, gridChannel, CorrectionRowTask.Channel.retains,
          channels, semanticSide_grid, terminal, Y]
      simp only [hu'] at ho
      rw [ho] at h
      exact h.trans_eq (by norm_num)
    · intro σ x y hx _
      simp only [halfTable, hx, ↓reduceIte, base, Matrix.one_apply]
      split_ifs <;> norm_num
  have hX : retainedMask (0 : Fin 3) (side 5 1) (halfData HP).padding [1] = source := rfl
  have hU : retainedMask (2 : Fin 3) (side 5 0) (halfData HP).padding [2, 3] = terminal := rfl
  have hu : {budgetRequest HP with usage := (budgetRequest HP).terminal} = budgetRequest HP := rfl
  have hbase : (halfData HP).base = base := rfl
  simp only [BudgetData.initialRawRelativePayment, hbase, show Nat.log2 33 + 1 = 6 from rfl,
    noise_zero, zero_add, hX, hU, hu, final_input, mean_const]
  change 8 * rowNormPow 4 5 (rate 1) source terminal
    (fun _ x y => (base x y / 2 - base x y) / (rate 0 + base x y)) ≤ _
  rw [show rate 0 = 1 by norm_num [rate]]
  linarith

private lemma scalar_paid (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (halfData HP).initialRawRelativePayment 33 (budgetRequest HP)
      0 2 (by decide) 1 0 [1] [2, 3] ≤
      ((2 : ℝ) ^ (-(halfData HP).requestPrecision 33 (budgetRequest HP))) ^ 4 := by
  apply (payment_bound HP).trans
  rw [precision]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_trans (b := (2 : ℝ) ^ (-1 : ℝ)) (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

-- The lower child is a genuine nonconstant evaluated table with nonzero own error.
-- Both source seeds, positive precision and actual RAW33/PREP34 remain checked.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    0 < (halfData HP).requestPrecision 33 (budgetRequest HP) ∧
    halfTable (seed 0) 0 0 = 1 / 2 ∧ halfTable (seed 4) 0 0 = 0 ∧
    rowNormPow 4 5 (rate 1) source terminal
      (fun σ x y => halfTable σ x y - base x y) = 81 / 625 := by
  have ho := own_moment HP
  have hu' : (fun σ y => (budgetRequest HP).usage.retains
      (channels (1 : ZMod 5)) σ y) = terminal := by
        funext σ y
        simp only [budgetRequest, request, gridChannel, CorrectionRowTask.Channel.retains,
          channels, semanticSide_grid, terminal, Y]
  simp only [hu'] at ho
  refine ⟨?_, ?_, ?_, ho⟩
  · rw [precision]; norm_num
  · simp [halfTable, source_both.1, base]
  · simp only [halfTable, source_both.2, ↓reduceIte]

-- At the actual final positive endpoint, direct/right are executed dense leaves
-- and left is the executed zero correction. Their own-mask rooted errors vanish.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := halfData HP
    let r := budgetRequest HP
    let Q := HierarchyTask.rawRequests 0 0 (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (BudgetData.midpoint r) r.terminal (B.binRate 0)
    let A := denseChild B.padding id Q.direct (B.cutoff 0) (B.auxiliary 0)
      HP.ρ HP.K B.base
    32 < 33 ∧ B.evaluate 32 Q.direct = some (.row A) ∧
      B.evaluate 32 Q.left = some (.row 0) ∧ Q.negative = none ∧
      Q.right.source = BudgetData.midpoint r ∧
      rootDistPow 4 5 Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) A A = 0 := by
  dsimp only
  refine ⟨by decide, BudgetData.evaluate_dense _ 32 0 (by decide) _ rfl,
    BudgetData.evaluate_pilotCorrection_zero _ 32 _ rfl, rfl, rfl, ?_⟩
  exact rootDistPow_self (by decide) _

-- The literal exhausted coarse endpoint is zero, even against a nonzero reference.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    LogSpaceEstimation.lastBudget 33 (2 * Cslib.RowCompression.dyadicSlack 6 0)
      (halfData HP).slack 0 = 0 ∧
    (halfData HP).sample (fun _ _ => none) 0 (.pilotInput ⟨0, HP.k_pos⟩)
      (budgetRequest HP) (some 0) = some 0 := by
  constructor
  · norm_num [Cslib.RowCompression.dyadicSlack, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff, halfData, budgetData]
  · exact BudgetData.sample_zero _ _ _ _ _

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    ∃ A W, B.evaluate 33 (budgetRequest HP) = some (.row A) ∧
      B.evaluate 34 r = some (.row W) ∧
      ∀ (raw : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)
        (maximum : Environment 5 3 → ZMod 5 → ℝ),
      let output := fun prep => correctionRequest B.padding id r
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
        HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
      rootDistPow 4 5 r.source.rate X U (output W)
        (output (B.incomingPreparation r (fun _ => base))) ≤
        HP.Q HP.toHierarchyParams.atomCap / 8 * (L * (1 + ((HP.k : ℝ) + 1))) ^ 4 *
          ((2 : ℝ) ^ (-B.requestPrecision 33 (budgetRequest HP))) ^ 4 := by
  obtain ⟨L, hL, h⟩ := BudgetData.evaluate_initial_preparation_relative_root (HP := HP)
  refine ⟨L, hL, ?_⟩
  have hp : 0 < (halfData HP).requestPrecision 33 (budgetRequest HP) := by rw [precision]; norm_num
  obtain ⟨A, W, hA, hW, _, hout⟩ := h 5 (halfData HP) 34 true
    (PreparationExecutionRegression.prepRequest HP) rfl (admissible HP) (prep_active HP)
    (by change 0 < 33; decide) ((halfData HP).childBudget_lt (by decide)) rfl 0 2 (by decide)
    1 0 [1] [2, 3] rfl rfl (by exact ⟨0, mem_singleton_self _⟩)
    (fun x y => by by_cases hxy : x = y <;> norm_num [halfData, budgetData, base,
      Matrix.one_apply, hxy])
    (by change (1 : Matrix (ZMod 5) (ZMod 5) ℝ) *ᵥ 1 ≤ 1; simp)
    (fun x y => by by_cases hxy : x = y <;>
      norm_num [halfData, budgetData, base, PreparationExecutionRegression.prepRequest,
        budgetRequest, request, gridChannel, rate, Matrix.one_apply, hxy]) hp
    ((2 : ℝ) ^ (-(halfData HP).requestPrecision 33 (budgetRequest HP))) (scalar_paid HP)
  exact ⟨A, W, hA, hW, hout⟩

end InitialRelativePropagationRegression
