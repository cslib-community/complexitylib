/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of sparse incoming PREP payment)
import Complexity.Foundations.Probability.HierarchyPreparationPayment
import all ComplexityTests.HierarchyPreparationGates
import all ComplexityTests.HierarchyPreparationSalary

/-!
Actual nonconstant RAW33/PREP34 consumes the general field-free payment and original
root decoder with nonzero own error against its genuine canonical reference. Generic
one-open/both-open and both-closed regressions remain in the imported gate test.
The growing-field test uses exhaustive nonempty production polynomial bins; its
pointwise payment requires no recursive success assumption. Successful executions of
that exhaustive family and the numerical recursive salary are not asserted.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open InitialPilotScoreRegression IncomingPreparationBiasRegression
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace PreparationPaymentRegression

private lemma paid_bias (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 5 r.source.rate X U (fun _ x y => rowSliceMean X U completedTable x y -
      rowSliceMean X U (B.incomingPreparation r
        (fun _ => B.canonicalPreparationInput true ⟨0, HP.k_pos⟩ r)) x y) ≤
      (L / r.terminal.rate) ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget 34) (budgetRequest HP))) ^ 4 := by
  obtain ⟨L, hL, h⟩ := BudgetData.evaluate_preparation_paid_bias (HP := HP)
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

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    let V := B.incomingPreparation r (fun _ => base)
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      halfTable prep (fun _ _ => 0)
    (halfData HP).evaluate 33 (budgetRequest HP) = some (.row halfTable) ∧
    rootDistPow 4 5 (rate 1) source U (output completedTable) (output V) ≤
      C ^ 4 * (K ^ 4 * ((2 : ℝ) ^
        (-B.requestPrecision 33 (budgetRequest HP))) ^ 4) := by
  obtain ⟨C, hC, hc⟩ := BudgetData.correctionRequest_normalizer_root_moment_le (HP := HP)
  obtain ⟨K, hK, hg⟩ := paid_bias HP
  have hb :
      let B := halfData HP
      let r := PreparationExecutionRegression.prepRequest HP
      let U := fun σ y => r.usage.retains (channels B.padding) σ y
      rowNormPow 4 5 (rate 1) source U (fun _ x y =>
        rowSliceMean source U completedTable x y -
        rowSliceMean source U (B.incomingPreparation r (fun _ => base)) x y) ≤
        K ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision 33 (budgetRequest HP))) ^ 4 := by
    have hX : (fun σ x => (PreparationExecutionRegression.prepRequest HP).source.retains
        (channels (halfData HP).padding) σ x) = source := by
      funext σ x
      simp only [PreparationExecutionRegression.prepRequest, budgetRequest, request,
        gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
        source, X, roles, halfData, budgetData]
    simp only [hX] at hg
    have hf : (PreparationExecutionRegression.prepRequest HP).terminal.rate = 1 := by
      norm_num [PreparationExecutionRegression.prepRequest, budgetRequest, request,
        gridChannel, rate]
    have hs : (PreparationExecutionRegression.prepRequest HP).source.rate = rate 1 := rfl
    have hchild : (halfData HP).childBudget 34 = 33 := rfl
    simpa only [canonical_zero, hf, hs, hchild, div_one] using hg
  refine ⟨C, K, hC, hK, half_evaluated HP, ?_⟩
  have h := hc 5 (halfData HP) (PreparationExecutionRegression.prepRequest HP)
    (admissible HP) (rate_pos 1).le (rate_pos 0) halfTable completedTable
    ((halfData HP).incomingPreparation (PreparationExecutionRegression.prepRequest HP)
      (fun _ => base)) (fun _ _ => 0)
  have hX : (fun σ x => (PreparationExecutionRegression.prepRequest HP).source.retains
      (channels (halfData HP).padding) σ x) = source := by
    funext σ x
    simp only [PreparationExecutionRegression.prepRequest, budgetRequest, request,
      gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
      source, X, roles, halfData, budgetData]
  simp only [hX, Nat.cast_ofNat] at h
  exact h.trans (mul_le_mul_of_nonneg_left hb (pow_nonneg hC 4))

-- Fixed HP and its two caps precede arbitrarily large prime fields. Unlike the
-- execution fixture above, these data have the exhaustive production polynomial
-- bins and original dyadic rates. The inequality is unconditional for every signed
-- A and the genuine canonical input, not contingent on the existence of a successful
-- recursive run. This does not claim that such runs are jointly available.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ, ∃ P : ℕ, P.Prime ∧ N < P ∧ HP.K < P ∧
      ⌈4 * (1 + 32 * HP.R)⌉₊ < P ∧
      ∀ (hP : Fact P.Prime),
      letI := hP
      let B := PreparationSalaryRegression.data HP P N 1
      let r := PreparationSalaryRegression.request HP P true
      B.bins = range (N + 1) ∧ B.bins.Nonempty ∧
      ∀ (A : Matrix (ZMod P) (ZMod P) ℝ) (pilot : Bool),
      (∑ x : ZMod P, ∑ y : ZMod P,
        |correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
            ⌈4 * (1 + 32 * HP.R)⌉₊ 1 A (polynomialPrepCutoff4 HP.θ) HP.ρ univ univ x y -
          correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
            ⌈4 * (1 + 32 * HP.R)⌉₊ 1
            (B.canonicalPreparationInput pilot ⟨0, HP.k_pos⟩ r)
            (polynomialPrepCutoff4 HP.θ) HP.ρ univ univ x y| ^ 4) ≤
        L ^ 4 * ∑ x : ZMod P, ∑ y : ZMod P,
          |A x y - B.canonicalPreparationInput pilot ⟨0, HP.k_pos⟩ r x y| ^ 4 := by
  obtain ⟨L, hL, h⟩ := HP.preparation_fourth_sum
  let Kc := ⌈4 * (1 + 32 * HP.R)⌉₊
  refine ⟨L * (1 + Kc), by positivity, ?_⟩
  intro N
  obtain ⟨P, hbig, hprime⟩ := Nat.exists_infinite_primes (max N (max HP.K Kc) + 1)
  refine ⟨P, hprime, by omega, by omega, by dsimp only [Kc] at hbig; omega, ?_⟩
  intro hP
  let := hP
  refine ⟨rfl, ⟨0, by simp [PreparationSalaryRegression.data]⟩, ?_⟩
  intro A pilot
  have hc : 0 < Kc := Nat.ceil_pos.mpr (by linarith [HP.R_var])
  simpa only [div_one] using h (ZMod P) Kc hc 1 (by norm_num) A
    ((PreparationSalaryRegression.data HP P N 1).canonicalPreparationInput pilot
      ⟨0, HP.k_pos⟩ (PreparationSalaryRegression.request HP P true)) univ univ

-- Empty retained sets remain valid boundary cases of the same general payment.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (Kc : ℕ) (f : ℝ)
    (A B : Matrix Unit Unit ℝ) :
    (∑ x ∈ (∅ : Finset Unit), ∑ y ∈ univ,
      |correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f A
          (polynomialPrepCutoff4 HP.θ) HP.ρ ∅ univ x y -
        correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f B
          (polynomialPrepCutoff4 HP.θ) HP.ρ ∅ univ x y| ^ 4) = 0 := by
  exact sum_empty

end PreparationPaymentRegression
