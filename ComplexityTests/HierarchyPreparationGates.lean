/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of incoming PREP gate cancellation)
import Complexity.Foundations.Probability.HierarchyPreparationGates
import all ComplexityTests.PreparationColumnObstruction

/-!
Gate-aware clients reuse literal RAW2/PREP3 and nonconstant RAW33/PREP34 fixtures.
The overloaded column now charges zero. The latter fixture's own nonzero error pays
the smaller profile and its original normalizer/root decoder. These supplied singleton
finite-bin executions do not establish exhaustive production bins or recursive IH.
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

namespace PreparationGatesRegression

-- Genuine incoming-rank boundary: one gate open, one closed, positive bias.
example :
    incomingGate (fun a _ => a) (fun a => max (1 - a) 0) 1 1 1
      (0 : Matrix Unit Unit ℝ) univ univ () = 1 ∧
    incomingGate (fun a _ => a) (fun a => max (1 - a) 0) 1 1 1
      (fun _ _ : Unit => (1 : ℝ)) univ univ () = 0 ∧
    preparationGateError (fun a _ => a) (fun a => max (1 - a) 0)
      (fun _ => 1) (fun _ => 1) 1 1 1 0 0 1
      (0 : Matrix Unit Unit ℝ) (fun _ _ => 1) univ univ () () = 1 := by
  norm_num [preparationGateError, incomingGate, auxScore, rowGate, atomPrep,
    kthLargest, Finset.univ_unique]

-- The one-open boundary has positive actual preparation bias, matching its bound.
example :
    |correctionPrep (fun a _ => a) (fun a => max (1 - a) 0) 1 1 1
        (0 : Matrix Unit Unit ℝ) (fun _ => 1) (fun _ => 1) univ univ () () -
      correctionPrep (fun a _ => a) (fun a => max (1 - a) 0) 1 1 1
        (fun _ _ : Unit => (1 : ℝ)) (fun _ => 1) (fun _ => 1) univ univ () ()| = 1 := by
  rw [abs_sub_comm, abs_correctionPrep_sub_of_left_closed
    (fun _ => zero_le_one) (fun _ => zero_le_one) (fun _ => le_max_right _ _)
    _ _ _ _ _ _ (by norm_num [incomingGate, auxScore, kthLargest, Finset.univ_unique])]
  norm_num [atomPrep, incomingGate, auxScore, rowGate, kthLargest, Finset.univ_unique]

-- Both gates open: the incoming term retains a nonzero actual rank perturbation.
example :
    preparationGateError (fun a _ => a) (fun a => max (1 - a) 0)
      (fun _ => 1) (fun _ => 1) 1 1 1 0 0 1
      (fun _ _ : Unit => (1 / 4 : ℝ)) (fun _ _ => 1 / 2) univ univ () () = 1 / 4 := by
  norm_num [preparationGateError, incomingGate, auxScore, rowGate, atomPrep,
    kthLargest, Finset.univ_unique]

-- The stochastic counterexample's overloaded column now pays exactly zero on
-- every row, although the old profile is positive on every row there.
private lemma counterexample_column {P : ℕ} [Fact P.Prime]
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hP : ⌈4 * (1 + 32 * HP.R)⌉₊ < P) (x : ZMod P)
    (Lh Lρ Lτ : ℝ) (ht : 0 ≤ Lτ) :
    preparationGateError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ 1
      Lh Lρ Lτ (PreparationColumn.deleted 0 1) (PreparationColumn.reference 0 1)
      univ univ x 0 = 0 := by
  have hK := PreparationColumnRegression.cap HP
  have hc := PreparationColumn.closed_column HP (0 : ZMod P) 1 1 hK
    (Kc := ⌈4 * (1 + 32 * HP.R)⌉₊)
    (Nat.ceil_pos.mpr (by linarith [HP.R_var])) (by simpa only [ZMod.card] using hP)
  have hb := hc.2
  change atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
    (PreparationColumn.reference 0 1) univ 1 0 * _ = 0 at hb
  rw [PreparationColumn.reference_preparation HP 0 1 1 hK, one_mul] at hb
  have ha := hc.1
  have he : atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
      (PreparationColumn.deleted (0 : ZMod P) 1) univ 1 0 = 1 := by
    simp only [atomPrep, rowGate, div_one]
    rw [(PreparationColumn.row_ranks (0 : ZMod P) 1 1 hK).1,
      HP.ρ_one 0 HP.η_pos.le, mul_one]
    have hv : PreparationColumn.deleted (0 : ZMod P) 1 1 0 = 1 := by
      simp [PreparationColumn.deleted, PreparationColumn.reference, one_ne_zero]
    rw [hv]
    exact polynomialPrepCutoff4_eq_one HP.θ_pos
      (by linarith [HP.θ_lt_θ₂, HP.θ₂_lt])
  change atomPrep (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K 1
    (PreparationColumn.deleted 0 1) univ 1 0 * _ = 0 at ha
  rw [he, one_mul] at ha
  exact preparationGateError_eq_zero_of_closed ht _ _ _ _ _ _ ha hb

open PreparationColumnRegression in
example {P : ℕ} [Fact P.Prime] (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hP : ⌈4 * (1 + 32 * HP.R)⌉₊ < P)
    (Lh Lρ Lτ : ℝ) (ht : 0 ≤ Lτ) :
    (data (P := P) HP).evaluate 3 (prep (P := P) HP) = some (.row 0) ∧
    (data (P := P) HP).evaluate 2 (input (P := P) HP) =
      some (.row (fun _ => PreparationColumn.deleted 0 1)) ∧
    ∀ x : ZMod P, preparationGateError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
      (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ 1 Lh Lρ Lτ
      (PreparationColumn.deleted 0 1) (PreparationColumn.reference 0 1) univ univ x 0 = 0 := by
  refine ⟨?_, evaluated HP, fun x => counterexample_column HP hP x Lh Lρ Lτ ht⟩
  have hp : 0 < (data (P := P) HP).requestPrecision 3 (prep (P := P) HP) := by
    rw [BudgetData.requestPrecision_grid _ 3 0 0 _ rfl rfl]
    norm_num [data]
  have hc : (data (P := P) HP).childBudget 3 = 2 := by
    norm_num [BudgetData.childBudget, data, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff]
  have he : (data (P := P) HP).evaluate ((data (P := P) HP).childBudget 3)
      {prep HP with task := .row 0 (.pilotInput ⟨0, HP.k_pos⟩)} =
      some (.row (fun _ => PreparationColumn.deleted 0 1)) := by rw [hc]; exact evaluated HP
  rw [BudgetData.evaluate_preparation _ 3 true ⟨0, HP.k_pos⟩ _ rfl hp
    (by rw [hc]; decide) _ he, prep_zero HP hP]
  rw [BudgetData.complete_grid _ 3 _ 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl]
  simp only [Option.map_some]
  apply congrArg some
  apply congrArg BudgetValue.row
  funext σ x y
  change conditionalWalk _ _ _ _ (fun _ _ _ => (0 : ℝ)) σ x y = 0
  rw [conditionalWalk_const]
  split_ifs <;> rfl


open PreparationRanksRegression

private lemma actual_gate_bias (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lh Lρ Lτ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧ 0 ≤ Lτ ∧
    let B := halfData HP
    let r := PreparationExecutionRegression.prepRequest HP
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 5 r.source.rate X U (fun _ x y => rowSliceMean X U completedTable x y -
      rowSliceMean X U (B.incomingPreparation r (fun _ => base)) x y) ≤
    rowNormPow 4 5 r.source.rate X U (fun σ x y =>
      preparationGateError (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff
        (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        r.terminal.rate Lh Lρ Lτ (halfTable σ) base {z | X σ z} {w | U σ w} x y) := by
  obtain ⟨Lh, Lρ, Lτ, hh, hr, ht, h⟩ := BudgetData.evaluate_preparation_gate_bias (HP := HP)
  refine ⟨Lh, Lρ, Lτ, hh, hr, ht, ?_⟩
  have hq : 0 < (halfData HP).requestPrecision 33 (budgetRequest HP) := by
    rw [precision]; norm_num
  have hc := h 5 (halfData HP) 34 true ⟨0, HP.k_pos⟩
    (PreparationExecutionRegression.prepRequest HP) rfl (prep_active HP)
    ((halfData HP).childBudget_lt (by decide)) rfl (rate_pos 1).le (rate_pos 0)
    halfTable completedTable hq (half_evaluated HP) (prep_evaluated HP)
    0 2 (by decide) 1 0 [1] [2, 3] rfl rfl
  simpa only [canonical_zero, Nat.cast_ofNat] using hc

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
  obtain ⟨Lh, Lρ, Lτ, hh, hr, ht, hg⟩ := actual_gate_bias HP
  obtain ⟨LI, hi, hm⟩ := actual_profile_moment HP Lh Lρ Lτ hh hr ht
  let K := Lh + Lρ + 2 * Lτ * LI
  have hK : 0 ≤ K := by dsimp only [K]; positivity
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
    rw [hf] at hg
    apply hg.trans
    apply le_trans _ (hm.trans (mul_le_mul_of_nonneg_left
      (by rw [← own_moment HP]; exact own_accuracy HP) (pow_nonneg hK 4)))
    apply (rowNormPow_le_mul (N := 5) (u := rate 1) (c := 1)
      (by norm_num [rate]) ?_).trans_eq (one_mul _)
    intro σ x y _hx _hy
    have hn := preparationGateError_nonneg (I := polynomialAuxCutoff4 HP.θ)
      (τ := HP.incomingCutoff) (h := polynomialPrepCutoff4 HP.θ) (ρ := HP.ρ)
      (K := HP.K) (Kc := ⌈4 * (1 + 32 * HP.R)⌉₊) (f := 1)
      (by norm_num) hh hr ht (polynomialPrepCutoff4_nonneg HP.θ)
      HP.ρ_nonneg HP.incomingCutoff_nonneg (halfTable σ) base
      {z | source σ z} {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} x y
    have hc := preparationGateError_le_rank_error
      (Lh := Lh)
      (I := polynomialAuxCutoff4 HP.θ) (τ := HP.incomingCutoff)
      (h := polynomialPrepCutoff4 HP.θ) (ρ := HP.ρ)
      (FourthRootHierarchyParams.NormalizedRow.rank_pos HP)
      (show 0 < ⌈4 * (1 + 32 * HP.R)⌉₊ from Nat.ceil_pos.mpr (by linarith [HP.R_var]))
      (by norm_num : (0 : ℝ) < 1) hr ht (polynomialPrepCutoff4_nonneg HP.θ)
      HP.ρ_nonneg HP.incomingCutoff_nonneg (halfTable σ) base
      {z | source σ z} {w | (budgetRequest HP).usage.retains (channels (1 : ZMod 5)) σ w} x y
    have hpw := pow_le_pow_left₀ hn hc 4
    rw [← abs_of_nonneg hn, ← abs_of_nonneg (hn.trans hc)] at hpw
    simpa only [one_mul, PreparationExecutionRegression.prepRequest, halfData, budgetData] using hpw
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


end PreparationGatesRegression
