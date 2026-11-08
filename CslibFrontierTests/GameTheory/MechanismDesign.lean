/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Mechanism.Knapsack
import CslibFrontier.GameTheory.Mechanism.VCG
import CslibFrontier.GameTheory.Mechanism.Vickrey
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mechanism design clients

Concrete Vickrey auctions (a strict winner and a tie), a non-monotone rule that is not
implementable, Myerson's payments for a continuous (linear) allocation rule, VCG payments in a
two-agent public project, knapsack feasibility, and nonvacuity of the existence theorems.
-/

namespace CslibFrontierTests.GameTheory.MechanismDesign

open Cslib.GameTheory Cslib.GameTheory.SingleParameter

/-! ### Vickrey auction -/

section Vickrey

open SingleParameter.Vickrey

/-- On bids `(3, 5, 4)` bidder `1` wins, pays the second-highest bid `4`, and the others pay
nothing. -/
example :
    Wins ![(3 : ℝ), 5, 4] 1 ∧ mechanism.payment ![(3 : ℝ), 5, 4] 1 = 4 ∧
      mechanism.payment ![(3 : ℝ), 5, 4] 0 = 0 ∧ mechanism.payment ![(3 : ℝ), 5, 4] 2 = 0 := by
  have hw : Wins ![(3 : ℝ), 5, 4] 1 := by
    intro j hj
    fin_cases j
    · norm_num
    · exact absurd rfl hj
    · norm_num
  have hother : ∀ j : Fin 3, j ≠ 1 → mechanism.payment ![(3 : ℝ), 5, 4] j = 0 := fun j hj => by
    change highestOtherBid _ j * allocation _ j = 0
    rw [allocation_eq_zero_iff.2 fun h => hj (h.unique hw), mul_zero]
  refine ⟨hw, ?_, hother 0 (by decide), hother 2 (by decide)⟩
  change highestOtherBid _ 1 * allocation _ 1 = 4
  rw [allocation_eq_one_iff.2 hw, mul_one]
  refine le_antisymm (highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩) ?_
  · fin_cases j
    · norm_num
    · exact absurd rfl hj
    · norm_num
  · exact le_of_eq_of_le (by norm_num)
      (le_highestOtherBid (b := ![(3 : ℝ), 5, 4]) (i := 1) (j := 2) (by decide))

/-- Ties go to the smallest index: on bids `(5, 5)` bidder `0` wins and pays `5`. -/
example : Wins ![(5 : ℝ), 5] 0 ∧ ¬ Wins ![(5 : ℝ), 5] 1 ∧
    mechanism.payment ![(5 : ℝ), 5] 0 = 5 := by
  have hw : Wins ![(5 : ℝ), 5] 0 := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · exact ⟨le_rfl, fun h => absurd h (by decide)⟩
  refine ⟨hw, fun h => absurd (h.unique hw) (by decide), ?_⟩
  change highestOtherBid _ 0 * allocation _ 0 = 5
  rw [allocation_eq_one_iff.2 hw, mul_one]
  refine le_antisymm (highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩) ?_
  · fin_cases j
    · exact absurd rfl hj
    · norm_num
  · exact le_of_eq_of_le (by norm_num)
      (le_highestOtherBid (b := ![(5 : ℝ), 5]) (i := 0) (j := 1) (by decide))

/-- The Vickrey auction is DSIC, individually rational and welfare-maximizing on three bidders. -/
example : (mechanism (ι := Fin 3)).IsDSIC ∧ (mechanism (ι := Fin 3)).IsIR ∧
    IsWelfareMaximizing singleItemFeasible (allocation (ι := Fin 3)) :=
  ⟨mechanism_isDSIC, mechanism_isIR, isWelfareMaximizing_allocation⟩

end Vickrey

/-! ### Myerson's Lemma -/

/-- A single bidder who gets the item exactly when bidding at most `1`. -/
noncomputable def lowBidRule : (Unit → ℝ) → Unit → ℝ := fun b _ => if b () ≤ 1 then 1 else 0

/-- The rule `lowBidRule` is not monotone, so no payment rule makes it DSIC. -/
example : ¬ IsMonotone lowBidRule ∧ ¬ IsImplementable lowBidRule := by
  have h : ¬ IsMonotone lowBidRule := fun hm => by
    have h02 : (0 : ℝ) ≤ 2 := by norm_num
    have := hm () 0 le_rfl (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h02) h02
    norm_num [lowBidRule, Function.update_self] at this
  exact ⟨h, fun hi => h (isImplementable_iff_isMonotone.1 hi)⟩

/-- The linear allocation rule `xᵢ(b) = bᵢ` (a divisible good, allocation proportional to the
bid) is monotone; its Myerson payment is `bᵢ² / 2`, and with these payments it is DSIC. This is a
non-piecewise-constant instance of Myerson's Lemma. -/
example (b : Fin 2 → ℝ) (i : Fin 2) :
    myersonPayment (fun b i => b i) b i = b i ^ 2 / 2 ∧ IsMonotone (fun (b : Fin 2 → ℝ) i => b i) ∧
      (myerson fun (b : Fin 2 → ℝ) i => b i).IsDSIC := by
  have hm : IsMonotone (fun (b : Fin 2 → ℝ) i => b i) := fun i b _ z _ z' _ hzz' => by
    simpa only [Function.update_self] using hzz'
  refine ⟨?_, hm, myerson_isDSIC hm⟩
  simp only [myersonPayment, Function.update_self, integral_id]
  ring

/-! ### VCG -/

/-- A two-agent public project: build it (`true`) exactly when the reported welfare of building
is at least that of not building. -/
noncomputable def buildRule (b : Fin 2 → Bool → ℝ) : Bool :=
  decide (Mechanism.welfare b false ≤ Mechanism.welfare b true)

theorem buildRule_isWelfareMaximizing : Mechanism.IsWelfareMaximizing buildRule := by
  intro b ω
  unfold buildRule
  by_cases h : Mechanism.welfare b false ≤ Mechanism.welfare b true
  · rw [decide_eq_true h]
    cases ω
    · exact h
    · exact le_rfl
  · rw [decide_eq_false h]
    cases ω
    · exact le_rfl
    · exact (not_le.1 h).le

/-- Agent `0` values the project at `3` and agent `1` at `-1`. -/
noncomputable def projectValues : Fin 2 → Bool → ℝ := ![fun ω => if ω then 3 else 0,
  fun ω => if ω then -1 else 0]

/-- The project is built; the pivotal agent `0` pays its externality `1` and agent `1` pays
nothing. -/
example : buildRule projectValues = true ∧
    (Mechanism.vcg buildRule).payment projectValues 0 = 1 ∧
    (Mechanism.vcg buildRule).payment projectValues 1 = 0 := by
  have hb : buildRule projectValues = true := by
    simp only [buildRule, Mechanism.welfare, Fin.sum_univ_two, projectValues]
    norm_num
  have hpiv : ∀ i : Fin 2, Mechanism.clarkePivot i projectValues =
      max (∑ j ∈ Finset.univ.erase i, projectValues j true)
        (∑ j ∈ Finset.univ.erase i, projectValues j false) := fun i => by
    refine le_antisymm (Finset.sup'_le _ _ fun ω _ => ?_) (max_le ?_ ?_)
    · cases ω
      · exact le_max_right _ _
      · exact le_max_left _ _
    · exact Finset.le_sup' (fun ω => ∑ j ∈ Finset.univ.erase i, projectValues j ω)
        (Finset.mem_univ true)
    · exact Finset.le_sup' (fun ω => ∑ j ∈ Finset.univ.erase i, projectValues j ω)
        (Finset.mem_univ false)
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  have hpay : ∀ i, (Mechanism.vcg buildRule).payment projectValues i =
      Mechanism.clarkePivot i projectValues -
        ∑ j ∈ Finset.univ.erase i, projectValues j (buildRule projectValues) := fun _ => rfl
  refine ⟨hb, ?_, ?_⟩
  · rw [hpay, hpiv, hb, h0]
    simp only [Finset.sum_singleton]
    norm_num [projectValues]
  · rw [hpay, hpiv, hb, h1]
    simp only [Finset.sum_singleton]
    norm_num [projectValues]

/-- VCG with this outcome rule is DSIC, individually rational, with nonnegative payments. -/
example : (Mechanism.vcg buildRule).IsDSIC ∧ (Mechanism.vcg buildRule).IsIR ∧
    ∀ b i, 0 ≤ (Mechanism.vcg buildRule).payment b i :=
  ⟨Mechanism.vcg_isDSIC buildRule_isWelfareMaximizing,
    Mechanism.vcg_isIR buildRule_isWelfareMaximizing, Mechanism.vcg_payment_nonneg buildRule⟩

/-- Nonvacuity: a DSIC welfare-maximizing IR mechanism exists with three agents and three
outcomes. -/
example : ∃ M : Mechanism (Fin 3) (Fin 3), M.IsDSIC ∧ Mechanism.IsWelfareMaximizing M.outcome ∧
    M.IsIR ∧ ∀ b i, 0 ≤ M.payment b i :=
  Mechanism.exists_isDSIC_isWelfareMaximizing

/-! ### Knapsack auctions -/

/-- With sizes `(2, 3)` and capacity `4`, the first bidder alone fits, both together do not, and
fractional allocations are excluded. -/
example : ![(1 : ℝ), 0] ∈ knapsackFeasible ![2, 3] 4 ∧
    ![(1 : ℝ), 1] ∉ knapsackFeasible ![2, 3] 4 ∧
    ![(1 / 2 : ℝ), 0] ∉ knapsackFeasible ![2, 3] 4 := by
  refine ⟨⟨fun i => ?_, ?_⟩, fun h => ?_, fun h => ?_⟩
  · fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_two]
    norm_num
  · have := h.2
    simp only [Fin.sum_univ_two] at this
    norm_num at this
  · rcases h.1 0 with h0 | h0 <;> norm_num at h0

/-- Nonvacuity of the knapsack theorem for these sizes and capacity. -/
example : ∃ x, IsWelfareMaximizing (knapsackFeasible ![(2 : ℝ), 3] 4) x ∧
    (criticalBidMechanism x).IsDSIC ∧ (criticalBidMechanism x).IsIR ∧
    ∀ b, 0 ≤ b → ∀ i, criticalBid x b i * x b i = myersonPayment x b i :=
  exists_knapsack_isWelfareMaximizing _ (by norm_num)

end CslibFrontierTests.GameTheory.MechanismDesign
