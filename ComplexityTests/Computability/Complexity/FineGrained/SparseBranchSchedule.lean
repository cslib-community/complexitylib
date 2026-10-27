/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseBranchSchedule
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests for `Complexity.Computability.Complexity.FineGrained.SparseBranchSchedule`

Concrete expected-value checks for `branchEquationScope`, `branchAugmentedScope`,
`sum_card_branchAugmentedScope`, `le_sum_card_branchAugmentedScope`,
`varIncidence_branchAugmentedScope_le`, `sum_card_branchAugmentedScope_le`,
`card_branchAugmentedScope_le`, `branchDegreeBudget_le`, and `sum_branch_domainExaminationBound_le`,
together with a nonvacuous witness at `n = 2 ^ (2 ^ 50)` instantiating
`Feasible.exists_branch_replacementDesign` and `Feasible.branch_domainExaminationBound_le`.
-/

@[expose] public noncomputable section

namespace Cslib.Complexity.SubexponentialSAT.SparseBranchScheduleTests

open Finset
open scoped BigOperators
open Cslib.BitString Cslib.LinearAlgebra Cslib.ReplacementCounting
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

/-- Concrete 2-variable, 1-equation system `P 0 = {{0, 1}}` on `Fin 2` with no heavy variables
(`b₀ = 1`, `S = ∅`), checking `branchEquationScope`, `branchAugmentedScope`,
`sum_card_branchAugmentedScope`, `varIncidence_branchAugmentedScope_le`, and
`card_branchAugmentedScope_le`. -/
def sampleP (_ : Fin 1) : Finset (Finset (Fin 2)) :=
  {{0, 1}}

theorem heavyVars_sampleP_eq_empty :
    heavyVars (univ : Finset (Fin 2)) (univ : Finset (Fin 1))
      (fun i => equationScope (sampleP i)) 1 = ∅ := by
  decide

def sampleEquiv :
    ↥((univ : Finset (Fin 2)) \
      heavyVars (univ : Finset (Fin 2)) (univ : Finset (Fin 1))
        (fun i => equationScope (sampleP i)) 1) ≃ Fin 2 where
  toFun v := v.1
  invFun v := ⟨v, by decide +revert⟩
  left_inv v := by ext; rfl
  right_inv v := rfl

example (b : Fin 2 → Bool) :
    let S := heavyVars (univ : Finset (Fin 2)) (univ : Finset (Fin 1))
      (fun i => equationScope (sampleP i)) 1
    (∑ f : {i : Fin 1 // i ∈ (univ : Finset (Fin 1))} ⊕ Fin 2,
        #(branchAugmentedScope S sampleEquiv univ sampleP b f)) =
      totalIncidence (univ : Finset (Fin 1))
        (branchEquationScope S sampleEquiv sampleP b) + 2 ∧
    2 ≤ ∑ f : {i : Fin 1 // i ∈ (univ : Finset (Fin 1))} ⊕ Fin 2,
        #(branchAugmentedScope S sampleEquiv univ sampleP b f) ∧
    (∑ f : {i : Fin 1 // i ∈ (univ : Finset (Fin 1))} ⊕ Fin 2,
        #(branchAugmentedScope S sampleEquiv univ sampleP b f)) ≤ 2 * 2 ∧
    (∀ v : Fin 2,
      #{f : {i : Fin 1 // i ∈ (univ : Finset (Fin 1))} ⊕ Fin 2 |
          v ∈ branchAugmentedScope S sampleEquiv univ sampleP b f} ≤ 2) := by
  intro S
  refine ⟨sum_card_branchAugmentedScope S sampleEquiv univ sampleP b,
    le_sum_card_branchAugmentedScope S sampleEquiv univ sampleP b,
    sum_card_branchAugmentedScope_le univ univ sampleP 1 (Subset.refl _) sampleEquiv b,
    varIncidence_branchAugmentedScope_le univ univ sampleP 1 (Subset.refl _) sampleEquiv b⟩

/-- Concrete degree-budget check for `branchDegreeBudget_le`:
for `k = 3`, `c = 4`, `n = 10`, `n' = 5`, `m = 40`, `3 * (40 + 2 * (11 - 1)) = 180 ≤ 36 * 5 = 180`.
-/
example :
    3 * (40 + 2 * (branchPrecision 10 - 1)) ≤ (3 * (2 * 4 + 4)) * 5 :=
  branchDegreeBudget_le (m := 40) (c := 4) (n := 10) (n' := 5) (by decide) (by decide)

/-- Concrete multi-branch sum check for `sum_branch_domainExaminationBound_le` on `sampleP`
(`s_div = 2`, `b₀ = 2`, `totalIncidence = 2`, `Fintype.card (Fin 2) = 2`, `n' = 2`):
`Fintype.card (Fin 2) ≤ 2 * 2` and the zero examination sum is bounded by the `2 ^ (2 / 2)`
branch-summed upper bound. -/
def sampleEquiv2 :
    ↥((univ : Finset (Fin 2)) \
      heavyVars (univ : Finset (Fin 2)) (univ : Finset (Fin 1))
        (fun i => equationScope (sampleP i)) 2) ≃ Fin 2 where
  toFun v := v.1
  invFun v := ⟨v, by decide +revert⟩
  left_inv v := by ext; rfl
  right_inv v := rfl

example :
    Fintype.card (Fin 2) ≤ 2 * 2 ∧
    (∑ _b ∈ branchAssignments
        (heavyVars (univ : Finset (Fin 2)) (univ : Finset (Fin 1))
          (fun i => equationScope (sampleP i)) 2), (0 : ℝ)) ≤
      (2 : ℝ) ^ (Fintype.card (Fin 2) / 2) *
        (2 * (numNodes 2 : ℝ) * (numGroups 2 : ℝ) *
          Real.exp (((3 * (2 * 1 + 4) + 4 : ℕ) : ℝ) * (2 : ℝ) * rowCost 1 2)) :=
  sum_branch_domainExaminationBound_le (β := 1) (k := 3) (c := 1)
    (univ : Finset (Fin 1)) sampleP (by decide) (by decide) (by decide) sampleEquiv2
    (fun _ => 0) (fun _ _ => by positivity)

/-- Nonvacuous concrete witness at `n = 2 ^ (2 ^ 50)` for an empty active equation set
(`I = F = ∅ : Finset (Fin 0)`, `b₀ = 1`, `w = 1`, `S = ∅`, `n' = n`), instantiating
`Feasible.exists_branch_replacementDesign`, `Feasible.branch_domainExaminationBound_le`, and
`sum_branch_domainExaminationBound_le`. -/
def emptyP (n : ℕ) : Fin 0 → Finset (Finset (Fin n)) :=
  Fin.elim0

theorem heavyVars_emptyP_eq_empty (n b₀ : ℕ) :
    heavyVars (univ : Finset (Fin n)) (∅ : Finset (Fin 0))
      (fun i => equationScope (emptyP n i)) b₀ = ∅ := by
  ext v
  simp [heavyVars, varIncidence]

def emptyEquiv (n b₀ : ℕ) :
    ↥((univ : Finset (Fin n)) \
      heavyVars (univ : Finset (Fin n)) (∅ : Finset (Fin 0))
        (fun i => equationScope (emptyP n i)) b₀) ≃ Fin n where
  toFun v := v.1
  invFun v := ⟨v, by rw [heavyVars_emptyP_eq_empty]; simp⟩
  left_inv v := by ext; rfl
  right_inv v := rfl

example :
    ∃ m n : ℕ,
      m = 2 ^ 50 ∧
      n = 2 ^ m ∧
      rowCost 1 n < 1 / 3 ∧
      ∀ b : Fin n → Bool,
        ∃ (hF : Feasible 1 n (1 + 1) (max 1 1)
            (∑ f : {i : Fin 0 // i ∈ (∅ : Finset (Fin 0))} ⊕ Fin n,
              #(branchAugmentedScope
                (heavyVars (univ : Finset (Fin n)) (∅ : Finset (Fin 0))
                  (fun i => equationScope (emptyP n i)) 1)
                (emptyEquiv n 1) ∅ (emptyP n) b f)))
          (D : ReplacementDesign
            (branchAugmentedScope
              (heavyVars (univ : Finset (Fin n)) (∅ : Finset (Fin 0))
                (fun i => equationScope (emptyP n i)) 1)
              (emptyEquiv n 1) ∅ (emptyP n) b)
            (numNodes n) (numGroups n) (intervalStart 1 n) (rowBound 1 n) (tauRat n)),
          let d := 3 * (#(∅ : Finset (Fin 0)) + 2 * (branchPrecision (Fintype.card (Fin n)) - 1))
          let q := (d * rowBound 1 n) / numNodes n
          let C := hF.toCountingDesign D univ
          (∑ t : Fin (numNodes n),
              (#{p : Finset (Fin n) × Finset (Fin n) | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                (2 * (#(C.measurementBox t) : ℝ) *
                  ∑ g : Fin (numGroups n), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
            2 * (numNodes n : ℝ) * (numGroups n : ℝ) *
              Real.exp (((3 * (2 * 1 + 4) + 4 : ℕ) : ℝ) * (n : ℝ) * rowCost 1 n) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 ^ 50 := ⟨2 ^ 50, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 ^ m := ⟨2 ^ m, rfl⟩
  have hcl_n : Nat.clog 2 n = 2 ^ 50 := by
    rw [hn, Nat.clog_pow 2 m one_lt_two, hm]
  have hcl_cl : Nat.clog 2 (Nat.clog 2 n) = 50 := by
    rw [hcl_n]
    exact Nat.clog_pow 2 50 one_lt_two
  have hr_eq : numGroups n = 13421 := by
    unfold numGroups
    rw [hcl_cl, hcl_n]
    have hsq : (2 ^ 50 : ℕ).sqrt = 2 ^ 25 :=
      le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by norm_num)))
        (Nat.le_sqrt.mpr (by norm_num))
    rw [hsq]
    norm_num
  have hQ_eq : numNodes n = 175921860444 := by
    unfold numNodes
    rw [hcl_cl, hcl_n]
    norm_num
  have hR_eq : rowBound 1 n = 134217728 := by
    unfold rowBound
    rw [hcl_n]
    have hsq : (2 ^ 50 - 1 : ℕ).sqrt = 2 ^ 25 - 1 :=
      le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by norm_num)))
        (Nat.le_sqrt.mpr (by norm_num))
    simp only [show (2 ^ 50 : ℕ) ≠ 0 by positivity, ↓reduceIte, hsq]
    norm_num
  have hr : 2 ≤ numGroups n := by rw [hr_eq]; norm_num
  have hR : 32 ≤ rowBound 1 n := by rw [hR_eq]; norm_num
  have hRQ : 6 * rowBound 1 n ≤ numNodes n := by rw [hR_eq, hQ_eq]; norm_num
  have hsub := interval_subset_range (β := 1) hr (by omega) (by omega)
  have hrc := rowCost_le hr hR hRQ
  have hrc_lt : rowCost 1 n < 1 / 3 := hrc.trans_lt <| by
    rw [hcl_cl, hcl_n, show ((2 ^ 50 : ℕ) : ℝ) = ((2 : ℝ) ^ 25) ^ 2 by norm_num,
      Real.sqrt_sq (by positivity)]
    norm_num
  refine ⟨m, n, hm, hn, hrc_lt, fun b => ?_⟩
  let S := heavyVars (univ : Finset (Fin n)) (∅ : Finset (Fin 0))
    (fun i => equationScope (emptyP n i)) 1
  have hsum_eq :
      (∑ f : {i : Fin 0 // i ∈ (∅ : Finset (Fin 0))} ⊕ Fin n,
        #(branchAugmentedScope S (emptyEquiv n 1) ∅ (emptyP n) b f)) = n := by
    rw [sum_card_branchAugmentedScope]
    simp [totalIncidence]
  have hF : Feasible 1 n (1 + 1) (max 1 1)
      (∑ f : {i : Fin 0 // i ∈ (∅ : Finset (Fin 0))} ⊕ Fin n,
        #(branchAugmentedScope S (emptyEquiv n 1) ∅ (emptyP n) b f)) := by
    rw [hsum_eq]
    exact {
      twenty_le := by
        rw [hn]
        exact (by norm_num : 20 ≤ 2 ^ 5).trans
          (Nat.pow_le_pow_right two_pos (by rw [hm]; norm_num))
      two_le_numGroups := hr
      thirtyTwo_le_rowBound := hR
      six_mul_rowBound_le_numNodes := hRQ
      tau_pos := by unfold tau; rw [hr_eq, hcl_n]; positivity
      tau_le_half := by unfold tau; rw [hr_eq, hcl_n]; norm_num
      auxDim_le := auxDim_le_two_pow n
      aux_balance :=
        (Nat.mul_le_mul (by norm_num : 2 * (1 + 1 + max 1 1) ≤ 2 ^ 3)
          (Nat.pow_le_pow_left (auxDim_le_two_pow n) 2)).trans <| by
          rw [← pow_mul, ← pow_add, hn]
          exact Nat.pow_le_pow_right two_pos
            (by rw [Nat.clog_pow 2 m one_lt_two, hm]; norm_num)
      var_balance := by
        rw [hQ_eq, hr_eq, hn]
        exact (by norm_num : 2 * 175921860444 * 13421 ^ 2 ≤ 2 ^ 66).trans
          (Nat.pow_le_pow_right two_pos (by rw [hm]; norm_num))
      card_interval_eq := card_interval (by omega)
      interval_subset := hsub
      mem_interval_of_close := fun k hk =>
        ⟨mem_interval_of_abs_sub_le hr hR (by omega) hk,
          Nat.lt_succ_iff.mp
            (mem_range.mp (hsub (mem_interval_of_abs_sub_le hr hR (by omega) hk)))⟩
      binomTail_lt :=
        binomTail_lt_tailBudget le_rfl hr hR hRQ (by norm_num) (by rw [hcl_n]; norm_num)
      rowCost_bound := hrc
    }
  have hw : ∀ i ∈ (∅ : Finset (Fin 0)), #(equationScope (emptyP n i)) ≤ 1 := by simp
  obtain ⟨D⟩ := hF.exists_branch_replacementDesign (∅ : Finset (Fin 0)) ∅ (emptyP n)
    (Subset.refl _) (emptyEquiv n 1) b hw
  refine ⟨hF, D, ?_⟩
  have hm_card : #(∅ : Finset (Fin 0)) ≤ 1 * Fintype.card (Fin n) := by simp
  have hn_card : Fintype.card (Fin n) ≤ 2 * n := by
    rw [Fintype.card_fin]
    omega
  exact (hF.branch_domainExaminationBound_le (ι := Fin n) (k := 3) (c := 1)
    (∅ : Finset (Fin 0)) D univ hm_card hn_card).1

end Cslib.Complexity.SubexponentialSAT.SparseBranchScheduleTests
