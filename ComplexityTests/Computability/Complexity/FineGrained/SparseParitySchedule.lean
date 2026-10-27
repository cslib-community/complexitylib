/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseParitySchedule
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests for `Complexity.Computability.Complexity.FineGrained.SparseParitySchedule`

Concrete expected-value checks on a 2-variable 2-CNF formula `testCNF` (`(x₀ ∨ ¬x₁) ∧ (x₁)`) for
`CNF.totalIncidence_parityRowSystem_le_six_mul`, `CNF.card_le_two_mul_freeVar_parityRowSystem`,
`CNF.card_branchAugmentedScope_parityRowSystem_le`, and
`CNF.sum_branch_domainExaminationBound_parityRowSystem_le`, together with a nonvacuous witness at
`n = 2 ^ (2 ^ 50)` instantiating `CNF.exists_branch_replacementDesign_parityRowSystem` and
`CNF.branch_domainExaminationBound_parityRowSystem_le`.
-/

@[expose] public noncomputable section

namespace Cslib.Complexity.SubexponentialSAT.SparseParityScheduleTests

open Finset
open scoped BigOperators
open Cslib.BitString Cslib.LinearAlgebra Cslib.ReplacementCounting Cslib.Logic.PL
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

/-- Concrete 2-variable 2-CNF formula `(x₀ ∨ ¬x₁) ∧ (x₁)` on `Fin 2`. -/
def testCNF : CNF (Fin 2) :=
  [[(0, true), (1, false)], [(1, true)]]

/-- Concrete two-row unit parity check matrix selecting clause `0` and clause `1` of `testCNF`. -/
def testRows : List (Fin testCNF.length → Bool) :=
  [Pi.single ⟨0, by decide⟩ true, Pi.single ⟨1, by decide⟩ true]

/-- Concrete check of `CNF.totalIncidence_parityRowSystem_le_six_mul` on `testCNF` and `testRows`
(`k = 2`, `W = 1`, `Fintype.card (Fin 2) = 2`):
`totalIncidence ≤ (6 * (2 * (1 * 2 ^ 2))) * 2 = 96`. -/
example :
    totalIncidence (univ : Finset (Fin testRows.length))
        (fun j => equationScope (testCNF.parityRowSystem testRows j)) ≤
      (6 * (2 * (1 * 2 ^ 2))) * Fintype.card (Fin 2) :=
  testCNF.totalIncidence_parityRowSystem_le_six_mul (k := 2) (W := 1)
    (by decide) (by decide) (by decide)

/-- At threshold `b₀ = 96` (`s_div = 2`), `heavyVars` on `testCNF.parityRowSystem testRows` is
empty, so `n' = 2`. -/
def testEquiv96 :
    ↥((univ : Finset (Fin 2)) \
      heavyVars univ (univ : Finset (Fin testRows.length))
        (fun j => equationScope (testCNF.parityRowSystem testRows j)) 96) ≃ Fin 2 where
  toFun v := v.1
  invFun v := ⟨v, by decide +revert⟩
  left_inv v := by ext; rfl
  right_inv v := rfl

/-- Concrete check of `CNF.card_le_two_mul_freeVar_parityRowSystem`,
`CNF.card_branchAugmentedScope_parityRowSystem_le`, and
`CNF.sum_branch_domainExaminationBound_parityRowSystem_le` on `testCNF` and `testRows`. -/
example (b : Fin 2 → Bool)
    (f : {j : Fin testRows.length // j ∈ (univ : Finset (Fin testRows.length))} ⊕ Fin 2) :
    let S := heavyVars univ (univ : Finset (Fin testRows.length))
      (fun j => equationScope (testCNF.parityRowSystem testRows j)) 96
    (Fintype.card (Fin 2) ≤ 2 * 2 ∧ Fintype.card (Fin 2) / 2 ≤ 2) ∧
    #(branchAssignments S) ≤ 2 ^ (Fintype.card (Fin 2) / 2) ∧
    #(branchAugmentedScope S testEquiv96 univ (testCNF.parityRowSystem testRows) b f) ≤
      max (2 * (1 * 2 ^ 2)) 1 ∧
    (∑ _b ∈ branchAssignments S, (0 : ℝ)) ≤
      (2 : ℝ) ^ (Fintype.card (Fin 2) / 2) *
        (2 * (numNodes 2 : ℝ) * (numGroups 2 : ℝ) *
          Real.exp (((16 * 2 + 4 : ℕ) : ℝ) * (2 : ℝ) * rowCost 1 2)) := by
  intro S
  have hfree := testCNF.card_le_two_mul_freeVar_parityRowSystem (k := 2) (W := 1) (b₀ := 96)
    (s_div := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    testEquiv96
  have hscope := testCNF.card_branchAugmentedScope_parityRowSystem_le (k := 2) (W := 1)
    (by decide) (by decide) S testEquiv96 b f
  have hsum := testCNF.sum_branch_domainExaminationBound_parityRowSystem_le
    (β := 1) (k := 2) (W := 1) (b₀ := 96) (s_div := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    testEquiv96 (fun _ => 0) (fun _ _ => by positivity)
  exact ⟨hfree.1, hfree.2, hscope, hsum.2⟩

/-- Nonvacuous concrete witness at `n = 2 ^ (2 ^ 50)` for an empty 3-CNF `emptyCNF n : CNF (Fin n)`
and empty parity-row list `[]`, instantiating `CNF.exists_branch_replacementDesign_parityRowSystem`
and `CNF.branch_domainExaminationBound_parityRowSystem_le`. -/
def emptyCNF (n : ℕ) : CNF (Fin n) :=
  []

theorem heavyVars_emptyCNF_eq_empty (n b₀ : ℕ) :
    heavyVars (univ : Finset (Fin n)) (univ : Finset (Fin ([] : List (Fin 0 → Bool)).length))
      (fun j => equationScope ((emptyCNF n).parityRowSystem [] j)) b₀ = ∅ := by
  ext v
  simp [heavyVars, varIncidence]

def emptyCNFEquiv (n b₀ : ℕ) :
    ↥((univ : Finset (Fin n)) \
      heavyVars (univ : Finset (Fin n)) (univ : Finset (Fin ([] : List (Fin 0 → Bool)).length))
        (fun j => equationScope ((emptyCNF n).parityRowSystem [] j)) b₀) ≃ Fin n where
  toFun v := v.1
  invFun v := ⟨v, by rw [heavyVars_emptyCNF_eq_empty]; simp⟩
  left_inv v := by ext; rfl
  right_inv v := rfl

example :
    ∃ m n : ℕ,
      m = 2 ^ 50 ∧
      n = 2 ^ m ∧
      rowCost 1 n < 1 / 3 ∧
      ∀ b : Fin n → Bool,
        ∃ (hF : Feasible 1 n (1 + 1) (max (3 * (0 * 2 ^ 3)) 1)
            (∑ f : {j : Fin ([] : List (Fin (emptyCNF n).length → Bool)).length //
                j ∈ (univ : Finset (Fin ([] : List (Fin (emptyCNF n).length → Bool)).length))} ⊕
                Fin n,
              #(branchAugmentedScope
                (heavyVars (univ : Finset (Fin n))
                  (univ : Finset (Fin ([] : List (Fin (emptyCNF n).length → Bool)).length))
                  (fun j => equationScope ((emptyCNF n).parityRowSystem [] j)) 1)
                (emptyCNFEquiv n 1) univ ((emptyCNF n).parityRowSystem []) b f)))
          (D : ReplacementDesign
            (branchAugmentedScope
              (heavyVars (univ : Finset (Fin n))
                (univ : Finset (Fin ([] : List (Fin (emptyCNF n).length → Bool)).length))
                (fun j => equationScope ((emptyCNF n).parityRowSystem [] j)) 1)
              (emptyCNFEquiv n 1) univ ((emptyCNF n).parityRowSystem []) b)
            (numNodes n) (numGroups n) (intervalStart 1 n) (rowBound 1 n) (tauRat n)),
          let d := 3 * (([] : List (Fin (emptyCNF n).length → Bool)).length +
            2 * (branchPrecision (Fintype.card (Fin n)) - 1))
          let q := (d * rowBound 1 n) / numNodes n
          let C := hF.toCountingDesign D univ
          (∑ t : Fin (numNodes n),
              (#{p : Finset (Fin n) × Finset (Fin n) | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                (2 * (#(C.measurementBox t) : ℝ) *
                  ∑ g : Fin (numGroups n), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
            2 * (numNodes n : ℝ) * (numGroups n : ℝ) *
              Real.exp (((16 * 3 + 4 : ℕ) : ℝ) * (n : ℝ) * rowCost 1 n) := by
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
  let S := heavyVars (univ : Finset (Fin n))
    (univ : Finset (Fin ([] : List (Fin (emptyCNF n).length → Bool)).length))
    (fun j => equationScope ((emptyCNF n).parityRowSystem [] j)) 1
  have hsum_eq :
      (∑ f : {j : Fin ([] : List (Fin (emptyCNF n).length → Bool)).length //
          j ∈ (univ : Finset (Fin ([] : List (Fin (emptyCNF n).length → Bool)).length))} ⊕ Fin n,
        #(branchAugmentedScope S (emptyCNFEquiv n 1) univ
          ((emptyCNF n).parityRowSystem []) b f)) = n := by
    rw [sum_card_branchAugmentedScope]
    simp [totalIncidence]
  have hF : Feasible 1 n (1 + 1) (max (3 * (0 * 2 ^ 3)) 1)
      (∑ f : {j : Fin ([] : List (Fin (emptyCNF n).length → Bool)).length //
          j ∈ (univ : Finset (Fin ([] : List (Fin (emptyCNF n).length → Bool)).length))} ⊕ Fin n,
        #(branchAugmentedScope S (emptyCNFEquiv n 1) univ
          ((emptyCNF n).parityRowSystem []) b f)) := by
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
        (Nat.mul_le_mul (by norm_num : 2 * (1 + 1 + max (3 * (0 * 2 ^ 3)) 1) ≤ 2 ^ 3)
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
  have hk : ∀ c ∈ emptyCNF n, c.length ≤ 3 := by simp [emptyCNF]
  have hW : ∀ r ∈ ([] : List (Fin (emptyCNF n).length → Bool)), weight r ≤ 0 := by simp
  obtain ⟨D⟩ := (emptyCNF n).exists_branch_replacementDesign_parityRowSystem hk hW
    (emptyCNFEquiv n 1) b hF
  refine ⟨hF, D, ?_⟩
  have hlen : ([] : List (Fin (emptyCNF n).length → Bool)).length ≤ 6 * Fintype.card (Fin n) := by
    simp
  have hn_card : Fintype.card (Fin n) ≤ 2 * n := by
    rw [Fintype.card_fin]
    omega
  exact ((emptyCNF n).branch_domainExaminationBound_parityRowSystem_le (k := 3)
    ([] : List (Fin (emptyCNF n).length → Bool)) hF D univ hlen hn_card).1

-- 6. Concrete check of `CNF.initialRowWeightBound_le_mul_pow_clog` on `testCNF` (`n = 2`, `m = 2`,
--    `B = 1`, `C_B = 1`, `β_B = 0`).
example :
    initialRowWeightBound 1 testCNF.length ≤
      CNF.initialRowWeightCoeff 1 0 * Nat.clog 2 (Fintype.card (Fin 2)) ^ (2 * 0 + 3) :=
  CNF.initialRowWeightBound_le_mul_pow_clog (by decide) (by decide) (by decide)

-- 7. Unconditional schedule discharge `CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow`
--    at `k = 3`, `C_B = 1`, `β_B = 1`.
example :
    ∃ N₀ : ℕ, 20 ≤ N₀ ∧
      ∀ n ≥ N₀,
        let φ := emptyCNF n
        let W := initialRowWeightBound 1 φ.length
        let b₀ := CNF.parityBranchThreshold 3 W (Fintype.card (Fin n))
        ∀ b : Fin n → Bool,
          Nonempty
            (ReplacementDesign
              (branchAugmentedScope
                (heavyVars univ (univ : Finset (Fin ([] : List (Fin φ.length → Bool)).length))
                  (fun j => equationScope (φ.parityRowSystem [] j)) b₀)
                (emptyCNFEquiv n b₀) univ (φ.parityRowSystem []) b)
              (numNodes n) (numGroups n) (intervalStart (2 * 1 + 5) n)
              (rowBound (2 * 1 + 5) n) (tauRat n)) := by
  obtain ⟨N₀, hN₀20, hsched⟩ := CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow 3 1 1
  refine ⟨N₀, hN₀20, fun n hn => ?_⟩
  intro φ W b₀ b
  have hk : ∀ c ∈ φ, c.length ≤ 3 := by simp [φ, emptyCNF]
  have hcard : N₀ ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hn
  have hm : φ.length ≤ 1 * Fintype.card (Fin n) := by simp [φ, emptyCNF]
  have hB : 1 ≤ 1 * Nat.clog 2 (Fintype.card (Fin n)) ^ 1 := by
    rw [Fintype.card_fin, one_mul, pow_one]
    have : 2 ^ 0 < n := by omega
    exact (Nat.lt_clog_iff_pow_lt one_lt_two).mpr this
  have hW : ∀ r ∈ ([] : List (Fin φ.length → Bool)), weight r ≤ W := by simp
  have hlen : ([] : List (Fin φ.length → Bool)).length ≤ 6 * Fintype.card (Fin n) := by simp
  exact (hsched hk hcard hm hB le_rfl hW hlen (emptyCNFEquiv n b₀)).2.2.2 b |>.2

end Cslib.Complexity.SubexponentialSAT.SparseParityScheduleTests
