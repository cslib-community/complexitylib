/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseCNFDesignSchedule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for `Complexity.Computability.Complexity.FineGrained.SparseCNFDesignSchedule`

Concrete checks for Section 6.3 candidate/final degree budgets (`branchParityRowDegreeBudget_le`,
`greedyCandidateDegreeBudget_le`), greedy row-weight preservation
(`weight_le_max_of_append_testRow`), free-variable dimension lower bounds
(`card_le_two_mul_freeVar_of_heavyVars_parityRowSystem`), a concrete schedule witness at
`n = 2 ^ (2 ^ 50)` instantiating `Feasible.exists_branchParityRow_replacementDesign`,
`Feasible.branchParityRow_domainExaminationBound_le`,
`Feasible.greedyCandidate_domainExaminationBound_le`, and
`sum_branchParityRow_domainExaminationBound_le`, and instantiations of the uniform schedule
recovery theorems (`exists_schedule_branchParityRow_replacementDesign`,
`exists_schedule_design_commonZeroCount_parityRowSystem_eq`,
`exists_schedule_design_numPassing_eq`, `exists_schedule_design_modelCountOn_eq_greedy`, and
`exists_initialTests_and_schedule_design_modelCountOn_eq`).
-/

@[expose] public noncomputable section

namespace Cslib.Complexity.SubexponentialSAT.SparseCNFDesignScheduleTests

open Finset Polynomial Cslib.BitString Cslib.BalancedSchedules Cslib.LinearAlgebra
  Cslib.ReplacementCounting Cslib.Logic.PL
open Cslib.Complexity.SubexponentialSAT.ReplacementParams
open scoped BigOperators

/-! ### 1. Concrete degree-budget and row-weight checks -/

/-- Concrete check of `branchParityRowDegreeBudget_le` and `greedyCandidateDegreeBudget_le` for
`k = 3, c = 6, n = 20, n' = 12, m = 100`. -/
example :
    3 * (100 + 2 * (branchPrecision 20 - 1)) ≤ (3 * (2 * 6 + 4)) * 12 ∧
      3 * (100 + 2 * (branchPrecision 20 - 1)) ≤ (16 * 3) * 12 :=
  ⟨branchParityRowDegreeBudget_le (k := 3) (c := 6) (n := 20) (n' := 12) (m := 100)
      (by decide) (by decide),
    greedyCandidateDegreeBudget_le (k := 3) (n := 20) (n' := 12) (m := 100)
      (by decide) (by decide)⟩

/-- Concrete 2-CNF over `Fin 3`: `(x₀ ∨ ¬x₁) ∧ (x₁ ∨ x₂)`. -/
def sampleCNF3 : CNF (Fin 3) :=
  [[(0, true), (1, false)], [(1, true), (2, true)]]

/-- Concrete check of `weight_le_max_of_append_testRow` on a 1-step greedy sequence over
`sampleCNF3`. -/
example :
    let γ₀ : Fin 1 → Fin sampleCNF3.length × Bool := fun _ => (⟨0, by decide⟩, true)
    let A : ℕ → List (Fin sampleCNF3.length → Bool) :=
      fun j => Nat.rec [![true, false]] (fun _ acc => acc ++ [testRow γ₀]) j
    ∀ (j : ℕ) (r_row : Fin sampleCNF3.length → Bool), r_row ∈ A j → weight r_row ≤ max 1 1 := by
  intro γ₀ A
  refine weight_le_max_of_append_testRow A ?_ (fun _ => γ₀) (fun _ => rfl)
  intro r_row hr
  change r_row ∈ [![true, false]] at hr
  rcases List.mem_singleton.mp hr with rfl
  decide

/-- Concrete check of `card_le_two_mul_freeVar_of_heavyVars_parityRowSystem` on `sampleCNF3` with
an empty row list (`b₀ = 1, s_div = 2, n' = 3`). -/
example :
    let rows : List (Fin sampleCNF3.length → Bool) := []
    let S := heavyVars univ (univ : Finset (Fin rows.length))
      (fun j => equationScope (sampleCNF3.parityRowSystem rows j)) 1
    let _e : ↥(univ \ S) ≃ Fin 3 :=
      Fintype.equivFinOfCardEq (by decide)
    Fintype.card (Fin 3) ≤ 2 * 3 ∧ Fintype.card (Fin 3) / 2 ≤ 3 := by
  intro rows S e
  exact card_le_two_mul_freeVar_of_heavyVars_parityRowSystem sampleCNF3 rows
    (b₀ := 1) (s_div := 2) (by decide) (by decide) (by decide) e

/-! ### 2. Concrete schedule witness at `n = 2 ^ (2 ^ 50)` -/

private def emptyCNF (n : ℕ) : CNF (Fin n) :=
  []

private def emptyRows (n : ℕ) : List (Fin (emptyCNF n).length → Bool) :=
  []

/-- For `emptyCNF n` and `emptyRows n`, `heavyVars` at `b₀` is empty. -/
private theorem empty_heavyVars_eq_empty (n b₀ : ℕ) :
    heavyVars (univ : Finset (Fin n)) (univ : Finset (Fin (emptyRows n).length))
      (fun j => equationScope ((emptyCNF n).parityRowSystem (emptyRows n) j)) b₀ = ∅ := by
  ext v
  have hzero :
      varIncidence (univ : Finset (Fin (emptyRows n).length))
        (fun j => equationScope ((emptyCNF n).parityRowSystem (emptyRows n) j)) v = 0 := by
    rfl
  simp only [heavyVars, hzero, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_lt]
  exact Nat.zero_le b₀

private def emptyFreeEquiv (n b₀ : ℕ) :
    ↥((univ : Finset (Fin n)) \
      heavyVars univ (univ : Finset (Fin (emptyRows n).length))
        (fun j => equationScope ((emptyCNF n).parityRowSystem (emptyRows n) j)) b₀) ≃
      Fin n :=
  { toFun := fun v => v.1
    invFun := fun v => ⟨v, by rw [empty_heavyVars_eq_empty]; simp⟩
    left_inv := fun v => by ext; rfl
    right_inv := fun v => rfl }

private theorem totalIncidence_empty_branchParityRowNeutralScope (n b₀ : ℕ) (b : Fin n → Bool) :
    totalIncidence
      (univ : Finset (Fin (emptyRows n).length ⊕ Fin n))
      ((emptyCNF n).branchParityRowNeutralScope (emptyRows n)
        (heavyVars univ (univ : Finset (Fin (emptyRows n).length))
          (fun j => equationScope ((emptyCNF n).parityRowSystem (emptyRows n) j)) b₀)
        (emptyFreeEquiv n b₀) b) = n := by
  rw [CNF.totalIncidence_branchParityRowNeutralScope_eq]
  have hzero :
      totalIncidence
        (univ : Finset (Fin (emptyRows n).length))
        ((emptyCNF n).branchParityRowScope (emptyRows n)
          (heavyVars univ (univ : Finset (Fin (emptyRows n).length))
            (fun j => equationScope ((emptyCNF n).parityRowSystem (emptyRows n) j)) b₀)
          (emptyFreeEquiv n b₀) b) = 0 := rfl
  rw [hzero, zero_add]

/-- Concrete witness at `n = 2 ^ (2 ^ 50)`, `β = 1`, `b₀ = 1`, `W = 0`, `k = 3`:
instantiates `Feasible.exists_branchParityRow_replacementDesign`,
`Feasible.branchParityRow_domainExaminationBound_le`,
`Feasible.greedyCandidate_domainExaminationBound_le`, and
`sum_branchParityRow_domainExaminationBound_le`. -/
example :
    ∃ m n : ℕ,
      m = 2 ^ 50 ∧
      n = 2 ^ m ∧
      rowCost 1 n < 1 / 3 ∧
      let φ := emptyCNF n
      let rows := emptyRows n
      let S := heavyVars univ (univ : Finset (Fin rows.length))
        (fun j => equationScope (φ.parityRowSystem rows j)) 1
      let e := emptyFreeEquiv n 1
      (∀ b : Fin n → Bool,
        ∃ (hF : Feasible 1 n 2 (max 1 (3 * (0 * 2 ^ 3)))
            (totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n))
              (φ.branchParityRowNeutralScope rows S e b)))
          (D : ReplacementDesign (φ.branchParityRowNeutralScope rows S e b)
            (numNodes n) (numGroups n) (intervalStart 1 n) (rowBound 1 n) (tauRat n)),
          let d := 3 * (rows.length + 2 * (branchPrecision (Fintype.card (Fin n)) - 1))
          let q := (d * rowBound 1 n) / numNodes n
          let C := hF.toCountingDesign D univ
          (∑ t : Fin (numNodes n),
              (#{p : Finset (Fin n) × Finset (Fin n) | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                (2 * (#(C.measurementBox t) : ℝ) *
                  ∑ g : Fin (numGroups n), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
            2 * (numNodes n : ℝ) * (numGroups n : ℝ) *
              Real.exp (((16 * 3 + 4 : ℕ) : ℝ) * (n : ℝ) * rowCost 1 n)) ∧
      Fintype.card (Fin n) ≤ 2 * n := by
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
  have hF_base : Feasible 1 n 2 1 n := {
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
      (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left (auxDim_le_two_pow n) 2)).trans <| by
        have h6 : 6 ≤ 2 ^ 3 := by decide
        refine (Nat.mul_le_mul_right _ h6).trans ?_
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
      binomTail_lt_tailBudget le_rfl hr hR hRQ (by decide) (by rw [hcl_n]; norm_num)
    rowCost_bound := hrc
  }
  refine ⟨m, n, hm, hn, hrc_lt, ?_⟩
  intro φ rows S e
  have hM :
      totalIncidence (univ : Finset (Fin rows.length))
        (fun j => equationScope (φ.parityRowSystem rows j)) * 2 ≤
          1 * Fintype.card (Fin n) := by
    have hzero :
        totalIncidence (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) = 0 := rfl
    rw [hzero, zero_mul]
    exact Nat.zero_le _
  have hsum := sum_branchParityRow_domainExaminationBound_le φ rows
    (β := 1) (b₀ := 1) (s_div := 2) (k := 3) (c := 6)
    le_rfl le_rfl hM e (fun _ => 0) (fun _ _ => by positivity)
  refine ⟨fun b => ?_, hsum.1⟩
  have hF_b : Feasible 1 n 2 (max 1 (3 * (0 * 2 ^ 3)))
      (totalIncidence (univ : Finset (Fin rows.length ⊕ Fin n))
        (φ.branchParityRowNeutralScope rows S e b)) := by
    rw [totalIncidence_empty_branchParityRowNeutralScope n 1 b]
    exact hF_base
  have hk : ∀ c ∈ φ, c.length ≤ 3 := fun _ hc => False.elim (List.not_mem_nil hc)
  have hW : ∀ r_row ∈ rows, weight r_row ≤ 0 := fun _ hr_row => False.elim (List.not_mem_nil hr_row)
  obtain ⟨D⟩ := hF_b.exists_branchParityRow_replacementDesign hk hW e b
  refine ⟨hF_b, D, ?_⟩
  have hm_rows : rows.length ≤ 6 * Fintype.card (Fin n) := Nat.zero_le _
  exact (hF_b.greedyCandidate_domainExaminationBound_le (k := 3) φ rows D univ hm_rows hsum.1).1

/-! ### 3. Instantiation of uniform schedule recovery theorems at `β = 1` -/

/-- Nonvacuous instantiation of `exists_schedule_branchParityRow_replacementDesign`,
`exists_schedule_design_commonZeroCount_parityRowSystem_eq`,
`exists_schedule_design_numPassing_eq`,
`exists_schedule_design_modelCountOn_eq_greedy`, and
`exists_initialTests_and_schedule_design_modelCountOn_eq` at `β = 1`. -/
example :
    (∃ n₀ : ℕ, 20 ≤ n₀) ∧
    (∃ n₁ : ℕ, 20 ≤ n₁) ∧
    (∃ n₂ : ℕ, 20 ≤ n₂) ∧
    (∃ n₃ : ℕ, 20 ≤ n₃) ∧
    (∃ n₄ : ℕ, 20 ≤ n₄) := by
  obtain ⟨n₀, hn₀, _⟩ := exists_schedule_branchParityRow_replacementDesign.{0} (β := 1) le_rfl
  obtain ⟨n₁, hn₁, _⟩ :=
    exists_schedule_design_commonZeroCount_parityRowSystem_eq.{0} (β := 1) le_rfl
  obtain ⟨n₂, hn₂, _⟩ := exists_schedule_design_numPassing_eq.{0} (β := 1) le_rfl
  obtain ⟨n₃, hn₃, _⟩ := exists_schedule_design_modelCountOn_eq_greedy.{0} (β := 1) le_rfl
  obtain ⟨n₄, hn₄, _⟩ :=
    exists_initialTests_and_schedule_design_modelCountOn_eq.{0} (β := 1) le_rfl
  exact ⟨⟨n₀, hn₀⟩, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩, ⟨n₃, hn₃⟩, ⟨n₄, hn₄⟩⟩

end Cslib.Complexity.SubexponentialSAT.SparseCNFDesignScheduleTests
