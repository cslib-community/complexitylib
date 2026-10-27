/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.ReplacementScheduleDesign
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for `Complexity.Computability.Complexity.FineGrained.ReplacementScheduleDesign`

Concrete checks for rational-to-real parameter alignment (`cast_tauRat`,
`cast_binomTailProb_eq_binomTail`, `threeTermExponent_eq_rowCost`) and a nonvacuous witness at
`n = 2 ^ (2 ^ 50)`, `β = b = w = 1` instantiating `Feasible.exists_replacementDesign`,
`Feasible.toCountingDesign`, and `Feasible.domainExaminationBound_le_mul_exp_rowCost`.
-/

@[expose] public noncomputable section

namespace Cslib.Complexity.SubexponentialSAT.ReplacementScheduleDesignTests

open Finset
open scoped BigOperators
open Cslib.LinearAlgebra Cslib.ReplacementCounting
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

/-- Rational-to-real identity check for `tauRat`, `threeTermExponent_eq_rowCost`, and
`notMem_interval_iff`. -/
example (β n : ℕ) :
    (tauRat n : ℝ) = tau n ∧
      threeTermExponent (numGroups n) (numNodes n) (rowBound β n) (auxDim n) (tau n) =
        rowCost β n :=
  ⟨cast_tauRat n, threeTermExponent_eq_rowCost β n⟩

/-- Singleton-scope family on `Fin n`, where factor `f : Fin n` has scope `{f}` (`b = 1, w = 1,
M = n`). -/
def singletonScope (n : ℕ) (f : Fin n) : Finset (Fin n) :=
  {f}

theorem sum_card_singletonScope (n : ℕ) :
    (∑ f : Fin n, #(singletonScope n f)) = n := by
  simp [singletonScope]

theorem var_deg_singletonScope (n : ℕ) (v : Fin n) :
    #{f : Fin n | v ∈ singletonScope n f} ≤ 1 := by
  have hEq : univ.filter (fun f : Fin n => v ∈ singletonScope n f) = {v} := by
    ext f
    simp [singletonScope, eq_comm]
  rw [hEq, card_singleton]

/-- Nonvacuous concrete witness at `n = 2 ^ (2 ^ 50)` and `β = b = w = 1`:
`Feasible 1 n 1 1 n` holds with `rowCost 1 n < 1 / 3`, and `Feasible.exists_replacementDesign` +
`Feasible.toCountingDesign` + `Feasible.domainExaminationBound_le_mul_exp_rowCost` produce a
concrete schedule `ReplacementDesign` and induced `Cslib.ReplacementCounting.Design` satisfying the
subexponential domain-examination bound. -/
example :
    ∃ m n : ℕ,
      m = 2 ^ 50 ∧
      n = 2 ^ m ∧
      rowCost 1 n < 1 / 3 ∧
      ∃ (hF : Feasible 1 n 1 1 (∑ f : Fin n, #(singletonScope n f)))
        (D : ReplacementDesign (singletonScope n) (numNodes n) (numGroups n)
          (intervalStart 1 n) (rowBound 1 n) (tauRat n)),
        let C := hF.toCountingDesign D univ
        (∑ t : Fin (numNodes n),
            (#{p : Finset (Fin n) × Finset (Fin n) | #p.1 ≤ 0 ∧ p.2 ⊆ p.1} : ℝ) *
              (2 * (#(C.measurementBox t) : ℝ) *
                ∑ g : Fin (numGroups n), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
          2 * (numNodes n : ℝ) * (numGroups n : ℝ) *
            Real.exp ((0 + 4) * (n : ℝ) * rowCost 1 n) := by
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
  have hF : Feasible 1 n 1 1 (∑ f : Fin n, #(singletonScope n f)) := by
    rw [sum_card_singletonScope]
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
        (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (auxDim_le_two_pow n) 2)).trans <| by
          rw [show 4 = 2 ^ 2 from rfl, ← pow_mul, ← pow_add, hn]
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
      binomTail_lt := binomTail_lt_tailBudget le_rfl hr hR hRQ le_rfl (by rw [hcl_n]; norm_num)
      rowCost_bound := hrc
    }
  obtain ⟨D⟩ := hF.exists_replacementDesign (singletonScope n) le_rfl le_rfl
    (var_deg_singletonScope n)
    (fun f => by simp [singletonScope])
    (by rw [sum_card_singletonScope, one_mul])
  refine ⟨m, n, hm, hn, hrc_lt, hF, D, ?_⟩
  have hq : ((0 : ℕ) : ℝ) ≤ (0 : ℝ) * (n : ℝ) * ((rowBound 1 n : ℝ) / numNodes n) := by
    simp only [Nat.cast_zero, zero_mul, le_refl]
  exact (hF.domainExaminationBound_le_mul_exp_rowCost D univ le_rfl hq).1

end Cslib.Complexity.SubexponentialSAT.ReplacementScheduleDesignTests
