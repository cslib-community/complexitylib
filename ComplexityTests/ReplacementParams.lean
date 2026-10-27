/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.Complexity.FineGrained.ReplacementParams
import Complexity.Foundations.Combinatorics.BinomialTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Concrete checks for biased Binomial Hoeffding tails and the Lemma 4.8 parameter schedule

Exercises `Complexity.Foundations.Combinatorics.BinomialTail` on boundary (`s = 0`, `Q = 0`) and
biased (`p = 1 / 4`, both signs of `s`, and exact rational `Q = 4` tail mass) inputs, and exercises
`Complexity.Computability.Complexity.FineGrained.ReplacementParams` on both a small-`n` negative
control (`n = 20`) and an explicit feasible point `n = 2 ^ (2 ^ 50)` with `rowCost 1 n < 1 / 3`.
-/

namespace ComplexityTests.ReplacementParams

open Cslib Cslib.Complexity.SubexponentialSAT Cslib.Complexity.SubexponentialSAT.ReplacementParams
open Finset

/-! ### Biased Bernoulli MGF and Binomial Hoeffding tail bounds -/

-- Tightness of Hoeffding's Bernoulli MGF bound at `s = 0` for biased `p = 1 / 4`.
example :
    (1 - (1 / 4 : ℝ)) * Real.exp (-0 * (1 / 4)) + (1 / 4) * Real.exp (0 * (1 - 1 / 4)) =
      Real.exp (0 ^ 2 / 8) := by
  norm_num

-- Positive- and negative-`s` biased MGF bounds at `p = 1 / 4` (`r = 2` in `(r - 1) / (2 r)`).
example :
    (3 / 4 : ℝ) * Real.exp (-1 / 2) + (1 / 4) * Real.exp (3 / 2) ≤ Real.exp (1 / 2) := by
  have h := one_sub_mul_exp_add_mul_exp_le (p := 1 / 4) (by norm_num) (by norm_num) 2
  exact (le_of_eq (by ring_nf)).trans (h.trans_eq (by norm_num))

example :
    (3 / 4 : ℝ) * Real.exp 1 + (1 / 4) * Real.exp (-3) ≤ Real.exp 2 := by
  have h := one_sub_mul_exp_add_mul_exp_le (p := 1 / 4) (by norm_num) (by norm_num) (-4)
  exact (le_of_eq (by ring_nf)).trans (h.trans_eq (by norm_num))

-- Degenerate `Q = 0` Binomial tail sum evaluates to `1 ≤ 2 * exp 0`.
example :
    (∑ k ∈ range (0 + 1) with (0 : ℝ) ≤ |((k : ℕ) : ℝ) - (0 : ℕ) * (1 / 4 : ℝ)|,
      ((0 : ℕ).choose k : ℝ) * (1 / 4) ^ k * (1 - 1 / 4) ^ (0 - k)) = 1 := by
  have hset : (range (0 + 1)).filter
      (fun k : ℕ => (0 : ℝ) ≤ |((k : ℕ) : ℝ) - (0 : ℕ) * (1 / 4 : ℝ)|) = {0} := by
    ext k
    simp only [zero_add, mem_filter, mem_range, Nat.lt_one_iff, mem_singleton,
      and_iff_left_iff_imp, implies_true, abs_nonneg]
  rw [hset, sum_singleton]; norm_num

-- Exact biased `Bin(4, 1 / 4)` mass outside `{1}` is `37 / 64 ≤ 2 * exp (-1 / 8)`.
example :
    (∑ k ∈ range 5 with k ∉ ({1} : Finset ℕ),
      ((4 : ℕ).choose k : ℝ) * (1 / 4) ^ k * (1 - 1 / 4) ^ (4 - k)) = 37 / 64 ∧
      (37 / 64 : ℝ) ≤ 2 * Real.exp (-1 / 8) := by
  have hexact : (∑ k ∈ range 5 with k ∉ ({1} : Finset ℕ),
      ((4 : ℕ).choose k : ℝ) * (1 / 4) ^ k * (1 - 1 / 4) ^ (4 - k)) = 37 / 64 := by
    have hsplit := sum_filter_add_sum_filter_not (range 5) (fun k => k ∉ ({1} : Finset ℕ))
      (fun k => ((4 : ℕ).choose k : ℝ) * (1 / 4) ^ k * (1 - 1 / 4) ^ (4 - k))
    have hall := sum_choose_mul_pow_eq_one 4 (1 / 4 : ℝ)
    have hin : (∑ k ∈ range 5 with ¬k ∉ ({1} : Finset ℕ),
        ((4 : ℕ).choose k : ℝ) * (1 / 4) ^ k * (1 - 1 / 4) ^ (4 - k)) = 27 / 64 := by
      have hset : (range 5).filter (fun k => ¬k ∉ ({1} : Finset ℕ)) = {1} := by decide
      rw [hset, sum_singleton]; norm_num
    linarith
  refine ⟨hexact, ?_⟩
  have htail := sum_filter_notMem_choose_mul_pow_le 4 ({1} : Finset ℕ) (p := 1 / 4) (t := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) fun k _ hk => by
      obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp hk
      have h4 : ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 := by norm_num
      have hk0 : 0 < k := (Nat.cast_lt (α := ℝ)).mp (by rw [Nat.cast_zero]; linarith)
      have hk2 : k < 2 := (Nat.cast_lt (α := ℝ)).mp (by rw [Nat.cast_ofNat]; linarith)
      simp only [mem_singleton, show k = 1 by omega]
  exact (le_of_eq hexact.symm).trans (htail.trans_eq (by norm_num))

/-! ### Replacement parameter schedule: small-`n` negative control and concrete feasible point -/

-- At `n = 20` (`λ = 5`, `ν = 3`), `numGroups 20 = 0 < 2`, so `Feasible 1 20 1 1 20` fails.
example : numGroups 20 = 0 ∧ numNodes 20 = 0 ∧ ¬Feasible 1 20 1 1 20 := by
  have hcl20 : Nat.clog 2 20 = 5 :=
    le_antisymm ((Nat.clog_le_iff_le_pow one_lt_two).mpr (by norm_num))
      (Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by norm_num)))
  have hcl5 : Nat.clog 2 5 = 3 :=
    le_antisymm ((Nat.clog_le_iff_le_pow one_lt_two).mpr (by norm_num))
      (Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by norm_num)))
  have hsq5 : (5 : ℕ).sqrt = 2 :=
    le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by norm_num))) (Nat.le_sqrt.mpr (by norm_num))
  have hr : numGroups 20 = 0 := by unfold numGroups; rw [hcl20, hcl5, hsq5]; norm_num
  have hQ : numNodes 20 = 0 := by unfold numNodes; rw [hcl20, hcl5]
  exact ⟨hr, hQ, fun hf => by have := hf.two_le_numGroups; omega⟩

-- At `n = 2 ^ (2 ^ 50)` and `β = b = w = 1`, `Feasible` holds and `rowCost 1 n < 1 / 3`.
example : ∃ m n : ℕ, m = 2 ^ 50 ∧ n = 2 ^ m ∧ numGroups n = 13421 ∧
    numNodes n = 175921860444 ∧ rowBound 1 n = 134217728 ∧
    Feasible 1 n 1 1 n ∧ rowCost 1 n < 1 / 3 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 ^ 50 := ⟨2 ^ 50, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 ^ m := ⟨2 ^ m, rfl⟩
  have hcl_n : Nat.clog 2 n = 2 ^ 50 := by rw [hn, Nat.clog_pow 2 m one_lt_two, hm]
  have hcl_cl : Nat.clog 2 (Nat.clog 2 n) = 50 := by
    rw [hcl_n]; exact Nat.clog_pow 2 50 one_lt_two
  have hr_eq : numGroups n = 13421 := by
    unfold numGroups; rw [hcl_cl, hcl_n]
    have hsq : (2 ^ 50 : ℕ).sqrt = 2 ^ 25 :=
      le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by norm_num)))
        (Nat.le_sqrt.mpr (by norm_num))
    rw [hsq]; norm_num
  have hQ_eq : numNodes n = 175921860444 := by unfold numNodes; rw [hcl_cl, hcl_n]; norm_num
  have hR_eq : rowBound 1 n = 134217728 := by
    unfold rowBound; rw [hcl_n]
    have hsq : (2 ^ 50 - 1 : ℕ).sqrt = 2 ^ 25 - 1 :=
      le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by norm_num)))
        (Nat.le_sqrt.mpr (by norm_num))
    simp only [show (2 ^ 50 : ℕ) ≠ 0 by positivity, ↓reduceIte, hsq]; norm_num
  have hr : 2 ≤ numGroups n := by rw [hr_eq]; norm_num
  have hR : 32 ≤ rowBound 1 n := by rw [hR_eq]; norm_num
  have hRQ : 6 * rowBound 1 n ≤ numNodes n := by rw [hR_eq, hQ_eq]; norm_num
  have hsub := interval_subset_range (β := 1) hr (by omega) (by omega)
  have hrc := rowCost_le hr hR hRQ
  have hrc_lt : rowCost 1 n < 1 / 3 := hrc.trans_lt <| by
    rw [hcl_cl, hcl_n, show ((2 ^ 50 : ℕ) : ℝ) = ((2 : ℝ) ^ 25) ^ 2 by norm_num,
      Real.sqrt_sq (by positivity)]; norm_num
  refine ⟨m, n, hm, hn, hr_eq, hQ_eq, hR_eq, {
    twenty_le := by
      rw [hn]; exact (by norm_num : 20 ≤ 2 ^ 5).trans
        (Nat.pow_le_pow_right two_pos (by rw [hm]; norm_num))
    two_le_numGroups := hr
    thirtyTwo_le_rowBound := hR
    six_mul_rowBound_le_numNodes := hRQ
    tau_pos := by unfold tau; rw [hr_eq, hcl_n]; positivity
    tau_le_half := by unfold tau; rw [hr_eq, hcl_n]; norm_num
    auxDim_le := auxDim_le_two_pow n
    aux_balance := (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (auxDim_le_two_pow n) 2)).trans <| by
      rw [show 4 = 2 ^ 2 from rfl, ← pow_mul, ← pow_add, hn]
      exact Nat.pow_le_pow_right two_pos (by rw [Nat.clog_pow 2 m one_lt_two, hm]; norm_num)
    var_balance := by
      rw [hQ_eq, hr_eq, hn]; exact (by norm_num : 2 * 175921860444 * 13421 ^ 2 ≤ 2 ^ 66).trans
        (Nat.pow_le_pow_right two_pos (by rw [hm]; norm_num))
    card_interval_eq := card_interval (by omega)
    interval_subset := hsub
    mem_interval_of_close := fun k hk =>
      ⟨mem_interval_of_abs_sub_le hr hR (by omega) hk,
        Nat.lt_succ_iff.mp (mem_range.mp (hsub (mem_interval_of_abs_sub_le hr hR (by omega) hk)))⟩
    binomTail_lt := binomTail_lt_tailBudget le_rfl hr hR hRQ le_rfl (by rw [hcl_n]; norm_num)
    rowCost_bound := hrc }, hrc_lt⟩

end ComplexityTests.ReplacementParams
