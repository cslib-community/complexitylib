/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: local-only (test driver)

import Complexity.Computability.Complexity.FineGrained.SparseCountingScale

/-!
# Tests for `SparseCountingScale`

Concrete evaluations of `Nat.clog 2`, `ReplacementParams.numGroups`, and `leafOccurrenceBound`,
sharpness and non-monotonicity witnesses for the integer floor schedule, and nonvacuous `k = 3`
instantiations of tree-exponent big-O, Lemma 4.8 feasibility, quasi-polynomial query absorption,
`sparse_formula_time_bound`, and `prop64_time_bound`.
-/

namespace Cslib.Complexity.SubexponentialSAT.SparseCountingScale.Tests

open Filter Asymptotics
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams
open Cslib.Complexity.SubexponentialSAT.SparseCountingScale

-- Concrete `decide` checks on `Nat.clog 2`, `Nat.clog 2 ∘ Nat.clog 2`, and `leafOccurrenceBound`.
example : [Nat.clog 2 0, Nat.clog 2 1, Nat.clog 2 2, Nat.clog 2 3, Nat.clog 2 4,
    Nat.clog 2 5, Nat.clog 2 16, Nat.clog 2 20, Nat.clog 2 64, Nat.clog 2 1024] =
    [0, 0, 1, 2, 2, 3, 4, 5, 6, 10] := by decide

example : [2, 3, 4, 5, 16, 20, 64, 1024].map (fun n => Nat.clog 2 (Nat.clog 2 n)) =
    [0, 1, 1, 2, 2, 3, 3, 4] := by decide

example : leafOccurrenceBound 5 3 2 = 180 ∧ leafOccurrenceBound 7 1 10 = 7 := by decide

-- Concrete floor-inequality checks at explicit `n` via `decide` and `numGroups` values.
example : 1 ^ 2 * Nat.clog 2 (Nat.clog 2 4) ^ 4 ≤ Nat.clog 2 4 ∧
    Nat.clog 2 4 < (1 + 1) ^ 2 * Nat.clog 2 (Nat.clog 2 4) ^ 4 := by decide

example : 0 ^ 2 * Nat.clog 2 (Nat.clog 2 20) ^ 4 ≤ Nat.clog 2 20 ∧
    Nat.clog 2 20 < (0 + 1) ^ 2 * Nat.clog 2 (Nat.clog 2 20) ^ 4 := by decide

example : [numGroups 0, numGroups 2, numGroups 3, numGroups 4, numGroups 20, numGroups 1024] =
    [0, 0, 1, 1, 0, 0] := by
  simp only [List.cons.injEq, and_true]
  exact ⟨numGroups_of_lt_three (by decide), numGroups_of_lt_three (by decide),
    (numGroups_eq_iff (by decide)).mpr (by decide),
    (numGroups_eq_iff (by decide)).mpr (by decide),
    (numGroups_eq_iff (by decide)).mpr (by decide),
    (numGroups_eq_iff (by decide)).mpr (by decide)⟩

-- Non-monotonicity witness: `s_n = 2` at `λ_n = 2^19`, then drops back to `1` at `λ_n = 2^19 + 1`
-- when `ν_n` steps from `19` to `20`.
example : numGroups (2 ^ 524288) = 2 ∧ numGroups (2 ^ 524289) = 1 := by
  refine ⟨(numGroups_eq_iff ?_).mpr ?_, (numGroups_eq_iff ?_).mpr ?_⟩ <;>
    (rw [Nat.clog_pow 2 _ one_lt_two]; decide)

-- Sharpness of the permanent threshold `640000 ≤ Nat.clog 2 n`:
-- `λ_n = 639999` still gives `s_n = 1`, whereas `λ_n = 640000` reaches `s_n = 2` permanently.
example : numGroups (2 ^ 639999) = 1 ∧ numGroups (2 ^ 640000) = 2 := by
  refine ⟨(numGroups_eq_iff ?_).mpr ?_, (numGroups_eq_iff ?_).mpr ?_⟩ <;>
    (rw [Nat.clog_pow 2 _ one_lt_two]; decide)

-- Nonvacuous instantiation of `n / numGroups n =O[atTop] interpolationScale` and explicit `C = 16`
-- bound together with the `d = 3` polynomial leaf-factor bound.
example : ∃ (C : ℝ) (N : ℕ), 0 < C ∧
    (∀ n : ℕ, N ≤ n →
      (n : ℝ) / (numGroups n : ℝ) ≤ C * interpolationScale n ∧
      ((n : ℝ) + (numGroups n : ℝ) + 1) ^ 3 * (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) ≤
        (2 : ℝ) ^ (17 * interpolationScale n)) ∧
    0 < interpolationScale (2 ^ 640000) ∧
    ((2 ^ 640000 : ℕ) : ℝ) / (numGroups (2 ^ 640000) : ℝ) ≤
      16 * interpolationScale (2 ^ 640000) := by
  obtain ⟨c, hc_pos, hc_ev⟩ := isBigO_div_numGroups_interpolationScale.exists_pos
  rw [IsBigOWith] at hc_ev
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hc_ev.and (eventually_poly_mul_two_pow_div_numGroups_le 3))
  refine ⟨c, N, hc_pos, fun n hn => ?_, ?_, ?_⟩
  · obtain ⟨hbig, hleaf⟩ := hN n hn
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (interpolationScale_nonneg n)] at hbig
    exact ⟨hbig, hleaf⟩
  · exact interpolationScale_pos ((by decide : 1 ≤ 5).trans
      (five_le_of_two_le_numGroups (two_le_numGroups_of_pow_le le_rfl)))
  · exact div_numGroups_le_interpolationScale_of_clog_ge
      (by rw [Nat.clog_pow 2 _ one_lt_two])

-- Nonvacuous `k = 3` instantiation chaining Lemma 6.3's occurrence bound (`β = 3`) into Lemma 4.8
-- replacement feasibility (`ReplacementParams.Feasible`) and into both linear and Lemma 6.1
-- polynomial-exponent (`P ≤ 20000 * B² * μ²`) quasi-polynomial query absorption.
example : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    2 ≤ numGroups n ∧
    leafOccurrenceBound 8 3 (numGroups n) ≤ Nat.clog 2 n ^ 3 ∧
    Feasible 3 n (leafOccurrenceBound 8 3 (numGroups n)) 3
      (leafOccurrenceBound 8 3 (numGroups n) * n) ∧
    (∀ m P : ℕ,
      m ≤ leafOccurrenceBound 8 3 (numGroups n) * n →
      P ≤ 24 * Nat.clog 2 (2 * m + 2) →
      (3 * (n : ℝ) * (2 * (m : ℝ)) ^ P + 1) ≤ (2 : ℝ) ^ ((1 / 8 : ℝ) * interpolationScale n)) ∧
    (∀ m P : ℕ,
      m ≤ leafOccurrenceBound 8 3 (numGroups n) * n →
      P ≤ 20000 * leafOccurrenceBound 8 3 (numGroups n) ^ 2 * Nat.clog 2 (2 * m + 4) ^ 2 →
      (3 * (n : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1) ≤
        (2 : ℝ) ^ ((1 / 8 : ℝ) * interpolationScale n)) := by
  have hε : (0 : ℝ) < 1 / 8 := by norm_num
  have hk1 : 1 ≤ 3 := by decide
  obtain ⟨N, hN⟩ := eventually_atTop.mp <|
    (eventually_ge_atTop 8).and <|
      eventually_two_le_numGroups.and <|
        (eventually_leafOccurrenceBound_le 8 hk1).and <|
          (eventually_leafOccurrenceBound_feasible 8 hk1).and <|
            (eventually_query_overhead_le 1 3 24 hε).and
              (eventually_query_overhead_poly_le 1 3 20000 2 2 hε)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn8, hs2, hocc, hfeas, hq_lin, hq_poly⟩ := hN n hn
  have hB_pos : 1 ≤ leafOccurrenceBound 8 3 (numGroups n) := by
    change 0 < leafOccurrenceBound 8 3 (numGroups n)
    unfold leafOccurrenceBound
    have : 0 < numGroups n := by omega
    positivity
  have h3_lam : 3 ≤ Nat.clog 2 n ^ 3 := by
    have h3 : 3 ≤ Nat.clog 2 n :=
      (by decide : 3 = Nat.clog 2 8).trans_le (Nat.clog_mono_right 2 hn8)
    exact h3.trans (Nat.le_self_pow (by decide) _)
  have hB : leafOccurrenceBound 8 3 (numGroups n) ≤ 1 * Nat.clog 2 n ^ 3 := by
    simpa only [one_mul] using hocc
  exact ⟨hs2, hocc,
    hfeas hB_pos le_rfl (by decide) h3_lam (Nat.le_mul_of_pos_left n hB_pos) le_rfl,
    fun m P hm hP => hq_lin m _ P hm hB hP,
    fun m P hm hP => hq_poly m _ P hm hB hP⟩

-- Nonvacuous instantiation of `sparse_formula_time_bound` over `m ≤ 8 * ⌈log₂ n⌉ ^ 3 * n`,
-- exercising both the `n < 5` fallback (`n = 4, m = 40`) and the active Lemma 6.1 + Lemma 6.2
-- sparse branch (`P = 20000 * B ^ 2 * μ ^ 2`) at the boundary `n = 5, m = 8 * ⌈log₂ 5⌉ ^ 3 * 5`.
example : ∃ sampleSparseRuntime : ℕ → ℕ → ℝ,
    40 ≤ 8 * Nat.clog 2 4 ^ 3 * 4 ∧ (2 : ℝ) ^ (4 : ℕ) < sampleSparseRuntime 4 40 ∧
    1080 ≤ 8 * Nat.clog 2 5 ^ 3 * 5 ∧ (2 : ℝ) ^ (27 : ℕ) < sampleSparseRuntime 5 1080 ∧
    ∃ (C_sparse d_sparse : ℕ) (A_sparse : ℝ), 0 < A_sparse ∧
      ∀ n m : ℕ, m ≤ 8 * Nat.clog 2 n ^ 3 * n → sampleSparseRuntime n m ≤
        (C_sparse : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_sparse *
          (2 : ℝ) ^ (A_sparse * interpolationScale n) := by
  let sampleSparseRuntime : ℕ → ℕ → ℝ := fun n m =>
    if n < 5 then 4 * ((n : ℝ) + (m : ℝ) + 1) ^ 2 * (2 : ℝ) ^ n
    else
      let P := 20000 * (8 * Nat.clog 2 n ^ 3) ^ 2 * Nat.clog 2 (2 * m + 4) ^ 2
      (2 : ℝ) ^ (3 * (Nat.clog 2 n : ℝ) ^ 2) + ((n : ℝ) + (m : ℝ) + 1) ^ 2 *
        (3 * (n : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1) * (2 : ℝ) ^ (6 * interpolationScale n)
  refine ⟨sampleSparseRuntime, by decide, ?_, by decide, ?_, ?_⟩
  · simp only [sampleSparseRuntime, show 4 < 5 by decide, ↓reduceIte]; norm_num
  · simp only [sampleSparseRuntime, show ¬ 5 < 5 by decide, ↓reduceIte,
      show Nat.clog 2 5 = 3 by decide, Nat.cast_ofNat]
    rw [show (2 : ℝ) ^ (27 : ℕ) = (2 : ℝ) ^ ((3 : ℝ) * (3 : ℝ) ^ 2) by
      rw [← Real.rpow_natCast]; norm_num]
    exact lt_add_of_pos_right _ (by positivity)
  · refine sparse_formula_time_bound 5 4 2 3 2 2 8 3 20000 2 2 6 sampleSparseRuntime
      fun n m hm => ?_
    by_cases hcond : n < 5
    · exact Or.inl ⟨hcond, by simp only [sampleSparseRuntime, hcond, ↓reduceIte, Nat.cast_ofNat,
        le_rfl]⟩
    · refine Or.inr ⟨by omega, 8 * Nat.clog 2 n ^ 3,
        20000 * (8 * Nat.clog 2 n ^ 3) ^ 2 * Nat.clog 2 (2 * m + 4) ^ 2, hm, le_rfl, le_rfl, ?_⟩
      simp only [sampleSparseRuntime, hcond, ↓reduceIte, Nat.cast_ofNat, le_rfl]

-- Nonvacuous instantiation of `prop64_time_bound` on a concrete piecewise `3`-SAT runtime model
-- exercising both fallback sub-regimes (`n = 4 < 5` and `n = 20 ≥ 5` with `s_20 = 0 < 2`) and the
-- active sparsification-tree + sparse-leaf branch (`n = 2 ^ 640000`).
example : ∃ sampleRuntime : ℕ → ℕ → ℝ,
    (2 : ℝ) ^ (4 : ℕ) < sampleRuntime 4 40 ∧
    (2 : ℝ) ^ (20 : ℕ) < sampleRuntime 20 40 ∧
    0 < sampleRuntime (2 ^ 640000) 100 ∧
    ∃ (C_total d_total : ℕ) (A_total : ℝ), 0 < A_total ∧
      ∀ n m : ℕ, sampleRuntime n m ≤
        (C_total : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_total *
          (2 : ℝ) ^ (A_total * interpolationScale n) := by
  let sampleRuntime : ℕ → ℕ → ℝ := fun n m =>
    if n < 5 ∨ numGroups n < 2 then
      4 * ((n : ℝ) + (m : ℝ) + 1) ^ 2 * (2 : ℝ) ^ n
    else
      let B_n := leafOccurrenceBound 8 3 (numGroups n)
      let m_leaf := B_n * n
      let P_leaf := 12 * Nat.clog 2 (2 * m_leaf + 4)
      5 * ((n : ℝ) + (numGroups n : ℝ) + 1) ^ 2 *
        (2 : ℝ) ^ (n / numGroups n + 1 : ℕ) *
        (((n : ℝ) + (m : ℝ) + 1) ^ 3 +
          ((n : ℝ) + (m_leaf : ℝ) + 1) ^ 2 *
            (3 * (n : ℝ) * (2 * (m_leaf : ℝ) + 2) ^ P_leaf + 1) *
            (2 : ℝ) ^ (6 * interpolationScale n))
  refine ⟨sampleRuntime, ?_, ?_, ?_, ?_⟩
  · have hcond : 4 < 5 ∨ numGroups 4 < 2 := Or.inl (by decide)
    simp only [sampleRuntime, hcond, ↓reduceIte]
    norm_num
  · have hs20 : numGroups 20 = 0 := (numGroups_eq_iff (by decide)).mpr (by decide)
    have hcond : 20 < 5 ∨ numGroups 20 < 2 := Or.inr (by rw [hs20]; decide)
    simp only [sampleRuntime, hcond, ↓reduceIte]
    norm_num
  · have hs2 : 2 ≤ numGroups (2 ^ 640000) := two_le_numGroups_of_pow_le le_rfl
    have hn5 : 5 ≤ 2 ^ 640000 := five_le_of_two_le_numGroups hs2
    have hcond : ¬ (2 ^ 640000 < 5 ∨ numGroups (2 ^ 640000) < 2) := by
      rintro (h1 | h2)
      · exact (not_lt_of_ge hn5) h1
      · exact (not_lt_of_ge hs2) h2
    simp only [sampleRuntime, hcond, ↓reduceIte]
    positivity
  · refine prop64_time_bound 5 4 2 5 2 3 2 8 3 12 6 sampleRuntime fun n m => ?_
    by_cases hcond : n < 5 ∨ numGroups n < 2
    · refine Or.inl ⟨hcond, ?_⟩
      simp only [sampleRuntime, hcond, ↓reduceIte, Nat.cast_ofNat, le_rfl]
    · have hn5 : 5 ≤ n := by omega
      have hs2 : 2 ≤ numGroups n := by omega
      refine Or.inr ⟨hs2, leafOccurrenceBound 8 3 (numGroups n),
        leafOccurrenceBound 8 3 (numGroups n) * n,
        12 * Nat.clog 2 (2 * (leafOccurrenceBound 8 3 (numGroups n) * n) + 4),
        le_rfl, ?_, le_rfl, ?_⟩
      · have hpos : 0 < Nat.clog 2 n :=
          (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < n)
        exact (leafOccurrenceBound_le_mul_pow hn5).trans
          (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_right hpos (by decide)))
      · simp only [sampleRuntime, hcond, ↓reduceIte, Nat.cast_ofNat, le_rfl]

end Cslib.Complexity.SubexponentialSAT.SparseCountingScale.Tests
