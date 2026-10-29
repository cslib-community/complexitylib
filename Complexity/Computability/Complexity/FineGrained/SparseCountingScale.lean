/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.CountingScale
public import Complexity.Computability.Complexity.FineGrained.ReplacementParams
public import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Asymptotic parameter schedules for sparse and general `k`-SAT counting

In Sections 6.3 and 6.4 of OpenAI's *The Exponential Time Hypothesis is False* [OpenAI2026ETH],
satisfiability counting on a `k`-CNF with `n` variables and `m` clauses reduces via disjoint
sparsification (Lemma 6.3) to counting sparse leaf formulas at the discrete parameter schedule
`λ_n = ⌈log₂ n⌉`, `ν_n = ⌈log₂ λ_n⌉`, and `s_n = ⌊√λ_n / ν_n²⌋`. Notice that `s_n` coincides with
the replacement-matrix group count `ReplacementParams.numGroups n` of Section 4.7, equation (4.17).

This module establishes the exact integer-comparison floor characterization and sharp permanent
threshold `2 ≤ numGroups n` (`640000 ≤ ⌈log₂ n⌉`), the tree-exponent bound
`n / numGroups n = O(interpolationScale n)`, the polylogarithmic absorption
`(log n)^d = o(interpolationScale n)` underlying equation `(6.4)`, the polylogarithmic
leaf-occurrence bound `B = O_k((s_n log s_n)^{k - 1}) ≤ λ_n^k` discharging Lemma 4.8 feasibility,
and the uniform runtime-composition theorems of Section 6.3 equation `(6.4)` (on the sparse
domain `m ≤ C_B * ⌈log₂ n⌉ ^ β * n`) and Proposition 6.4 (across all `n, m : ℕ`).

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.SparseCountingScale.leafOccurrenceBound`:
  `C_k * (s * (⌈log₂ (2 s)⌉ + 1)) ^ (k - 1)`, the per-variable occurrence cap of Lemma 6.3
  at `σ = 1 / s`.

## Main results

* `numGroups_floor_bounds`, `le_numGroups_iff`, `numGroups_eq_iff`: exact integer comparison
  characterization `s_n² ν_n⁴ ≤ λ_n < (s_n + 1)² ν_n⁴` for `s_n = ReplacementParams.numGroups n`
  (from `ReplacementParams.sq_mul_pow_four_le_clog` and
  `ReplacementParams.clog_lt_succ_sq_mul_pow_four`).
* `two_le_numGroups_of_clog_ge`, `eventually_two_le_numGroups`, `tendsto_numGroups_atTop`:
  `2 ≤ numGroups n` permanently once `640000 ≤ ⌈log₂ n⌉`, and `numGroups n → ∞`.
* `isBigO_div_numGroups_interpolationScale`, `eventually_div_numGroups_le`,
  `exists_eventually_poly_mul_two_pow_div_numGroups_le`: tree-exponent and leaf-factor bounds
  against `interpolationScale`.
* `isLittleO_log_pow_interpolationScale`, `isLittleO_clog_pow_interpolationScale`,
  `eventually_query_overhead_le`: polylogarithmic and quasi-polynomial query absorption.
* `eventually_leafOccurrenceBound_le`, `eventually_leafOccurrenceBound_feasible`:
  `leafOccurrenceBound C_k k (numGroups n) ≤ ⌈log₂ n⌉ ^ k` eventually for `1 ≤ k`, directly
  discharging `ReplacementParams.Feasible` at `β = k`.
* `sparse_formula_time_bound`, `prop64_time_bound`: Section 6.3 equation `(6.4)` across the
  sparse domain `m ≤ C_B * ⌈log₂ n⌉ ^ β * n` and the full Proposition 6.4 runtime composition
  across all `n, m : ℕ`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH],
  Section 6.3 equation `(6.4)` and Proposition 6.4, pp. 43–44.
-/

@[expose] public section

namespace Cslib.Complexity.SubexponentialSAT

open Filter Asymptotics
open scoped Topology

namespace SparseCountingScale

open ReplacementParams

/-! ### Integer floor characterization of `numGroups` (`s_n = ⌊√λ_n / ν_n²⌋`) -/

private theorem clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  (Nat.clog_le_iff_le_pow one_lt_two).mpr n.lt_two_pow_self.le

private theorem one_le_clog_two_iff {n : ℕ} : 1 ≤ Nat.clog 2 n ↔ 2 ≤ n := by
  change 0 < Nat.clog 2 n ↔ 2 ≤ n
  rw [Nat.lt_clog_iff_pow_lt one_lt_two]
  omega

private theorem one_le_iter_clog_two_iff {n : ℕ} :
    1 ≤ Nat.clog 2 (Nat.clog 2 n) ↔ 3 ≤ n := by
  change 0 < Nat.clog 2 (Nat.clog 2 n) ↔ 3 ≤ n
  rw [Nat.lt_clog_iff_pow_lt one_lt_two, pow_zero, Nat.lt_clog_iff_pow_lt one_lt_two]
  omega

private theorem two_le_iter_clog_two_iff {n : ℕ} :
    2 ≤ Nat.clog 2 (Nat.clog 2 n) ↔ 5 ≤ n := by
  change 1 < Nat.clog 2 (Nat.clog 2 n) ↔ 5 ≤ n
  rw [Nat.lt_clog_iff_pow_lt one_lt_two, pow_one, Nat.lt_clog_iff_pow_lt one_lt_two]
  omega

/-- For `n < 3`, `ν_n = 0` and `numGroups n = 0`. -/
theorem numGroups_of_lt_three {n : ℕ} (hn : n < 3) : numGroups n = 0 := by
  have hnu : Nat.clog 2 (Nat.clog 2 n) = 0 := by
    by_contra h
    exact (one_le_iter_clog_two_iff.mp (Nat.one_le_iff_ne_zero.mpr h)).not_gt hn
  simp only [numGroups, hnu, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.div_zero]

/-- `numGroups n ≤ √⌈log₂ n⌉` for every natural number `n`. -/
theorem numGroups_le_sqrt (n : ℕ) : numGroups n ≤ (Nat.clog 2 n).sqrt :=
  Nat.div_le_self _ _

/-- `numGroups n ≤ ⌈log₂ n⌉` for every natural number `n`. -/
theorem numGroups_le_clog (n : ℕ) : numGroups n ≤ Nat.clog 2 n :=
  (numGroups_le_sqrt n).trans (Nat.sqrt_le_self _)

/-- `numGroups n ≤ n` for every natural number `n`. -/
theorem numGroups_le_self (n : ℕ) : numGroups n ≤ n :=
  (numGroups_le_clog n).trans (clog_two_le_self n)

/-- Combined floor characterization `s_n² ν_n⁴ ≤ λ_n < (s_n + 1)² ν_n⁴` for `1 ≤ ν_n`. -/
theorem numGroups_floor_bounds {n : ℕ} (hnu : 1 ≤ Nat.clog 2 (Nat.clog 2 n)) :
    numGroups n ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 ≤ Nat.clog 2 n ∧
      Nat.clog 2 n < (numGroups n + 1) ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 :=
  ⟨sq_mul_pow_four_le_clog n, clog_lt_succ_sq_mul_pow_four hnu⟩

/-- Exact integer-comparison characterization of `numGroups n` (`s_n` in Proposition 6.4): when
`1 ≤ ν_n`, `numGroups n` is the largest natural number `m` satisfying `m² ν_n⁴ ≤ λ_n`. -/
theorem le_numGroups_iff {n : ℕ} (hnu : 1 ≤ Nat.clog 2 (Nat.clog 2 n)) (m : ℕ) :
    m ≤ numGroups n ↔ m ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 ≤ Nat.clog 2 n := by
  refine ⟨fun hm => (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm 2)).trans
    (sq_mul_pow_four_le_clog n), fun hm => ?_⟩
  by_contra hlt
  have hge : numGroups n + 1 ≤ m := by omega
  exact (clog_lt_succ_sq_mul_pow_four hnu).not_ge
    ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hge 2)).trans hm)

/-- Decidable equality characterization of `numGroups n` via pure integer comparisons for
`1 ≤ ν_n`. -/
theorem numGroups_eq_iff {n s : ℕ} (hnu : 1 ≤ Nat.clog 2 (Nat.clog 2 n)) :
    numGroups n = s ↔
      s ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 ≤ Nat.clog 2 n ∧
        Nat.clog 2 n < (s + 1) ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 := by
  constructor
  · rintro rfl
    exact numGroups_floor_bounds hnu
  · rintro ⟨hle, hlt⟩
    have h1 : s ≤ numGroups n := (le_numGroups_iff hnu s).mpr hle
    have h2 : ¬ s + 1 ≤ numGroups n := by
      rw [le_numGroups_iff hnu (s + 1)]
      omega
    omega

private theorem sqrt_clog_lt_succ_mul_iter_clog_sq {n : ℕ} (hnu : 1 ≤ Nat.clog 2 (Nat.clog 2 n)) :
    Real.sqrt (Nat.clog 2 n : ℝ) <
      ((numGroups n : ℝ) + 1) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 := by
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  have hc : (Nat.clog 2 n : ℝ) <
      (((numGroups n + 1) ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 : ℕ) : ℝ) :=
    Nat.cast_lt.mpr (clog_lt_succ_sq_mul_pow_four hnu)
  linarith [show (((numGroups n : ℝ) + 1) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2) ^ 2 =
    (((numGroups n + 1) ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 : ℕ) : ℝ) by push_cast; ring]

/-! ### Permanent positivity threshold and divergence of `numGroups` -/

private theorem four_mul_succ_pow_four_le_two_pow {m : ℕ} (hm : 20 ≤ m) :
    4 * (m + 1) ^ 4 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hstep : (m + 2) ^ 4 ≤ 2 * (m + 1) ^ 4 := by
      have hm3 : (m + 1) ^ 3 * 15 ≤ (m + 1) ^ 3 * (m + 1) := Nat.mul_le_mul_left _ (by omega)
      nlinarith [sq_nonneg m]
    calc
      4 * (m + 2) ^ 4 ≤ 4 * (2 * (m + 1) ^ 4) := Nat.mul_le_mul_left 4 hstep
      _ = 2 * (4 * (m + 1) ^ 4) := by ring
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by ring

private theorem le_clog_of_two_pow_le {m n : ℕ} (hn : 2 ^ m ≤ n) : m ≤ Nat.clog 2 n :=
  (Nat.clog_pow 2 m one_lt_two).symm.le.trans (Nat.clog_mono_right 2 hn)

/-- Exact permanent threshold in `λ_n = ⌈log₂ n⌉`: whenever `640000 ≤ Nat.clog 2 n`,
`2 ≤ numGroups n`. (Note `λ_n = 639999` still gives `ν_n = 20` and `s_n = 799 / 400 = 1`, so
`640000` is sharp.) -/
theorem two_le_numGroups_of_clog_ge {n : ℕ} (h : 640000 ≤ Nat.clog 2 n) :
    2 ≤ numGroups n := by
  have hk20 : 20 ≤ Nat.clog 2 (Nat.clog 2 n) :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 19 < Nat.clog 2 n)
  rw [le_numGroups_iff (by omega) 2]
  obtain hk_eq | hk21 := eq_or_lt_of_le hk20
  · rw [← hk_eq]; omega
  · set m := Nat.clog 2 (Nat.clog 2 n) - 1
    have hm_eq : Nat.clog 2 (Nat.clog 2 n) = m + 1 := by omega
    have hpow_lt : 2 ^ m < Nat.clog 2 n :=
      (Nat.lt_clog_iff_pow_lt one_lt_two).mp (by omega)
    rw [hm_eq]
    exact (four_mul_succ_pow_four_le_two_pow (by omega)).trans hpow_lt.le

/-- Explicit dyadic threshold: for `2 ^ 640000 ≤ n`, `2 ≤ numGroups n`. -/
theorem two_le_numGroups_of_pow_le {n : ℕ} (hn : 2 ^ 640000 ≤ n) :
    2 ≤ numGroups n :=
  two_le_numGroups_of_clog_ge (le_clog_of_two_pow_le hn)

/-- For all sufficiently large `n`, `2 ≤ numGroups n`. -/
theorem eventually_two_le_numGroups : ∀ᶠ n : ℕ in atTop, 2 ≤ numGroups n := by
  filter_upwards [eventually_ge_atTop (2 ^ 640000)] with n hn
  exact two_le_numGroups_of_pow_le hn

/-- When `2 ≤ numGroups n`, `5 ≤ n`. -/
theorem five_le_of_two_le_numGroups {n : ℕ} (hs : 2 ≤ numGroups n) : 5 ≤ n := by
  by_contra hlt
  have hlam : Nat.clog 2 n < 2 ^ 2 := by
    have : Nat.clog 2 n ≤ Nat.clog 2 4 := Nat.clog_mono_right 2 (by omega)
    have h4 : Nat.clog 2 4 = 2 := by decide
    omega
  have hsqrt : (Nat.clog 2 n).sqrt < 2 := Nat.sqrt_lt.mpr hlam
  have hs_le := numGroups_le_sqrt n
  omega

private theorem clog_two_le_three_mul_log (n : ℕ) :
    (Nat.clog 2 n : ℝ) ≤ 3 * Real.log ((n : ℝ) + 16) := by
  match n with
  | 0 =>
    have h0 : (Nat.clog 2 0 : ℝ) = 0 := by rw [show Nat.clog 2 0 = 0 by decide, Nat.cast_zero]
    linarith [log_add_sixteen_pos 0]
  | 1 =>
    have h1 : (Nat.clog 2 1 : ℝ) = 0 := by rw [show Nat.clog 2 1 = 0 by decide, Nat.cast_zero]
    linarith [log_add_sixteen_pos 1]
  | 2 =>
    rw [show Nat.clog 2 2 = 1 by decide, Nat.cast_one]
    linarith [one_lt_log_add_sixteen 2]
  | n' + 3 =>
    set n := n' + 3
    set lam := Nat.clog 2 n
    have hlam2 : 2 ≤ lam := (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 1 < n)
    set k := lam - 1
    have hk_eq : lam = k + 1 := by omega
    have hk1 : 1 ≤ k := by omega
    have hpow : 2 ^ k < n := (Nat.lt_clog_iff_pow_lt one_lt_two).mp (by change k < lam; omega)
    have hpow_real : (2 : ℝ) ^ k < (n : ℝ) + 16 := by
      have hcast : ((2 ^ k : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hpow
      push_cast at hcast; linarith
    have hlog_pow : (k : ℝ) * Real.log 2 < Real.log ((n : ℝ) + 16) := by
      simpa only [Real.log_pow] using Real.log_lt_log (by positivity) hpow_real
    have hk_le : (lam : ℝ) ≤ 2 * (k : ℝ) := by
      rw [hk_eq]; push_cast
      linarith [show (1 : ℝ) ≤ k from Nat.one_le_cast.mpr hk1]
    nlinarith [Real.log_two_gt_d9]

private theorem tendsto_clog_two_atTop : Tendsto (Nat.clog 2) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨2 ^ b, fun _ hn =>
    (Nat.clog_pow 2 b one_lt_two).symm.le.trans (Nat.clog_mono_right 2 hn)⟩

/-- The discrete sparsification parameter `numGroups n` (`s_n`) tends to infinity, justifying the
finiteness of the exhaustive-search fallback `s_n < 2` in Proposition 6.4. -/
theorem tendsto_numGroups_atTop : Tendsto numGroups atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  have hsmall : Tendsto (fun m : ℕ =>
      Real.log ((m : ℝ) + 16) ^ 2 / Real.sqrt (m : ℝ)) atTop (𝓝 0) := by
    have h1 : (fun x : ℝ => Real.log (x + 16) ^ (2 : ℝ)) =o[atTop]
        (fun x : ℝ => (x + 16) ^ (1 / 2 : ℝ)) :=
      (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) 2 (by norm_num)).comp_tendsto
        (tendsto_atTop_add_const_right atTop (16 : ℝ) tendsto_id)
    have h2 : (fun x : ℝ => (x + 16) ^ (1 / 2 : ℝ)) =O[atTop]
        (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
      refine IsBigO.of_bound 2 ?_
      filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
      calc
        Real.sqrt (x + 16) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
        _ = 2 * Real.sqrt x := by rw [Real.sqrt_mul (by norm_num), h4]
    simpa only [Function.comp_def, Real.rpow_two, Real.sqrt_eq_rpow] using
      (h1.trans_isBigO h2).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp <| (hsmall.comp tendsto_clog_two_atTop).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (9 * ((B : ℝ) + 1)) by positivity))
  refine ⟨max N₁ 3, fun n hn => ?_⟩
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  have hn3 : 3 ≤ n := (le_max_right N₁ 3).trans hn
  have hnu1 : 1 ≤ nu := one_le_iter_clog_two_iff.mpr hn3
  have hsqrt_pos : 0 < Real.sqrt (lam : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (one_le_clog_two_iff.mpr (by omega)))
  have hnu_sq : (nu : ℝ) ^ 2 ≤ 9 * Real.log ((lam : ℝ) + 16) ^ 2 := by
    have hnu_le : (nu : ℝ) ≤ 3 * Real.log ((lam : ℝ) + 16) := clog_two_le_three_mul_log lam
    simpa only [mul_pow, show (3 : ℝ) ^ 2 = 9 by norm_num] using
      pow_le_pow_left₀ (Nat.cast_nonneg _) hnu_le 2
  have hcross : Real.log ((lam : ℝ) + 16) ^ 2 * (9 * ((B : ℝ) + 1)) < 1 * Real.sqrt (lam : ℝ) :=
    (div_lt_div_iff₀ hsqrt_pos (by positivity)).mp (hN₁ n ((le_max_left N₁ 3).trans hn))
  have hmul : (nu : ℝ) ^ 2 * ((B : ℝ) + 1) < Real.sqrt (lam : ℝ) := by
    have : (0 : ℝ) < (B : ℝ) + 1 := by positivity
    nlinarith
  have hsucc_real := sqrt_clog_lt_succ_mul_iter_clog_sq hnu1
  have hB_lt : (B : ℝ) < ((numGroups n + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) < (nu : ℝ) ^ 2 := by positivity
    push_cast; nlinarith
  have hB_nat : B < numGroups n + 1 := (Nat.cast_lt (α := ℝ)).mp hB_lt
  omega

/-- For any bound `B`, there are only finitely many `n` with `numGroups n < B`. -/
theorem finite_numGroups_lt (B : ℕ) : {n : ℕ | numGroups n < B}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_numGroups_atTop.eventually_ge_atTop B)
  exact (Set.finite_lt_nat N).subset fun n hn => by
    by_contra hge
    exact (not_lt_of_ge (hN n (le_of_not_gt hge))) hn

/-! ### Core Section 6.4 tree-exponent bound (`n / numGroups n = O(interpolationScale n)`) -/

/-- When `1 ≤ numGroups n`, the integer floor gives `n / s_n ≤ 2 n ν_n² / √λ_n`. -/
theorem div_numGroups_le_two_mul {n : ℕ} (hs : 1 ≤ numGroups n) :
    (n : ℝ) / (numGroups n : ℝ) ≤
      2 * ((n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n : ℝ)) := by
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  have hnu1 : 1 ≤ nu := by
    by_contra h0
    have hnu0 : nu = 0 := by omega
    simp only [numGroups, lam, nu, hnu0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Nat.div_zero] at hs
    omega
  have hlam1 : 1 ≤ lam :=
    one_le_clog_two_iff.mpr (by have := one_le_iter_clog_two_iff.mp hnu1; omega)
  have hsqrt_le : Real.sqrt (lam : ℝ) ≤ 2 * (numGroups n : ℝ) * (nu : ℝ) ^ 2 := by
    have hs1 : (numGroups n : ℝ) + 1 ≤ 2 * (numGroups n : ℝ) := by
      linarith [show (1 : ℝ) ≤ numGroups n from Nat.one_le_cast.mpr hs]
    exact (sqrt_clog_lt_succ_mul_iter_clog_sq hnu1).le.trans
      (mul_le_mul_of_nonneg_right hs1 (by positivity))
  have hs_pos : (0 : ℝ) < numGroups n := Nat.cast_pos.mpr hs
  have hsqrt_pos : 0 < Real.sqrt (lam : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hlam1)
  rw [mul_div_assoc', div_le_div_iff₀ hs_pos hsqrt_pos]
  linarith [mul_le_mul_of_nonneg_left hsqrt_le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

private theorem log_add_sixteen_le_clog_two {n : ℕ} (hn : 16 ≤ n) :
    Real.log ((n : ℝ) + 16) ≤ (Nat.clog 2 n : ℝ) := by
  set lam := Nat.clog 2 n
  have hlam4 : (4 : ℝ) ≤ lam := Nat.cast_le.mpr <|
    (Nat.clog_pow 2 4 one_lt_two).symm.le.trans (Nat.clog_mono_right 2 (by omega))
  have hpow : (n : ℝ) + 16 ≤ (2 : ℝ) ^ (lam + 1) := by
    have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ lam := by exact_mod_cast Nat.le_pow_clog one_lt_two n
    rw [pow_succ]; linarith [show (16 : ℝ) ≤ n from Nat.cast_le.mpr hn]
  have hlog : Real.log ((n : ℝ) + 16) ≤ ((lam : ℝ) + 1) * Real.log 2 := by
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using Real.log_le_log (by positivity) hpow
  nlinarith [Real.log_two_lt_d9]

/-- Explicit constant tree-exponent inequality: whenever `640000 ≤ Nat.clog 2 n`,
`n / numGroups n ≤ 16 * interpolationScale n`. -/
theorem div_numGroups_le_interpolationScale_of_clog_ge {n : ℕ} (h : 640000 ≤ Nat.clog 2 n) :
    (n : ℝ) / (numGroups n : ℝ) ≤ 16 * interpolationScale n := by
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  have hs2 : 2 ≤ numGroups n := two_le_numGroups_of_clog_ge h
  have hn16 : 16 ≤ n := by have := clog_two_le_self n; omega
  have hdiv := div_numGroups_le_two_mul (by omega : 1 ≤ numGroups n)
  have hsqrt_ge : Real.sqrt (Real.log ((n : ℝ) + 16)) ≤ Real.sqrt (lam : ℝ) :=
    Real.sqrt_le_sqrt (log_add_sixteen_le_clog_two hn16)
  set X := Real.log ((n : ℝ) + 16)
  set L := Real.log X
  have hL4 : 4 < L := by
    have hpow100 : 2 ^ 100 < n :=
      (Nat.lt_clog_iff_pow_lt one_lt_two).mp (by change 100 < lam; omega)
    have hpow_real : (2 : ℝ) ^ (100 : ℕ) < (n : ℝ) + 16 := by
      have hcast : ((2 ^ 100 : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hpow100
      push_cast at hcast; linarith
    have hlog_pow : ((100 : ℕ) : ℝ) * Real.log 2 < X := by
      simpa only [Real.log_pow] using Real.log_lt_log (by positivity) hpow_real
    have hexp4 : Real.exp 4 < 56 := by
      have he4 : Real.exp 4 = Real.exp 1 ^ 4 := by
        simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 4
      have hpow4 : Real.exp 1 ^ 4 < (68 / 25 : ℝ) ^ 4 :=
        pow_lt_pow_left₀ (by linarith [Real.exp_one_lt_d9]) (Real.exp_pos 1).le (by decide)
      norm_num at hpow4; linarith
    norm_num at hlog_pow
    change 4 < Real.log X
    rw [← Real.log_exp 4]
    exact Real.log_lt_log (Real.exp_pos 4) (by linarith [Real.log_two_gt_d9])
  have hlog3 : Real.log 3 < 2 := by
    rw [← Real.log_exp 2]
    refine Real.log_lt_log (by norm_num) ?_
    have hsq : (2 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
      pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by decide)
    have he_eq : Real.exp 2 = Real.exp 1 ^ 2 := by
      simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 2
    linarith
  have hnu2 : 2 ≤ nu := two_le_iter_clog_two_iff.mpr (by omega)
  set m := nu - 1
  have hm_eq : nu = m + 1 := by omega
  have hX_pos : 0 < X := log_add_sixteen_pos n
  have hpow_m : (2 : ℝ) ^ m < 3 * X := by
    have hlt : 2 ^ m < lam := (Nat.lt_clog_iff_pow_lt one_lt_two).mp (by change m < nu; omega)
    have hcast : ((2 ^ m : ℕ) : ℝ) < (lam : ℝ) := Nat.cast_lt.mpr hlt
    push_cast at hcast
    exact hcast.trans_le (clog_two_le_three_mul_log n)
  have hlog_m : (m : ℝ) * Real.log 2 < Real.log 3 + L := by
    have h1 := Real.log_lt_log (by positivity) hpow_m
    rwa [Real.log_pow, Real.log_mul (by norm_num) hX_pos.ne'] at h1
  have hnu_le : (nu : ℝ) ≤ (5 / 2 : ℝ) * L := by
    have hm_le : (m : ℝ) ≤ (9 / 4 : ℝ) * L := by
      nlinarith [Real.log_two_gt_d9, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [hm_eq]; push_cast; linarith
  have hnu_sq : (nu : ℝ) ^ 2 ≤ 8 * L ^ 2 := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hnu_le 2
    nlinarith
  have hsqrtX_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX_pos
  have hsqrtL_pos : 0 < Real.sqrt (lam : ℝ) := lt_of_lt_of_le hsqrtX_pos hsqrt_ge
  have hfrac : (n : ℝ) * (nu : ℝ) ^ 2 / Real.sqrt (lam : ℝ) ≤ 8 * interpolationScale n := by
    unfold interpolationScale
    change (n : ℝ) * (nu : ℝ) ^ 2 / Real.sqrt (lam : ℝ) ≤ 8 * ((n : ℝ) * L ^ 2 / Real.sqrt X)
    rw [mul_div_assoc', div_le_div_iff₀ hsqrtL_pos hsqrtX_pos]
    have h1 : (n : ℝ) * (nu : ℝ) ^ 2 * Real.sqrt X ≤ (n : ℝ) * (8 * L ^ 2) * Real.sqrt X :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnu_sq (Nat.cast_nonneg n)) hsqrtX_pos.le
    have h2 : (n : ℝ) * (8 * L ^ 2) * Real.sqrt X ≤
        8 * ((n : ℝ) * L ^ 2) * Real.sqrt (lam : ℝ) := by
      rw [show (n : ℝ) * (8 * L ^ 2) = 8 * ((n : ℝ) * L ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hsqrt_ge (by positivity)
    exact h1.trans h2
  linarith

/-- Concrete eventual tree-exponent bound (`C = 16`): eventually
`n / numGroups n ≤ 16 * interpolationScale n`. -/
theorem eventually_div_numGroups_le :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / (numGroups n : ℝ) ≤ 16 * interpolationScale n := by
  filter_upwards [eventually_ge_atTop (2 ^ 640000)] with n hn
  exact div_numGroups_le_interpolationScale_of_clog_ge (le_clog_of_two_pow_le hn)

/-- Core Section 6.4 tree-exponent asymptotic bound:
`n / numGroups n = O(interpolationScale n)`. -/
theorem isBigO_div_numGroups_interpolationScale :
    (fun n : ℕ => (n : ℝ) / (numGroups n : ℝ)) =O[atTop] interpolationScale := by
  refine IsBigO.of_bound 16 ?_
  filter_upwards [eventually_div_numGroups_le] with n hn
  rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (interpolationScale_nonneg n)]

/-! ### Core Section 6.3 equation `(6.4)` polylogarithmic and quasi-polynomial absorption -/

/-- Any fixed power of `log (n + 16)` is `o(interpolationScale n)` (Section 6.3, p. 43). -/
theorem isLittleO_log_pow_interpolationScale (d : ℕ) :
    (fun n : ℕ => Real.log ((n : ℝ) + 16) ^ d) =o[atTop] interpolationScale := by
  set u : ℕ → ℝ := fun n => (n : ℝ) + 16
  have hu_tendsto : Tendsto u atTop atTop :=
    tendsto_atTop_add_const_right atTop (16 : ℝ) tendsto_natCast_atTop_atTop
  have h1 : (fun n : ℕ => Real.log (u n) ^ ((d : ℝ) + 1 / 2)) =o[atTop] u := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) ((d : ℝ) + 1 / 2) one_pos).comp_tendsto
        hu_tendsto
  have h2 : u =O[atTop] (fun n : ℕ => (n : ℝ)) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 16] with n hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg n)]
    linarith [show (16 : ℝ) ≤ n from Nat.cast_le.mpr hn, show u n = (n : ℝ) + 16 from rfl]
  have h3 : (fun n : ℕ => (n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (Real.log (u n)) ^ 2) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have hsq : 1 ≤ Real.log (Real.log (u n)) ^ 2 := by nlinarith [one_lt_log_log_add_sixteen n]
    rw [one_mul, Real.norm_of_nonneg (Nat.cast_nonneg n), Real.norm_of_nonneg (by positivity)]
    exact le_mul_of_one_le_right (Nat.cast_nonneg n) hsq
  have h4 := (h1.trans_isBigO (h2.trans h3)).mul_isBigO
    (isBigO_refl (fun n : ℕ => (Real.sqrt (Real.log (u n)))⁻¹) atTop)
  refine h4.congr' (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
  · dsimp only
    have hpos : 0 < Real.log (u n) := log_add_sixteen_pos n
    rw [Real.rpow_add hpos, Real.rpow_natCast, ← Real.sqrt_eq_rpow, mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne', mul_one]
  · simp only [interpolationScale, u, div_eq_mul_inv]

/-- Any fixed power of `λ_n = ⌈log₂ n⌉` is `o(interpolationScale n)`. -/
theorem isLittleO_clog_pow_interpolationScale (d : ℕ) :
    (fun n : ℕ => (Nat.clog 2 n : ℝ) ^ d) =o[atTop] interpolationScale := by
  refine (IsBigO.of_bound ((3 : ℝ) ^ d) (Eventually.of_forall fun n => ?_)).trans_isLittleO
    (isLittleO_log_pow_interpolationScale d)
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (pow_nonneg (log_add_sixteen_pos n).le d), ← mul_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (clog_two_le_three_mul_log n) d

/-- Every constant multiple of `log (n + 16) ^ d` is eventually bounded by
`ε * interpolationScale n` for any `ε > 0`. -/
theorem eventually_mul_log_pow_le_interpolationScale (C : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * Real.log ((n : ℝ) + 16) ^ d ≤ ε * interpolationScale n := by
  rcases le_or_gt C 0 with hC | hC
  · exact Eventually.of_forall fun n => by
      nlinarith [pow_nonneg (log_add_sixteen_pos n).le d,
        mul_nonneg hε.le (interpolationScale_nonneg n)]
  · filter_upwards [(isLittleO_log_pow_interpolationScale d).bound (div_pos hε hC)] with n hn
    rw [Real.norm_of_nonneg (pow_nonneg (log_add_sixteen_pos n).le d),
      Real.norm_of_nonneg (interpolationScale_nonneg n)] at hn
    calc
      C * Real.log ((n : ℝ) + 16) ^ d ≤ C * (ε / C * interpolationScale n) :=
        mul_le_mul_of_nonneg_left hn hC.le
      _ = ε * interpolationScale n := by field_simp

/-- Every constant multiple of `⌈log₂ n⌉ ^ d` is eventually bounded by `ε * interpolationScale n`
for any `ε > 0`. -/
theorem eventually_mul_clog_pow_le_interpolationScale (C : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * (Nat.clog 2 n : ℝ) ^ d ≤ ε * interpolationScale n := by
  rcases le_or_gt C 0 with hC | hC
  · exact Eventually.of_forall fun n => by
      nlinarith [pow_nonneg (Nat.cast_nonneg (Nat.clog 2 n) : (0 : ℝ) ≤ Nat.clog 2 n) d,
        mul_nonneg hε.le (interpolationScale_nonneg n)]
  · filter_upwards [(isLittleO_clog_pow_interpolationScale d).bound (div_pos hε hC)] with n hn
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (interpolationScale_nonneg n)] at hn
    calc
      C * (Nat.clog 2 n : ℝ) ^ d ≤ C * (ε / C * interpolationScale n) :=
        mul_le_mul_of_nonneg_left hn hC.le
      _ = ε * interpolationScale n := by field_simp

/-- Quasi-polynomial base-`2` overhead `(2 : ℝ) ^ (C * ⌈log₂ n⌉ ^ d)` is eventually bounded by
`(2 : ℝ) ^ (ε * interpolationScale n)` for every `ε > 0`. -/
theorem eventually_two_pow_clog_pow_le (C : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (C * (Nat.clog 2 n : ℝ) ^ d) ≤
      (2 : ℝ) ^ (ε * interpolationScale n) := by
  filter_upwards [eventually_mul_clog_pow_le_interpolationScale C d hε] with n hn
  exact Real.rpow_le_rpow_of_exponent_le one_le_two hn

private theorem eventually_two_pow_succ_clog_pow_le (C : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (C * ((Nat.clog 2 n : ℝ) + 1) ^ d) ≤
      (2 : ℝ) ^ (ε * interpolationScale n) := by
  rcases le_or_gt C 0 with hC | hC
  · refine Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have h1 : (0 : ℝ) ≤ ((Nat.clog 2 n : ℝ) + 1) ^ d := by positivity
    nlinarith [mul_nonneg hε.le (interpolationScale_nonneg n)]
  · filter_upwards [eventually_ge_atTop 2,
      eventually_two_pow_clog_pow_le (C * (2 : ℝ) ^ d) d hε] with n hn2 hpow
    have hlam1 : (1 : ℝ) ≤ Nat.clog 2 n := Nat.one_le_cast.mpr (one_le_clog_two_iff.mpr hn2)
    have hp : ((Nat.clog 2 n : ℝ) + 1) ^ d ≤ (2 : ℝ) ^ d * (Nat.clog 2 n : ℝ) ^ d := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) d
    have hexp :
        C * ((Nat.clog 2 n : ℝ) + 1) ^ d ≤ C * (2 : ℝ) ^ d * (Nat.clog 2 n : ℝ) ^ d := by
      linarith [mul_le_mul_of_nonneg_left hp hC.le]
    exact (Real.rpow_le_rpow_of_exponent_le one_le_two hexp).trans hpow

/-- Concrete leaf-factor bound (`A_tree = 17`): for any polynomial degree `d`, eventually
`(n + numGroups n + 1) ^ d * 2 ^ (n / numGroups n) ≤ 2 ^ (17 * ρ(n))`. -/
theorem eventually_poly_mul_two_pow_div_numGroups_le (d : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d * (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) ≤
        (2 : ℝ) ^ (17 * interpolationScale n) := by
  filter_upwards [eventually_div_numGroups_le,
    eventually_mul_log_pow_le_interpolationScale (2 * d) 1 (Real.log_pos one_lt_two)]
    with n hdiv hlog
  have hbase_le : (n : ℝ) + (numGroups n : ℝ) + 1 ≤ ((n : ℝ) + 16) ^ 2 := by
    have hs_le : (numGroups n : ℝ) ≤ n := Nat.cast_le.mpr (numGroups_le_self n)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hpoly_le : ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d ≤ (2 : ℝ) ^ interpolationScale n := by
    have hpow : ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d ≤ ((n : ℝ) + 16) ^ (2 * d) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hbase_le d
    have hexp : ((n : ℝ) + 16) ^ (2 * d) =
        Real.exp ((2 * (d : ℝ)) * Real.log ((n : ℝ) + 16) ^ 1) := by
      rw [pow_one, ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
      push_cast; ring_nf
    have hexp_le : Real.exp ((2 * (d : ℝ)) * Real.log ((n : ℝ) + 16) ^ 1) ≤
        (2 : ℝ) ^ interpolationScale n := by
      rw [Real.rpow_def_of_pos two_pos, Real.exp_le_exp]; linarith
    exact hpow.trans (hexp.le.trans hexp_le)
  calc
    ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d * (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ))
        ≤ (2 : ℝ) ^ interpolationScale n * (2 : ℝ) ^ (16 * interpolationScale n) :=
      mul_le_mul hpoly_le (Real.rpow_le_rpow_of_exponent_le one_le_two hdiv)
        (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (17 * interpolationScale n) := by rw [← Real.rpow_add two_pos]; ring_nf

/-- For any polynomial degree `d`, there exists `A_tree > 0` such that eventually the full
sparsification leaf factor `(n + numGroups n + 1) ^ d * 2 ^ (n / numGroups n)` is bounded by
`2 ^ (A_tree * interpolationScale n)`. -/
theorem exists_eventually_poly_mul_two_pow_div_numGroups_le (d : ℕ) :
    ∃ A_tree : ℝ, 0 < A_tree ∧ ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d * (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) ≤
        (2 : ℝ) ^ (A_tree * interpolationScale n) :=
  ⟨17, by norm_num, eventually_poly_mul_two_pow_div_numGroups_le d⟩

private def queryExpCoeff (C_B β C_P e_B e_μ : ℕ) : ℕ :=
  3 + (C_B + β + 4) * C_P * (C_B + 1) ^ e_B * (C_B + β + 4) ^ e_μ

private theorem query_count_le_two_pow_succ_clog_pow {n m B P C_B β C_P e_B e_μ : ℕ}
    (hm : m ≤ B * n) (hB : B ≤ C_B * Nat.clog 2 n ^ β)
    (hP : P ≤ C_P * B ^ e_B * Nat.clog 2 (2 * m + 4) ^ e_μ) :
    3 * n * (2 * m + 2) ^ P + 1 ≤
      2 ^ (queryExpCoeff C_B β C_P e_B e_μ * (Nat.clog 2 n + 1) ^ (β * e_B + e_μ + 1)) := by
  set lam1 := Nat.clog 2 n + 1
  have hlam1 : 1 ≤ lam1 := Nat.succ_pos _
  have hn_pow : n ≤ 2 ^ lam1 :=
    (Nat.le_pow_clog one_lt_two n).trans (Nat.pow_le_pow_right two_pos (Nat.le_succ _))
  have hm_pow : 2 * m + 4 ≤ 2 ^ ((C_B + β + 4) * lam1) := by
    have hlam_pow : Nat.clog 2 n ^ β ≤ 2 ^ (lam1 * β) := by
      calc
        Nat.clog 2 n ^ β ≤ lam1 ^ β := Nat.pow_le_pow_left (Nat.le_succ _) β
        _ ≤ (2 ^ lam1) ^ β := Nat.pow_le_pow_left lam1.lt_two_pow_self.le β
        _ = 2 ^ (lam1 * β) := (pow_mul 2 lam1 β).symm
    have hprod : 2 * m ≤ 2 ^ (C_B + lam1 * β + lam1 + 1) := by
      calc
        2 * m ≤ 2 * (C_B * Nat.clog 2 n ^ β * n) :=
          Nat.mul_le_mul_left 2 (hm.trans (Nat.mul_le_mul_right n hB))
        _ ≤ 2 ^ 1 * (2 ^ C_B * 2 ^ (lam1 * β) * 2 ^ lam1) := by
          simp only [pow_one]
          exact Nat.mul_le_mul_left 2
            (Nat.mul_le_mul (Nat.mul_le_mul C_B.lt_two_pow_self.le hlam_pow) hn_pow)
        _ = 2 ^ (C_B + lam1 * β + lam1 + 1) := by ring
    have h4 : 4 ≤ 2 ^ (C_B + lam1 * β + lam1 + 2) :=
      (show 4 = 2 ^ 2 by norm_num).trans_le (Nat.pow_le_pow_right two_pos (by omega))
    have hsum : 2 * m + 4 ≤ 2 ^ (C_B + lam1 * β + lam1 + 3) := by
      have hp1 := hprod.trans (Nat.pow_le_pow_right two_pos (by omega :
        C_B + lam1 * β + lam1 + 1 ≤ C_B + lam1 * β + lam1 + 2))
      exact (Nat.add_le_add hp1 h4).trans_eq (by ring)
    exact hsum.trans (Nat.pow_le_pow_right two_pos (by nlinarith))
  have hclog : Nat.clog 2 (2 * m + 4) ≤ (C_B + β + 4) * lam1 :=
    (Nat.clog_le_iff_le_pow one_lt_two).mpr hm_pow
  have hB_le : B ≤ (C_B + 1) * lam1 ^ β :=
    hB.trans (Nat.mul_le_mul (Nat.le_succ C_B) (Nat.pow_le_pow_left (Nat.le_succ _) β))
  set K := C_P * (C_B + 1) ^ e_B * (C_B + β + 4) ^ e_μ
  have hP_le : P ≤ K * lam1 ^ (β * e_B + e_μ) := by
    calc
      P ≤ C_P * ((C_B + 1) * lam1 ^ β) ^ e_B * ((C_B + β + 4) * lam1) ^ e_μ :=
        hP.trans (Nat.mul_le_mul (Nat.mul_le_mul_left C_P (Nat.pow_le_pow_left hB_le e_B))
          (Nat.pow_le_pow_left hclog e_μ))
      _ = K * lam1 ^ (β * e_B + e_μ) := by simp only [K, mul_pow, ← pow_mul, pow_add]; ring
  set E := (C_B + β + 4) * K * lam1 ^ (β * e_B + e_μ + 1)
  have hbase_pow : (2 * m + 2) ^ P ≤ 2 ^ E := by
    calc
      (2 * m + 2) ^ P ≤ (2 ^ ((C_B + β + 4) * lam1)) ^ P :=
        Nat.pow_le_pow_left (by omega) P
      _ = 2 ^ ((C_B + β + 4) * lam1 * P) := (pow_mul 2 _ P).symm
      _ ≤ 2 ^ ((C_B + β + 4) * lam1 * (K * lam1 ^ (β * e_B + e_μ))) :=
        Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left _ hP_le)
      _ = 2 ^ E := by dsimp only [E]; rw [pow_succ]; ring_nf
  have hterm : 3 * n * (2 * m + 2) ^ P + 1 ≤ 2 ^ (2 + lam1 + E) := by
    have hpos : 1 ≤ 2 ^ (lam1 + E) := Nat.one_le_pow _ 2 two_pos
    calc
      3 * n * (2 * m + 2) ^ P + 1 ≤ 3 * (2 ^ lam1 * 2 ^ E) + 1 := by
        linarith [Nat.mul_le_mul hn_pow hbase_pow]
      _ = 3 * 2 ^ (lam1 + E) + 1 := by rw [← pow_add]
      _ ≤ 4 * 2 ^ (lam1 + E) := by omega
      _ = 2 ^ (2 + lam1 + E) := by ring
  refine hterm.trans (Nat.pow_le_pow_right two_pos ?_)
  have hlam_pow1 : lam1 ≤ lam1 ^ (β * e_B + e_μ + 1) := Nat.le_self_pow (by omega) lam1
  have h1_pow : 1 ≤ lam1 ^ (β * e_B + e_μ + 1) := hlam1.trans hlam_pow1
  have hK_eq : queryExpCoeff C_B β C_P e_B e_μ = 3 + (C_B + β + 4) * K := by
    simp only [queryExpCoeff, K]; ring
  rw [hK_eq]; dsimp only [E]; linarith

private theorem query_term_le_two_pow_succ_clog {n m B P C_B β C_P e_B e_μ : ℕ}
    (hm : m ≤ B * n) (hB : B ≤ C_B * Nat.clog 2 n ^ β)
    (hP : P ≤ C_P * B ^ e_B * Nat.clog 2 (2 * m + 4) ^ e_μ) :
    3 * (n : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1 ≤
      (2 : ℝ) ^ ((queryExpCoeff C_B β C_P e_B e_μ : ℝ) *
        ((Nat.clog 2 n : ℝ) + 1) ^ (β * e_B + e_μ + 1)) := by
  have hcast : ((3 * n * (2 * m + 2) ^ P + 1 : ℕ) : ℝ) ≤
      ((2 ^ (queryExpCoeff C_B β C_P e_B e_μ *
        (Nat.clog 2 n + 1) ^ (β * e_B + e_μ + 1)) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (query_count_le_two_pow_succ_clog_pow hm hB hP)
  have hlhs : 3 * (n : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1 =
      ((3 * n * (2 * m + 2) ^ P + 1 : ℕ) : ℝ) := by push_cast; ring
  have hrhs : ((2 ^ (queryExpCoeff C_B β C_P e_B e_μ *
      (Nat.clog 2 n + 1) ^ (β * e_B + e_μ + 1)) : ℕ) : ℝ) =
      (2 : ℝ) ^ ((queryExpCoeff C_B β C_P e_B e_μ : ℝ) *
        ((Nat.clog 2 n : ℝ) + 1) ^ (β * e_B + e_μ + 1)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]; push_cast; rfl
  exact (hlhs.trans_le hcast).trans hrhs.le

/-- General polynomial-exponent query overhead absorption: for any `C_B, β, C_P, e_B, e_μ : ℕ` and
every `ε > 0`, eventually in `n`, every `(m, B, P)` satisfying `m ≤ B * n`,
`B ≤ C_B * ⌈log₂ n⌉ ^ β`, and `P ≤ C_P * B ^ e_B * ⌈log₂ (2 m + 4)⌉ ^ e_μ` obeys
`3 * n * (2 * m + 2) ^ P + 1 ≤ 2 ^ (ε * interpolationScale n)`. -/
theorem eventually_query_overhead_poly_le (C_B β C_P e_B e_μ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m B P : ℕ,
      m ≤ B * n → B ≤ C_B * Nat.clog 2 n ^ β →
        P ≤ C_P * B ^ e_B * Nat.clog 2 (2 * m + 4) ^ e_μ →
          (3 * (n : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1) ≤
            (2 : ℝ) ^ (ε * interpolationScale n) := by
  filter_upwards [eventually_two_pow_succ_clog_pow_le (queryExpCoeff C_B β C_P e_B e_μ : ℝ)
    (β * e_B + e_μ + 1) hε] with n hpow m B P hm hB hP
  exact (query_term_le_two_pow_succ_clog hm hB hP).trans hpow

/-- Query-count overhead absorption (`3 * n * (2 * m) ^ P + 1 ≤ 2 ^ (ε * interpolationScale n)`):
when `m ≤ B * n`, `B ≤ C_B * ⌈log₂ n⌉ ^ β`, and `P ≤ C_P * ⌈log₂ (2 m + 2)⌉`, the Lemma 6.2
candidate count is eventually bounded by `2 ^ (ε * interpolationScale n)` for every `ε > 0`. -/
theorem eventually_query_overhead_le (C_B β C_P : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m B P : ℕ,
      m ≤ B * n → B ≤ C_B * Nat.clog 2 n ^ β → P ≤ C_P * Nat.clog 2 (2 * m + 2) →
        (3 * (n : ℝ) * (2 * (m : ℝ)) ^ P + 1) ≤
          (2 : ℝ) ^ (ε * interpolationScale n) := by
  filter_upwards [eventually_query_overhead_poly_le C_B β C_P 0 1 hε] with n hn m B P hm hB hP
  have hP' : P ≤ C_P * B ^ 0 * Nat.clog 2 (2 * m + 4) ^ 1 := by
    simp only [pow_zero, mul_one, pow_one]
    exact hP.trans (Nat.mul_le_mul_left C_P (Nat.clog_mono_right 2 (by omega)))
  have hpow : (2 * (m : ℝ)) ^ P ≤ (2 * (m : ℝ) + 2) ^ P :=
    pow_le_pow_left₀ (by positivity) (by linarith) P
  have hle : 3 * (n : ℝ) * (2 * (m : ℝ)) ^ P + 1 ≤ 3 * (n : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1 := by
    linarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 3 * (n : ℝ))]
  exact hle.trans (hn m B P hm hB hP')

/-! ### Section 6.4 leaf occurrence polylogarithmic bound -/

/-- The per-variable occurrence bound `C_k * (s * (⌈log₂ (2 s)⌉ + 1)) ^ (k - 1)` of Lemma 6.3
specialized to `σ = 1 / s` (printed p. 44). -/
def leafOccurrenceBound (C_k k s : ℕ) : ℕ :=
  C_k * (s * (Nat.clog 2 (2 * s) + 1)) ^ (k - 1)

/-- For every `5 ≤ n`, `numGroups n * (⌈log₂ (2 * numGroups n)⌉ + 1) ≤ ⌈log₂ n⌉`. -/
theorem numGroups_mul_clog_le_clog {n : ℕ} (hn : 5 ≤ n) :
    numGroups n * (Nat.clog 2 (2 * numGroups n) + 1) ≤ Nat.clog 2 n := by
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  have hnu2 : 2 ≤ nu := two_le_iter_clog_two_iff.mpr hn
  have hclog : Nat.clog 2 (2 * numGroups n) ≤ nu + 1 := by
    rw [Nat.clog_le_iff_le_pow one_lt_two, pow_succ']
    exact Nat.mul_le_mul_left 2 ((numGroups_le_clog n).trans (Nat.le_pow_clog one_lt_two lam))
  have hnu_sq : Nat.clog 2 (2 * numGroups n) + 1 ≤ nu ^ 2 := by nlinarith
  calc
    numGroups n * (Nat.clog 2 (2 * numGroups n) + 1)
        ≤ numGroups n * nu ^ 2 := Nat.mul_le_mul_left _ hnu_sq
    _ ≤ lam.sqrt := Nat.div_mul_le_self lam.sqrt (nu ^ 2)
    _ ≤ lam := Nat.sqrt_le_self _

/-- Uniform polynomial occurrence bound: for every `5 ≤ n` (in particular whenever
`2 ≤ numGroups n`), `leafOccurrenceBound C_k k (numGroups n) ≤ C_k * ⌈log₂ n⌉ ^ (k - 1)`. -/
theorem leafOccurrenceBound_le_mul_pow {C_k k n : ℕ} (hn : 5 ≤ n) :
    leafOccurrenceBound C_k k (numGroups n) ≤ C_k * Nat.clog 2 n ^ (k - 1) :=
  Nat.mul_le_mul_left C_k
    (Nat.pow_le_pow_left (numGroups_mul_clog_le_clog hn) (k - 1))

/-- Explicit threshold form of the leaf occurrence bound (`β = k`): for `1 ≤ k`, `5 ≤ n`, and
`C_k ≤ ⌈log₂ n⌉`, `leafOccurrenceBound C_k k (numGroups n) ≤ ⌈log₂ n⌉ ^ k`. -/
theorem leafOccurrenceBound_le_of_le {C_k k n : ℕ} (hk : 1 ≤ k) (hn : 5 ≤ n)
    (hC : C_k ≤ Nat.clog 2 n) :
    leafOccurrenceBound C_k k (numGroups n) ≤ Nat.clog 2 n ^ k := by
  calc
    leafOccurrenceBound C_k k (numGroups n)
        ≤ C_k * Nat.clog 2 n ^ (k - 1) := leafOccurrenceBound_le_mul_pow hn
    _ ≤ Nat.clog 2 n * Nat.clog 2 n ^ (k - 1) := Nat.mul_le_mul_right _ hC
    _ = Nat.clog 2 n ^ k := by conv_rhs => rw [show k = 1 + (k - 1) by omega, pow_add, pow_one]

/-- Discharging Lemma 4.8's polylogarithmic occurrence hypothesis `b ≤ ⌈log₂ n⌉ ^ β` with explicit
exponent `β = k`: for `1 ≤ k` (including all `2 ≤ k` in Lemma 6.3 and Proposition 6.4), eventually
`leafOccurrenceBound C_k k (numGroups n) ≤ ⌈log₂ n⌉ ^ k`. -/
theorem eventually_leafOccurrenceBound_le (C_k : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ n : ℕ in atTop, leafOccurrenceBound C_k k (numGroups n) ≤ Nat.clog 2 n ^ k := by
  filter_upwards [eventually_ge_atTop (max 5 (2 ^ C_k))] with n hn
  refine leafOccurrenceBound_le_of_le hk ((le_max_left 5 (2 ^ C_k)).trans hn) ?_
  exact (Nat.clog_pow 2 C_k one_lt_two).symm.le.trans
    (Nat.clog_mono_right 2 ((le_max_right 5 (2 ^ C_k)).trans hn))

/-- Direct Lemma 4.8 feasibility bridge: for `1 ≤ k`, the Proposition 6.4 leaf-occurrence cap
`leafOccurrenceBound C_k k (numGroups n)` eventually discharges the `b ≤ ⌈log₂ n⌉ ^ k` hypothesis
of `ReplacementParams.exists_feasible`, yielding `ReplacementParams.Feasible k n b w M`. -/
theorem eventually_leafOccurrenceBound_feasible (C_k : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ ⦃b w M : ℕ⦄,
      1 ≤ b → b ≤ leafOccurrenceBound C_k k (numGroups n) →
      1 ≤ w → w ≤ Nat.clog 2 n ^ k →
      n ≤ M → M ≤ b * n → ReplacementParams.Feasible k n b w M := by
  obtain ⟨n₀, _, hfeas⟩ := ReplacementParams.exists_feasible hk
  filter_upwards [eventually_ge_atTop n₀, eventually_leafOccurrenceBound_le C_k hk] with
    n hn hleaf b w M hb₁ hb₂ hw₁ hw₂ hnM hMbn
  exact hfeas hn hb₁ (hb₂.trans hleaf) hw₁ hw₂ hnM hMbn

/-! ### Section 6.3 equation `(6.4)` and Proposition 6.4 runtime composition -/

private theorem uniform_bound_of_eventually {time : ℕ → ℕ → ℝ} {G : ℕ → ℝ}
    {d C_large : ℕ} {A : ℝ} (hA : 0 < A)
    (hG : ∀ n m : ℕ, time n m ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d * G n)
    (hev : ∀ᶠ n : ℕ in atTop, G n ≤ (C_large : ℝ) * (2 : ℝ) ^ (A * interpolationScale n)) :
    ∃ C_total : ℕ, ∀ n m : ℕ, time n m ≤
      (C_total : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d * (2 : ℝ) ^ (A * interpolationScale n) := by
  obtain ⟨N_cut, hN_cut⟩ := eventually_atTop.mp hev
  set M_small : ℕ := (Finset.range N_cut).sup fun k => ⌈G k⌉₊
  set C_total : ℕ := max C_large M_small
  refine ⟨C_total, fun n m => ?_⟩
  have hpoly_nonneg : (0 : ℝ) ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d := by positivity
  by_cases hn : n < N_cut
  · have hM_le : G n ≤ (C_total : ℝ) := by
      have hceil : G n ≤ (⌈G n⌉₊ : ℝ) := Nat.le_ceil (G n)
      have hsup : ⌈G n⌉₊ ≤ M_small :=
        Finset.le_sup (f := fun k => ⌈G k⌉₊) (Finset.mem_range.mpr hn)
      exact hceil.trans (Nat.cast_le.mpr (hsup.trans (le_max_right C_large M_small)))
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (A * interpolationScale n) :=
      Real.one_le_rpow one_le_two (mul_nonneg hA.le (interpolationScale_nonneg n))
    calc
      time n m ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d * (C_total : ℝ) :=
        (hG n m).trans (mul_le_mul_of_nonneg_left hM_le hpoly_nonneg)
      _ = (C_total : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d := mul_comm _ _
      _ ≤ (C_total : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d * (2 : ℝ) ^ (A * interpolationScale n) :=
        le_mul_of_one_le_right (by positivity) hpow1
  · have hC_ge : (C_large : ℝ) ≤ (C_total : ℝ) := Nat.cast_le.mpr (le_max_left C_large M_small)
    calc
      time n m ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d *
          ((C_large : ℝ) * (2 : ℝ) ^ (A * interpolationScale n)) :=
        (hG n m).trans (mul_le_mul_of_nonneg_left (hN_cut n (le_of_not_gt hn)) hpoly_nonneg)
      _ = (C_large : ℝ) * (((n : ℝ) + (m : ℝ) + 1) ^ d *
            (2 : ℝ) ^ (A * interpolationScale n)) := by ring
      _ ≤ (C_total : ℝ) * (((n : ℝ) + (m : ℝ) + 1) ^ d *
            (2 : ℝ) ^ (A * interpolationScale n)) :=
        mul_le_mul_of_nonneg_right hC_ge (by positivity)
      _ = (C_total : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d *
            (2 : ℝ) ^ (A * interpolationScale n) := by ring

private theorem leaf_poly_le_input_poly {n m m_leaf B_n C_B β : ℕ} (d_leaf : ℕ)
    (hm : m_leaf ≤ B_n * n) (hB : B_n ≤ C_B * Nat.clog 2 n ^ β) :
    ((n : ℝ) + (m_leaf : ℝ) + 1) ^ d_leaf ≤
      (((C_B + 1) ^ d_leaf : ℕ) : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ ((β + 1) * d_leaf) := by
  have hm_le : m_leaf ≤ C_B * (n + m + 1) ^ (β + 1) := by
    calc
      m_leaf ≤ C_B * Nat.clog 2 n ^ β * n := hm.trans (Nat.mul_le_mul_right n hB)
      _ ≤ C_B * n ^ β * n := Nat.mul_le_mul_right n
          (Nat.mul_le_mul_left C_B (Nat.pow_le_pow_left (clog_two_le_self n) β))
      _ = C_B * n ^ (β + 1) := by rw [pow_succ]; ring
      _ ≤ C_B * (n + m + 1) ^ (β + 1) :=
        Nat.mul_le_mul_left C_B (Nat.pow_le_pow_left (by omega) (β + 1))
  have hn1_le : n + 1 ≤ (n + m + 1) ^ (β + 1) :=
    (by omega : n + 1 ≤ n + m + 1).trans (Nat.le_self_pow (by omega) _)
  have hsum_real : (n : ℝ) + (m_leaf : ℝ) + 1 ≤
      ((C_B + 1 : ℕ) : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ (β + 1) := by
    have hcast : ((n + m_leaf + 1 : ℕ) : ℝ) ≤
        (((C_B + 1) * (n + m + 1) ^ (β + 1) : ℕ) : ℝ) := Nat.cast_le.mpr (by linarith)
    push_cast at hcast ⊢; exact hcast
  calc
    ((n : ℝ) + (m_leaf : ℝ) + 1) ^ d_leaf
        ≤ (((C_B + 1 : ℕ) : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ (β + 1)) ^ d_leaf :=
      pow_le_pow_left₀ (by positivity) hsum_real d_leaf
    _ = (((C_B + 1) ^ d_leaf : ℕ) : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ ((β + 1) * d_leaf) := by
      rw [mul_pow, ← pow_mul]; push_cast; rfl

private theorem rpow_two_mul_le_add_one {x A : ℝ} (n : ℕ)
    (hx : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (1 * interpolationScale n)) :
    (2 : ℝ) ^ x * (2 : ℝ) ^ (A * interpolationScale n) ≤
      (2 : ℝ) ^ ((A + 1) * interpolationScale n) := by
  calc
    (2 : ℝ) ^ x * (2 : ℝ) ^ (A * interpolationScale n)
        ≤ (2 : ℝ) ^ (1 * interpolationScale n) * (2 : ℝ) ^ (A * interpolationScale n) :=
      mul_le_mul_of_nonneg_right hx (by positivity)
    _ = (2 : ℝ) ^ ((A + 1) * interpolationScale n) := by rw [← Real.rpow_add two_pos]; ring_nf

private theorem rpow_two_le_add_one {x A : ℝ} (n : ℕ) (hA : 0 ≤ A)
    (hx : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (1 * interpolationScale n)) :
    (2 : ℝ) ^ x ≤ (2 : ℝ) ^ ((A + 1) * interpolationScale n) :=
  (le_mul_of_one_le_right (by positivity)
    (Real.one_le_rpow one_le_two (mul_nonneg hA (interpolationScale_nonneg n)))).trans
    (rpow_two_mul_le_add_one n hx)

/-- **Section 6.3 equation `(6.4)` (counting one sparse formula)**: on the promised sparse domain
`m ≤ C_B * ⌈log₂ n⌉ ^ β * n`, combining the finite `n < N₀` fallback with Lemma 6.1 initial-test
construction `2 ^ (C_init * ⌈log₂ n⌉ ^ d_init)` and at most `3 n (2 m + 2) ^ P + 1` candidate
calls each taking `(n + m + 1) ^ d_call * 2 ^ (A_sys * interpolationScale n)` bit operations yields
a uniform bound `C_sparse * (n + m + 1) ^ d_sparse * 2 ^ (A_sparse * interpolationScale n)` across
all `n, m : ℕ` with `m ≤ C_B * ⌈log₂ n⌉ ^ β * n`. -/
theorem sparse_formula_time_bound
    (N₀ C_exhaust d_exhaust C_init d_init d_call C_B β C_P e_B e_μ : ℕ) (A_sys : ℝ)
    (time : ℕ → ℕ → ℝ)
    (htime : ∀ n m : ℕ, m ≤ C_B * Nat.clog 2 n ^ β * n →
      (n < N₀ ∧
        time n m ≤ (C_exhaust : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_exhaust * (2 : ℝ) ^ n) ∨
      (N₀ ≤ n ∧ ∃ B P : ℕ, m ≤ B * n ∧ B ≤ C_B * Nat.clog 2 n ^ β ∧
        P ≤ C_P * B ^ e_B * Nat.clog 2 (2 * m + 4) ^ e_μ ∧
        time n m ≤ (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) +
          ((n : ℝ) + (m : ℝ) + 1) ^ d_call *
            (3 * (n : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1) *
            (2 : ℝ) ^ (A_sys * interpolationScale n))) :
    ∃ (C_sparse d_sparse : ℕ) (A_sparse : ℝ), 0 < A_sparse ∧
      ∀ n m : ℕ, m ≤ C_B * Nat.clog 2 n ^ β * n →
        time n m ≤
          (C_sparse : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_sparse *
            (2 : ℝ) ^ (A_sparse * interpolationScale n) := by
  set d_sparse : ℕ := max d_exhaust d_call
  set A' : ℝ := max A_sys 0
  set A_sparse : ℝ := A' + 1
  have hA_pos : 0 < A_sparse := by positivity
  set C_q : ℕ := queryExpCoeff C_B β C_P e_B e_μ
  set d_q : ℕ := β * e_B + e_μ + 1
  set F_main : ℕ → ℝ := fun n =>
    (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) +
      (2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
        (2 : ℝ) ^ (A' * interpolationScale n)
  set G : ℕ → ℝ := fun n => if n < N₀ then max ((C_exhaust : ℝ) * (2 : ℝ) ^ n) (F_main n)
    else F_main n
  set time_sparse : ℕ → ℕ → ℝ := fun n m =>
    if m ≤ C_B * Nat.clog 2 n ^ β * n then time n m else 0
  obtain ⟨C_sparse, hC⟩ := uniform_bound_of_eventually (time := time_sparse) (G := G)
    (d := d_sparse) (C_large := 2) hA_pos
    (fun n m => by
      by_cases hm_dom : m ≤ C_B * Nat.clog 2 n ^ β * n
      swap
      · have hF_nonneg : 0 ≤ F_main n := by dsimp only [F_main]; positivity
        have hG_nonneg : 0 ≤ G n := by
          dsimp only [G]; split_ifs <;> [exact le_max_of_le_right hF_nonneg; exact hF_nonneg]
        simp only [time_sparse, hm_dom, ↓reduceIte]
        exact mul_nonneg (by positivity) hG_nonneg
      simp only [time_sparse, hm_dom, ↓reduceIte]
      have hbase1 : (1 : ℝ) ≤ (n : ℝ) + (m : ℝ) + 1 := by
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have hd_ex := pow_le_pow_right₀ hbase1 (le_max_left d_exhaust d_call)
      have hd_call := pow_le_pow_right₀ hbase1 (le_max_right d_exhaust d_call)
      have hd_pos : (1 : ℝ) ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_sparse := one_le_pow₀ hbase1
      have hA_le : (2 : ℝ) ^ (A_sys * interpolationScale n) ≤
          (2 : ℝ) ^ (A' * interpolationScale n) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two
          (mul_le_mul_of_nonneg_right (le_max_left A_sys 0) (interpolationScale_nonneg n))
      rcases htime n m hm_dom with ⟨hlt, hfb⟩ | ⟨_, B, P, hm, hB, hP, hsp⟩
      · have hG_ge : (C_exhaust : ℝ) * (2 : ℝ) ^ n ≤ G n := by
          simp only [G, hlt, ↓reduceIte]; exact le_max_left _ _
        calc
          time n m ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_exhaust * ((C_exhaust : ℝ) * (2 : ℝ) ^ n) := by
            linarith
          _ ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_sparse * G n :=
            mul_le_mul hd_ex hG_ge (by positivity) (by positivity)
      · have hG_ge : F_main n ≤ G n := by
          dsimp only [G]; split_ifs <;> [exact le_max_right _ _; exact le_rfl]
        have hq := query_term_le_two_pow_succ_clog hm hB hP
        have hinit_le := le_mul_of_one_le_left
          (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init))
          hd_pos
        have hm1 := mul_le_mul hq hA_le (by positivity) (by positivity)
        have hprod_le : ((n : ℝ) + (m : ℝ) + 1) ^ d_call *
              (3 * (n : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1) *
              (2 : ℝ) ^ (A_sys * interpolationScale n) ≤
            ((n : ℝ) + (m : ℝ) + 1) ^ d_sparse *
              ((2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
                (2 : ℝ) ^ (A' * interpolationScale n)) := by
          rw [mul_assoc]
          exact mul_le_mul hd_call hm1 (by positivity) (by positivity)
        have hF : time n m ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_sparse * F_main n := by
          dsimp only [F_main] at *; linarith
        exact hF.trans (mul_le_mul_of_nonneg_left hG_ge (by positivity)))
    (by
      filter_upwards [eventually_ge_atTop N₀,
        eventually_two_pow_clog_pow_le (C_init : ℝ) d_init one_pos,
        eventually_two_pow_succ_clog_pow_le (C_q : ℝ) d_q one_pos] with n hn0 hinit_ev hq_ev
      have hnot : ¬ n < N₀ := not_lt_of_ge hn0
      simp only [G, hnot, ↓reduceIte, F_main, Nat.cast_ofNat]
      linarith [rpow_two_le_add_one n (le_max_right A_sys 0) hinit_ev,
        rpow_two_mul_le_add_one (A := A') n hq_ev])
  refine ⟨C_sparse, d_sparse, A_sparse, hA_pos, fun n m hm_dom => ?_⟩
  simpa only [time_sparse, hm_dom, ↓reduceIte] using hC n m

/-- **General Proposition 6.4 runtime-composition theorem** (including polynomial-exponent `P_leaf`
as in Lemma 6.1's `P = 20000 B² μ²` and optional per-leaf initial-matrix construction cost):
for all `n, m : ℕ`, total bit operations across the exhaustive-search fallback and the
sparsification-tree traversal are bounded by
`C_total * (n + m + 1) ^ d_total * 2 ^ (A_total * interpolationScale n)`. -/
theorem prop64_time_bound_general
    (N₀ C_exhaust d_exhaust C_tree d_tree C_node d_node C_init_coeff C_init d_init d_leaf
      C_B β C_P e_B e_μ : ℕ)
    (A_sys : ℝ) (time : ℕ → ℕ → ℝ)
    (htime : ∀ n m : ℕ,
      ((n < N₀ ∨ numGroups n < 2) ∧
        time n m ≤ (C_exhaust : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_exhaust * (2 : ℝ) ^ n) ∨
      (2 ≤ numGroups n ∧ ∃ B_n m_leaf P_leaf : ℕ,
        m_leaf ≤ B_n * n ∧ B_n ≤ C_B * Nat.clog 2 n ^ β ∧
        P_leaf ≤ C_P * B_n ^ e_B * Nat.clog 2 (2 * m_leaf + 4) ^ e_μ ∧
        time n m ≤
          (C_tree : ℝ) * ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d_tree *
            (2 : ℝ) ^ (n / numGroups n + 1 : ℕ) *
            ((C_node : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_node +
              (C_init_coeff : ℝ) * (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) +
              ((n : ℝ) + (m_leaf : ℝ) + 1) ^ d_leaf *
                (3 * (n : ℝ) * (2 * (m_leaf : ℝ) + 2) ^ P_leaf + 1) *
                (2 : ℝ) ^ (A_sys * interpolationScale n)))) :
    ∃ (C_total d_total : ℕ) (A_total : ℝ), 0 < A_total ∧
      ∀ n m : ℕ, time n m ≤
        (C_total : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_total *
          (2 : ℝ) ^ (A_total * interpolationScale n) := by
  set d_total : ℕ := max d_exhaust (max d_node ((β + 1) * d_leaf))
  set A' : ℝ := max A_sys 0
  set A_total : ℝ := A' + 18
  have hA_pos : 0 < A_total := by positivity
  set C_q : ℕ := queryExpCoeff C_B β C_P e_B e_μ
  set d_q : ℕ := β * e_B + e_μ + 1
  set K_coeff : ℕ := C_node + C_init_coeff + (C_B + 1) ^ d_leaf
  set C_large : ℕ := 2 * C_tree * K_coeff
  set F_tree : ℕ → ℝ := fun n =>
    2 * (C_tree : ℝ) * ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d_tree *
      (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) *
      ((C_node : ℝ) +
        (C_init_coeff : ℝ) * (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) +
        (((C_B + 1) ^ d_leaf : ℕ) : ℝ) *
          (2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
          (2 : ℝ) ^ (A' * interpolationScale n))
  set G : ℕ → ℝ := fun n =>
    if n < N₀ ∨ numGroups n < 2 then max ((C_exhaust : ℝ) * (2 : ℝ) ^ n) (F_tree n)
    else F_tree n
  obtain ⟨C_total, hC⟩ := uniform_bound_of_eventually (time := time) (G := G)
    (d := d_total) (C_large := C_large) hA_pos
    (fun n m => by
      have hbase1 : (1 : ℝ) ≤ (n : ℝ) + (m : ℝ) + 1 := by
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have hd_ex : ((n : ℝ) + (m : ℝ) + 1) ^ d_exhaust ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_total :=
        pow_le_pow_right₀ hbase1 (le_max_left _ _)
      have hd_node : ((n : ℝ) + (m : ℝ) + 1) ^ d_node ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_total :=
        pow_le_pow_right₀ hbase1 ((le_max_left _ _).trans (le_max_right _ _))
      have hd_leaf_deg :
          ((n : ℝ) + (m : ℝ) + 1) ^ ((β + 1) * d_leaf) ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_total :=
        pow_le_pow_right₀ hbase1 ((le_max_right _ _).trans (le_max_right _ _))
      have hd_pos : (1 : ℝ) ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_total := one_le_pow₀ hbase1
      have hA_le : (2 : ℝ) ^ (A_sys * interpolationScale n) ≤
          (2 : ℝ) ^ (A' * interpolationScale n) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two
          (mul_le_mul_of_nonneg_right (le_max_left A_sys 0) (interpolationScale_nonneg n))
      rcases htime n m with ⟨hfb_cond, hfb⟩ | ⟨_, B_n, m_leaf, P_leaf, hm, hB, hP, htr⟩
      · have hG_ge : (C_exhaust : ℝ) * (2 : ℝ) ^ n ≤ G n := by
          simp only [G, hfb_cond, ↓reduceIte]; exact le_max_left _ _
        calc
          time n m ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_exhaust * ((C_exhaust : ℝ) * (2 : ℝ) ^ n) := by
            linarith
          _ ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_total * G n :=
            mul_le_mul hd_ex hG_ge (by positivity) (by positivity)
      · have hG_ge : F_tree n ≤ G n := by
          dsimp only [G]; split_ifs <;> [exact le_max_right _ _; exact le_rfl]
        have hdiv_pow : (2 : ℝ) ^ (n / numGroups n + 1 : ℕ) ≤
            2 * (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) := by
          rw [pow_succ', ← Real.rpow_natCast]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le one_le_two Nat.cast_div_le) zero_le_two
        have hleaf_poly : ((n : ℝ) + (m_leaf : ℝ) + 1) ^ d_leaf ≤
            (((C_B + 1) ^ d_leaf : ℕ) : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_total :=
          (leaf_poly_le_input_poly d_leaf hm hB).trans
            (mul_le_mul_of_nonneg_left hd_leaf_deg (by positivity))
        have hq := query_term_le_two_pow_succ_clog hm hB hP
        have ht1 : (C_node : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_node ≤
            ((n : ℝ) + (m : ℝ) + 1) ^ d_total * (C_node : ℝ) := by
          linarith [mul_le_mul_of_nonneg_left hd_node (Nat.cast_nonneg C_node)]
        have ht2 := le_mul_of_one_le_left (by positivity :
          (0 : ℝ) ≤ (C_init_coeff : ℝ) * (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init))
          hd_pos
        have ht3 : ((n : ℝ) + (m_leaf : ℝ) + 1) ^ d_leaf *
              (3 * (n : ℝ) * (2 * (m_leaf : ℝ) + 2) ^ P_leaf + 1) *
              (2 : ℝ) ^ (A_sys * interpolationScale n) ≤
            ((n : ℝ) + (m : ℝ) + 1) ^ d_total *
              ((((C_B + 1) ^ d_leaf : ℕ) : ℝ) *
                (2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
                (2 : ℝ) ^ (A' * interpolationScale n)) := by
          have hm1 := mul_le_mul hq hA_le (by positivity) (by positivity)
          calc
            ((n : ℝ) + (m_leaf : ℝ) + 1) ^ d_leaf *
                (3 * (n : ℝ) * (2 * (m_leaf : ℝ) + 2) ^ P_leaf + 1) *
                (2 : ℝ) ^ (A_sys * interpolationScale n)
                ≤ ((((C_B + 1) ^ d_leaf : ℕ) : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_total) *
                  ((2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
                    (2 : ℝ) ^ (A' * interpolationScale n)) := by
              rw [mul_assoc]; exact mul_le_mul hleaf_poly hm1 (by positivity) (by positivity)
            _ = ((n : ℝ) + (m : ℝ) + 1) ^ d_total *
                  ((((C_B + 1) ^ d_leaf : ℕ) : ℝ) *
                    (2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
                    (2 : ℝ) ^ (A' * interpolationScale n)) := by ring
        have houter : (C_tree : ℝ) * ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d_tree *
              (2 : ℝ) ^ (n / numGroups n + 1 : ℕ) ≤
            2 * (C_tree : ℝ) * ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d_tree *
              (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ)) := by
          linarith [mul_le_mul_of_nonneg_left hdiv_pow (by positivity : (0 : ℝ) ≤
            (C_tree : ℝ) * ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d_tree)]
        have hinner :
            (C_node : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_node +
                (C_init_coeff : ℝ) * (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) +
                ((n : ℝ) + (m_leaf : ℝ) + 1) ^ d_leaf *
                  (3 * (n : ℝ) * (2 * (m_leaf : ℝ) + 2) ^ P_leaf + 1) *
                  (2 : ℝ) ^ (A_sys * interpolationScale n) ≤
              ((n : ℝ) + (m : ℝ) + 1) ^ d_total *
                ((C_node : ℝ) +
                  (C_init_coeff : ℝ) * (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) +
                  (((C_B + 1) ^ d_leaf : ℕ) : ℝ) *
                    (2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
                    (2 : ℝ) ^ (A' * interpolationScale n)) := by linarith
        have hF : time n m ≤ ((n : ℝ) + (m : ℝ) + 1) ^ d_total * F_tree n := by
          refine htr.trans ((mul_le_mul houter hinner (by positivity)
            (by positivity)).trans_eq ?_)
          dsimp only [F_tree]; ring
        exact hF.trans (mul_le_mul_of_nonneg_left hG_ge (by positivity)))
    (by
      filter_upwards [eventually_ge_atTop N₀, eventually_two_le_numGroups,
        eventually_poly_mul_two_pow_div_numGroups_le d_tree,
        eventually_two_pow_clog_pow_le (C_init : ℝ) d_init one_pos,
        eventually_two_pow_succ_clog_pow_le (C_q : ℝ) d_q one_pos]
        with n hn0 hs2 htree_ev hinit_ev hq_ev
      have hnot : ¬ (n < N₀ ∨ numGroups n < 2) := by omega
      simp only [G, hnot, ↓reduceIte]
      have hrho := interpolationScale_nonneg n
      have h1_1A' : (1 : ℝ) ≤ (2 : ℝ) ^ ((A' + 1) * interpolationScale n) :=
        Real.one_le_rpow one_le_two (mul_nonneg (by positivity) hrho)
      have hb1 : (C_node : ℝ) ≤ (C_node : ℝ) * (2 : ℝ) ^ ((A' + 1) * interpolationScale n) :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) h1_1A'
      have hb2 : (C_init_coeff : ℝ) * (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) ≤
          (C_init_coeff : ℝ) * (2 : ℝ) ^ ((A' + 1) * interpolationScale n) :=
        mul_le_mul_of_nonneg_left (rpow_two_le_add_one n (le_max_right A_sys 0) hinit_ev)
          (Nat.cast_nonneg _)
      have hb3 : (((C_B + 1) ^ d_leaf : ℕ) : ℝ) *
            (2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
            (2 : ℝ) ^ (A' * interpolationScale n) ≤
          (((C_B + 1) ^ d_leaf : ℕ) : ℝ) * (2 : ℝ) ^ ((A' + 1) * interpolationScale n) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (rpow_two_mul_le_add_one (A := A') n hq_ev) (by positivity)
      have hinner_ev :
          (C_node : ℝ) +
              (C_init_coeff : ℝ) * (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) +
              (((C_B + 1) ^ d_leaf : ℕ) : ℝ) *
                (2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
                (2 : ℝ) ^ (A' * interpolationScale n) ≤
            (K_coeff : ℝ) * (2 : ℝ) ^ ((A' + 1) * interpolationScale n) := by
        have hK : (K_coeff : ℝ) =
            (C_node : ℝ) + (C_init_coeff : ℝ) + (((C_B + 1) ^ d_leaf : ℕ) : ℝ) := by
          dsimp only [K_coeff]; push_cast; rfl
        rw [hK]; linarith
      have hC_cast : (C_large : ℝ) = 2 * (C_tree : ℝ) * (K_coeff : ℝ) := by
        dsimp only [C_large]; push_cast; ring
      calc
        F_tree n = (2 * (C_tree : ℝ)) *
            (((n : ℝ) + (numGroups n : ℝ) + 1) ^ d_tree *
              (2 : ℝ) ^ ((n : ℝ) / (numGroups n : ℝ))) *
            ((C_node : ℝ) +
              (C_init_coeff : ℝ) * (2 : ℝ) ^ ((C_init : ℝ) * (Nat.clog 2 n : ℝ) ^ d_init) +
              (((C_B + 1) ^ d_leaf : ℕ) : ℝ) *
                (2 : ℝ) ^ ((C_q : ℝ) * ((Nat.clog 2 n : ℝ) + 1) ^ d_q) *
                (2 : ℝ) ^ (A' * interpolationScale n)) := by dsimp only [F_tree]; ring
        _ ≤ (2 * (C_tree : ℝ)) * (2 : ℝ) ^ (17 * interpolationScale n) *
              ((K_coeff : ℝ) * (2 : ℝ) ^ ((A' + 1) * interpolationScale n)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left htree_ev (by positivity)) hinner_ev
            (by positivity) (by positivity)
        _ = (C_large : ℝ) * (2 : ℝ) ^ (A_total * interpolationScale n) := by
          rw [hC_cast]
          calc
            (2 * (C_tree : ℝ)) * (2 : ℝ) ^ (17 * interpolationScale n) *
                ((K_coeff : ℝ) * (2 : ℝ) ^ ((A' + 1) * interpolationScale n))
                = (2 * (C_tree : ℝ) * (K_coeff : ℝ)) *
                  ((2 : ℝ) ^ (17 * interpolationScale n) *
                    (2 : ℝ) ^ ((A' + 1) * interpolationScale n)) := by ring
            _ = (2 * (C_tree : ℝ) * (K_coeff : ℝ)) *
                  (2 : ℝ) ^ (A_total * interpolationScale n) := by
              rw [← Real.rpow_add two_pos]; dsimp only [A_total]; ring_nf)
  exact ⟨C_total, d_total, A_total, hA_pos, hC⟩

/-- **Proposition 6.4 runtime-composition theorem** (printed pp. 43–44): combining
1. tree node/leaf count `≤ C_tree * (n + s_n + 1) ^ d_tree * 2 ^ (n / s_n + 1)`
   for `s_n = numGroups n`,
2. per-leaf sparse-formula count time
   `≤ (n + m_leaf + 1) ^ d_leaf * (3 * n * (2 * m_leaf + 2) ^ P_leaf + 1) * 2 ^ (A_sys * ρ(n))`
   with `m_leaf ≤ B_n * n`, `B_n ≤ C_B * ⌈log₂ n⌉ ^ β`, and `P_leaf ≤ C_P * ⌈log₂ (2 m_leaf + 4)⌉`,
3. per-node processing overhead `(n + m + 1) ^ d_node`, and
4. finite small-`n` / `numGroups n < 2` exhaustive-search fallback
   `C_exhaust * (n + m + 1) ^ d_exhaust * 2 ^ n`,
there exist `C_total, d_total : ℕ` and `A_total > 0` bounding total bit operations uniformly by
`C_total * (n + m + 1) ^ d_total * 2 ^ (A_total * interpolationScale n)` for all `n, m : ℕ`. -/
theorem prop64_time_bound
    (N₀ C_exhaust d_exhaust C_tree d_tree d_node d_leaf C_B β C_P : ℕ) (A_sys : ℝ)
    (time : ℕ → ℕ → ℝ)
    (htime : ∀ n m : ℕ,
      ((n < N₀ ∨ numGroups n < 2) ∧
        time n m ≤ (C_exhaust : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_exhaust * (2 : ℝ) ^ n) ∨
      (2 ≤ numGroups n ∧ ∃ B_n m_leaf P_leaf : ℕ,
        m_leaf ≤ B_n * n ∧ B_n ≤ C_B * Nat.clog 2 n ^ β ∧
        P_leaf ≤ C_P * Nat.clog 2 (2 * m_leaf + 4) ∧
        time n m ≤
          (C_tree : ℝ) * ((n : ℝ) + (numGroups n : ℝ) + 1) ^ d_tree *
            (2 : ℝ) ^ (n / numGroups n + 1 : ℕ) *
            (((n : ℝ) + (m : ℝ) + 1) ^ d_node +
              ((n : ℝ) + (m_leaf : ℝ) + 1) ^ d_leaf *
                (3 * (n : ℝ) * (2 * (m_leaf : ℝ) + 2) ^ P_leaf + 1) *
                (2 : ℝ) ^ (A_sys * interpolationScale n)))) :
    ∃ (C_total d_total : ℕ) (A_total : ℝ), 0 < A_total ∧
      ∀ n m : ℕ, time n m ≤
        (C_total : ℝ) * ((n : ℝ) + (m : ℝ) + 1) ^ d_total *
          (2 : ℝ) ^ (A_total * interpolationScale n) := by
  refine prop64_time_bound_general N₀ C_exhaust d_exhaust C_tree d_tree 1 d_node 0 0 0 d_leaf
    C_B β C_P 0 1 A_sys time fun n m => ?_
  rcases htime n m with hfb | ⟨hs2, B_n, m_leaf, P_leaf, hm, hB, hP, htr⟩
  · exact Or.inl hfb
  · refine Or.inr ⟨hs2, B_n, m_leaf, P_leaf, hm, hB, ?_, ?_⟩
    · simpa only [pow_zero, mul_one, pow_one] using hP
    · simpa only [Nat.cast_one, one_mul, CharP.cast_eq_zero, zero_mul, add_zero] using htr

end SparseCountingScale

end Cslib.Complexity.SubexponentialSAT
