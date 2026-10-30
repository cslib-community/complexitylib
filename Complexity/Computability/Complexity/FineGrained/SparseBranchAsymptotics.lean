/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseParitySchedule
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Section 5.5 and Section 6.3 post-branching `interpolationScale` domain-examination bounds

This module establishes the Section 5.5 (Proof of Theorem 2.2, printed p. 39) and Section 6.3
(Counting one sparse formula, printed p. 43) real-analytic scale transfer connecting the
post-branching free-variable domain-examination bounds of
`Complexity.Computability.Complexity.FineGrained.SparseBranchSchedule` and
`Complexity.Computability.Complexity.FineGrained.SparseParitySchedule` to the sublinear exponent
`Cslib.Complexity.SubexponentialSAT.interpolationScale` of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]:

1. **Free-variable (`n / 2 ≤ n' ≤ n`) to original-variable (`n`) `rowCost` transfer (§5.5, p. 39)**:
   On every heavy-variable branch where `n ≤ 2 * n'` and `n' ≤ n` (`n / 2 ≤ n' ≤ n`),
   `Feasible.mul_rowCost_le_of_le_two_mul` proves that `hF : Feasible β n' b_occ w_width M'` implies
   `(n' : ℝ) * rowCost β n' ≤ 2056 * ((β : ℝ) + 3) * (n * (⌈log₂ ⌈log₂ n⌉⌉) ^ 2 / √⌈log₂ n⌉)`.
2. **Explicit comparison with `interpolationScale n` for `16384 ≤ n` (§5.5 & §6.4, pp. 39, 44)**:
   - `mul_iter_clog_sq_div_sqrt_clog_le_interpolationScale`: for `16384 ≤ n`,
     `(n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n) ≤`
     `16 * interpolationScale n`.
   - `div_sqrt_clog_le_interpolationScale` and `two_pow_div_sqrt_clog_le_interpolationScale`:
     for `16384 ≤ n`, `(n / (Nat.clog 2 n).sqrt : ℝ) ≤ 32 * interpolationScale n` and hence the
     heavy-variable branch count `(2 : ℝ) ^ (n / (Nat.clog 2 n).sqrt)` is at most
     `(2 : ℝ) ^ (32 * interpolationScale n)`.
   - `Feasible.mul_rowCost_le_interpolationScale`: for `16384 ≤ n`, `n ≤ 2 * n'`, and `n' ≤ n`,
     `(n' : ℝ) * rowCost β n' ≤ 32896 * ((β : ℝ) + 3) * interpolationScale n`.
   - `two_mul_numNodes_mul_numGroups_le_interpolationScale`: for `16384 ≤ n` and `n' ≤ n`, the
     evaluation-box prefactor `2 * (numNodes n' : ℝ) * (numGroups n' : ℝ)` is at most
     `interpolationScale n ≤ Real.exp (interpolationScale n) ≤`
     `(2 : ℝ) ^ (2 * interpolationScale n)`.
3. **Single-branch and multi-branch `2 ^ (A * interpolationScale n)` domain-examination bounds
   (§5.5 p. 39 & §6.3 p. 43)**:
   - `Feasible.branch_domainExaminationBound_le_two_pow_interpolationScale` and
     `sum_branch_domainExaminationBound_le_two_pow_interpolationScale`: bound the per-branch and
     branch-summed domain-examination counts of `SparseBranchSchedule` by
     `(2 : ℝ) ^ (branchExamScaleCoeff β k c * interpolationScale (Fintype.card ι))` and
     `(2 : ℝ) ^ ((branchExamScaleCoeff β k c + 32) * interpolationScale (Fintype.card ι))` for all
     `16384 ≤ Fintype.card ι`.
   - `CNF.branch_domainExaminationBound_parityRowSystem_le_two_pow_interpolationScale`,
     `CNF.sum_branch_domainExaminationBound_parityRowSystem_le_two_pow_interpolationScale`,
     `CNF.exists_branch_schedule_and_examBound_parityRowSystem_of_le_clog_pow`, and
     `CNF.exists_greedy_parityRowSystem_branch_schedule_and_examBound_of_le_clog_pow`: specialize
     these bounds to `CNF.parityRowSystem` at Lemma 6.2 equation-count ratio `c = 6` (distinct from
     Theorem 2.2's larger sparsity parameter `c = c(k)`), establishing that for any width-`≤ k` CNF
     `φ` with `B ≤ C_B * (Nat.clog 2 n) ^ β_B` and `N₁ ≤ Fintype.card V`, every branch of
     `φ.parityRowSystem` (and every greedy stage `i ≤ 3 * Fintype.card V`) admits a concrete
     `ReplacementDesign` and the sum of the domain-examination bounds across all heavy-variable
     branches is at most
     `(2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B + 32) *`
     `interpolationScale (Fintype.card V))`.

## Main definitions

* `Cslib.BitString.branchExamScaleCoeff`
* `Cslib.Logic.PL.CNF.parityBranchExamScaleCoeff`

## Main results

* `Feasible.mul_rowCost_le_of_le_two_mul`
* `mul_iter_clog_sq_div_sqrt_clog_le_interpolationScale`
* `div_sqrt_clog_le_interpolationScale`
* `Feasible.mul_rowCost_le_interpolationScale`
* `two_mul_numNodes_mul_numGroups_le_interpolationScale`
* `Cslib.BitString.Feasible.branch_domainExaminationBound_le_two_pow_interpolationScale`
* `Cslib.BitString.sum_branchAssignments_le_two_pow_interpolationScale`
* `Cslib.BitString.sum_branch_domainExaminationBound_le_two_pow_interpolationScale`
* `CNF.branch_domainExaminationBound_parityRowSystem_le_two_pow_interpolationScale`
* `CNF.sum_branch_domainExaminationBound_parityRowSystem_le_two_pow_interpolationScale`
* `CNF.exists_branch_schedule_and_examBound_parityRowSystem_of_le_clog_pow`
* `CNF.exists_greedy_parityRowSystem_branch_schedule_and_examBound_of_le_clog_pow`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Section 5.5, pp. 38–39; Section 6.3, p. 43; Section 6.4, pp. 43–44)
-/

public section

namespace Cslib.Complexity.SubexponentialSAT.ReplacementParams

open Cslib.Complexity.SubexponentialSAT

/-! ### 1. Free-variable (`n / 2 ≤ n' ≤ n`) to original-variable (`n`) `rowCost` transfer -/

/-- **Section 5.5 free-variable `rowCost` transfer (printed p. 39):**
Whenever `n ≤ 2 * n'`, `n' ≤ n`, and `hF : Feasible β n' b_occ w_width M'`, the free-variable
exponent factor `(n' : ℝ) * rowCost β n'` is bounded in terms of the original variable count `n` by
`2056 * ((β : ℝ) + 3) * ((n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n))`.
-/
theorem Feasible.mul_rowCost_le_of_le_two_mul {β n n' b_occ w_width M' : ℕ}
    (hF : Feasible β n' b_occ w_width M') (hn_le : n ≤ 2 * n') (hn'_le : n' ≤ n) :
    (n' : ℝ) * rowCost β n' ≤
      2056 * ((β : ℝ) + 3) *
        ((n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n)) := by
  have hn'20 : 20 ≤ n' := hF.twenty_le
  have hlam'_pos : 1 ≤ Nat.clog 2 n' :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < n')
  have hlam_pos : 1 ≤ Nat.clog 2 n :=
    hlam'_pos.trans (Nat.clog_mono_right 2 hn'_le)
  have hsqrt'_pos : 0 < Real.sqrt (Nat.clog 2 n') :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hlam'_pos)
  have hsqrt_pos : 0 < Real.sqrt (Nat.clog 2 n) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hlam_pos)
  have hsqrt_le : Real.sqrt (Nat.clog 2 n) ≤ 2 * Real.sqrt (Nat.clog 2 n') := by
    have hclog_le : (Nat.clog 2 n : ℝ) ≤ (2 : ℝ) ^ 2 * (Nat.clog 2 n' : ℝ) := by
      have hnat : Nat.clog 2 n ≤ 2 * Nat.clog 2 n' :=
        Nat.clog_two_le_two_mul_of_le_two_mul hn_le (by omega)
      have hcast : (Nat.clog 2 n : ℝ) ≤ 2 * (Nat.clog 2 n' : ℝ) := by exact_mod_cast hnat
      have hnn : (0 : ℝ) ≤ (Nat.clog 2 n' : ℝ) := Nat.cast_nonneg _
      linarith
    calc Real.sqrt (Nat.clog 2 n)
        ≤ Real.sqrt ((2 : ℝ) ^ 2 * (Nat.clog 2 n' : ℝ)) := Real.sqrt_le_sqrt hclog_le
      _ = Real.sqrt ((2 : ℝ) ^ 2) * Real.sqrt (Nat.clog 2 n') :=
          Real.sqrt_mul (sq_nonneg (2 : ℝ)) _
      _ = 2 * Real.sqrt (Nat.clog 2 n') := by rw [Real.sqrt_sq zero_le_two]
  have hnu_le : (Nat.clog 2 (Nat.clog 2 n') : ℝ) ^ 2 ≤ (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 := by
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 2
    exact_mod_cast Nat.clog_mono_right 2 (Nat.clog_mono_right 2 hn'_le)
  have hn'_real : (n' : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn'_le
  have hfrac :
      (n' : ℝ) * (Nat.clog 2 (Nat.clog 2 n') : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n') ≤
        2 * ((n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n)) := by
    rw [mul_div_assoc', div_le_div_iff₀ hsqrt'_pos hsqrt_pos]
    have h1 :
        (n' : ℝ) * (Nat.clog 2 (Nat.clog 2 n') : ℝ) ^ 2 * Real.sqrt (Nat.clog 2 n) ≤
          (n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 * (2 * Real.sqrt (Nat.clog 2 n')) :=
      mul_le_mul (mul_le_mul hn'_real hnu_le (by positivity) (Nat.cast_nonneg n)) hsqrt_le
        hsqrt_pos.le (by positivity)
    linarith
  calc (n' : ℝ) * rowCost β n'
      ≤ (n' : ℝ) * (1028 * ((β : ℝ) + 3) * (Nat.clog 2 (Nat.clog 2 n') : ℝ) ^ 2 /
          Real.sqrt (Nat.clog 2 n')) :=
        mul_le_mul_of_nonneg_left hF.rowCost_bound (Nat.cast_nonneg n')
    _ = 1028 * ((β : ℝ) + 3) *
          ((n' : ℝ) * (Nat.clog 2 (Nat.clog 2 n') : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n')) := by ring
    _ ≤ 1028 * ((β : ℝ) + 3) *
          (2 * ((n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n))) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = 2056 * ((β : ℝ) + 3) *
          ((n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n)) := by ring

/-! ### 2. Explicit comparison with `interpolationScale n` for `16384 ≤ n` -/

private theorem two_mul_cube_le_two_pow_pred {m : ℕ} (hm : 14 ≤ m) :
    2 * m ^ 3 ≤ 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hstep : (m + 1) ^ 3 ≤ 2 * m ^ 3 := by
      have hm2 : m ^ 2 * 5 ≤ m ^ 2 * m := Nat.mul_le_mul_left (m ^ 2) (by omega)
      nlinarith
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    calc 2 * (m + 1) ^ 3 ≤ 2 * (2 * m ^ 3) := Nat.mul_le_mul_left 2 hstep
      _ ≤ 2 * 2 ^ (m - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ m := hpow.symm

private theorem log_add_sixteen_bounds {n : ℕ} (hn : 16384 ≤ n) :
    14 ≤ Nat.clog 2 n ∧
    2 * Nat.clog 2 n ^ 3 ≤ n ∧
    0 < Real.log ((n : ℝ) + 16) ∧
    Real.log ((n : ℝ) + 16) ≤ (Nat.clog 2 n : ℝ) ∧
    2 < Real.log (Real.log ((n : ℝ) + 16)) ∧
    (Nat.clog 2 (Nat.clog 2 n) : ℝ) ≤ 4 * Real.log (Real.log ((n : ℝ) + 16)) := by
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  set X := Real.log ((n : ℝ) + 16)
  set L := Real.log X
  have hlam14 : 14 ≤ lam := by
    have hlt : 2 ^ 13 < n := by omega
    have hclog : 13 < lam := (Nat.lt_clog_iff_pow_lt one_lt_two).mpr hlt
    omega
  have h2pow_lt : 2 ^ (lam - 1) < n :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mp (by change lam - 1 < lam; omega)
  have hcube_le : 2 * lam ^ 3 ≤ n :=
    (two_mul_cube_le_two_pow_pred hlam14).trans h2pow_lt.le
  have hexp8 : Real.exp 8 < (n : ℝ) + 16 := by
    have he8 : Real.exp 8 = Real.exp 1 ^ 8 := by
      simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 8
    have hpow8 : Real.exp 1 ^ 8 < (68 / 25 : ℝ) ^ 8 :=
      pow_lt_pow_left₀ (by linarith [Real.exp_one_lt_d9]) (Real.exp_pos 1).le (by decide)
    have hn_r : (16384 : ℝ) ≤ n := Nat.cast_le.mpr hn
    norm_num at hpow8
    linarith
  have hX8 : 8 < X := by
    rw [← Real.log_exp 8]
    exact Real.log_lt_log (Real.exp_pos 8) hexp8
  have hX_pos : 0 < X := by linarith
  have hL2 : 2 < L := by
    have hexp2 : Real.exp 2 < 8 := by
      have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by
        simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 2
      have hpow2 : Real.exp 1 ^ 2 < (68 / 25 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ (by linarith [Real.exp_one_lt_d9]) (Real.exp_pos 1).le (by decide)
      norm_num at hpow2
      linarith
    change 2 < Real.log X
    rw [← Real.log_exp 2]
    exact Real.log_lt_log (Real.exp_pos 2) (hexp2.trans hX8)
  have hX_le_lam : X ≤ (lam : ℝ) := by
    have hn_pow : (n : ℝ) + 16 ≤ (2 : ℝ) ^ (lam + 1) := by
      have h1 : (n : ℝ) ≤ (2 : ℝ) ^ lam := by exact_mod_cast Nat.le_pow_clog one_lt_two n
      have h2 : (16 : ℝ) ≤ n := by exact_mod_cast (by omega : 16 ≤ n)
      rw [pow_succ']
      linarith
    have hlog : X ≤ ((lam : ℝ) + 1) * Real.log 2 := by
      simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using
        Real.log_le_log (by positivity) hn_pow
    have hlam_r : (14 : ℝ) ≤ lam := Nat.cast_le.mpr hlam14
    nlinarith [Real.log_two_lt_d9]
  have hlam_lt_4X : (lam : ℝ) < 4 * X := by
    have hpow_r : (2 : ℝ) ^ (lam - 1) < (n : ℝ) + 16 := by
      have hc : ((2 ^ (lam - 1) : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h2pow_lt
      push_cast at hc
      linarith
    have hlog_lam : ((lam - 1 : ℕ) : ℝ) * Real.log 2 < X := by
      simpa only [Real.log_pow] using Real.log_lt_log (by positivity) hpow_r
    have hlam_sub : (lam : ℝ) - 1 = ((lam - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hlam_r : (14 : ℝ) ≤ lam := Nat.cast_le.mpr hlam14
    nlinarith [Real.log_two_gt_d9]
  have hnu_le_4L : (nu : ℝ) ≤ 4 * L := by
    have hnu4 : 4 ≤ nu := by
      have : 2 ^ 3 < lam := by omega
      have hlt : 3 < nu := (Nat.lt_clog_iff_pow_lt one_lt_two).mpr this
      omega
    have hpow_nu : (2 : ℝ) ^ (nu - 1) < 4 * X := by
      have hlt : 2 ^ (nu - 1) < lam :=
        (Nat.lt_clog_iff_pow_lt one_lt_two).mp (by change nu - 1 < nu; omega)
      have hc : ((2 ^ (nu - 1) : ℕ) : ℝ) < (lam : ℝ) := Nat.cast_lt.mpr hlt
      push_cast at hc
      exact hc.trans hlam_lt_4X
    have hlog_nu : ((nu - 1 : ℕ) : ℝ) * Real.log 2 < 2 * Real.log 2 + L := by
      have h1 := Real.log_lt_log (by positivity) hpow_nu
      rw [Real.log_pow, Real.log_mul (by norm_num) hX_pos.ne',
        show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow, Nat.cast_ofNat] at h1
      exact h1
    have hnu_sub : (nu : ℝ) - 1 = ((nu - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    nlinarith [Real.log_two_gt_d9]
  exact ⟨hlam14, hcube_le, hX_pos, hX_le_lam, hL2, hnu_le_4L⟩

/-- **Explicit discrete-to-continuous scale bound:**
Whenever `16384 ≤ n`,
`(n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n) ≤`
`16 * interpolationScale n`. -/
theorem mul_iter_clog_sq_div_sqrt_clog_le_interpolationScale {n : ℕ} (hn : 16384 ≤ n) :
    (n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n) ≤
      16 * interpolationScale n := by
  obtain ⟨_, _, hX_pos, hX_le_lam, hL2, hnu_le_4L⟩ := log_add_sixteen_bounds hn
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  set X := Real.log ((n : ℝ) + 16)
  set L := Real.log X
  have hsqrtX_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX_pos
  have hsqrt_le : Real.sqrt X ≤ Real.sqrt (lam : ℝ) := Real.sqrt_le_sqrt hX_le_lam
  have hsqrtL_pos : 0 < Real.sqrt (lam : ℝ) := lt_of_lt_of_le hsqrtX_pos hsqrt_le
  have hnu_sq : (nu : ℝ) ^ 2 ≤ 16 * L ^ 2 := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg nu) hnu_le_4L 2
    linarith
  unfold interpolationScale
  change (n : ℝ) * (nu : ℝ) ^ 2 / Real.sqrt (lam : ℝ) ≤ 16 * ((n : ℝ) * L ^ 2 / Real.sqrt X)
  rw [mul_div_assoc', div_le_div_iff₀ hsqrtL_pos hsqrtX_pos]
  have h1 : (n : ℝ) * (nu : ℝ) ^ 2 * Real.sqrt X ≤ (n : ℝ) * (16 * L ^ 2) * Real.sqrt X :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnu_sq (Nat.cast_nonneg n)) hsqrtX_pos.le
  have h2 : (n : ℝ) * (16 * L ^ 2) * Real.sqrt X ≤
      16 * ((n : ℝ) * L ^ 2) * Real.sqrt (lam : ℝ) := by
    rw [show (n : ℝ) * (16 * L ^ 2) = 16 * ((n : ℝ) * L ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
  exact h1.trans h2

/-- **Section 5.5 heavy-variable branch exponent bound (printed pp. 38–39):**
Whenever `16384 ≤ n`, `(n / (Nat.clog 2 n).sqrt : ℝ) ≤ 32 * interpolationScale n`. -/
theorem div_sqrt_clog_le_interpolationScale {n : ℕ} (hn : 16384 ≤ n) :
    ((n / (Nat.clog 2 n).sqrt : ℕ) : ℝ) ≤ 32 * interpolationScale n := by
  obtain ⟨hlam14, _, _, _, _, _⟩ := log_add_sixteen_bounds hn
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  have hsqrt_pos : 1 ≤ lam.sqrt := Nat.le_sqrt.mpr (by omega)
  have hnu_pos : 1 ≤ nu :=
    (Nat.lt_clog_iff_pow_lt one_lt_two).mpr (by omega : 2 ^ 0 < lam)
  have hnu_sq1 : (1 : ℝ) ≤ (nu : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ nu := Nat.one_le_cast.mpr hnu_pos
    nlinarith
  have hsqrt_real_pos : 0 < Real.sqrt (lam : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hsqrt_le : Real.sqrt (lam : ℝ) ≤ 2 * (lam.sqrt : ℝ) := by
    have hlt : lam ≤ (lam.sqrt + 1) ^ 2 := (Nat.lt_succ_sqrt' lam).le
    have h1 : Real.sqrt (lam : ℝ) ≤ (lam.sqrt : ℝ) + 1 := by
      rw [Real.sqrt_le_iff]
      refine ⟨add_nonneg (Nat.cast_nonneg _) zero_le_one, ?_⟩
      exact_mod_cast hlt
    have h2 : (1 : ℝ) ≤ lam.sqrt := Nat.one_le_cast.mpr hsqrt_pos
    linarith
  have hdiv_le :
      ((n / lam.sqrt : ℕ) : ℝ) ≤
        2 * ((n : ℝ) * (nu : ℝ) ^ 2 / Real.sqrt (lam : ℝ)) := by
    refine Nat.cast_div_le.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ (Nat.cast_pos.mpr hsqrt_pos) hsqrt_real_pos]
    have hmul1 : (n : ℝ) * Real.sqrt (lam : ℝ) ≤ (n : ℝ) * (2 * (lam.sqrt : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt_le (Nat.cast_nonneg n)
    have hmul2 : (n : ℝ) * (2 * (lam.sqrt : ℝ)) ≤
        2 * ((n : ℝ) * (nu : ℝ) ^ 2) * (lam.sqrt : ℝ) := by
      have : (n : ℝ) ≤ (n : ℝ) * (nu : ℝ) ^ 2 :=
        le_mul_of_one_le_right (Nat.cast_nonneg n) hnu_sq1
      have hsqrt_nn : (0 : ℝ) ≤ (lam.sqrt : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact hmul1.trans hmul2
  linarith [mul_iter_clog_sq_div_sqrt_clog_le_interpolationScale hn]

/-- **Section 5.5 heavy-variable branch count bound:**
Whenever `16384 ≤ n`, `(2 : ℝ) ^ (n / (Nat.clog 2 n).sqrt) ≤ (2 : ℝ) ^ (32 * interpolationScale n)`.
-/
theorem two_pow_div_sqrt_clog_le_interpolationScale {n : ℕ} (hn : 16384 ≤ n) :
    (2 : ℝ) ^ (n / (Nat.clog 2 n).sqrt) ≤ (2 : ℝ) ^ (32 * interpolationScale n) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (div_sqrt_clog_le_interpolationScale hn)

/-- **Section 5.5 free-variable `rowCost` bound against `interpolationScale n` (printed p. 39):**
Whenever `16384 ≤ n`, `n ≤ 2 * n'`, `n' ≤ n`, and `hF : Feasible β n' b_occ w_width M'`,
`(n' : ℝ) * rowCost β n' ≤ 32896 * ((β : ℝ) + 3) * interpolationScale n`. -/
theorem Feasible.mul_rowCost_le_interpolationScale {β n n' b_occ w_width M' : ℕ}
    (hF : Feasible β n' b_occ w_width M') (hn : 16384 ≤ n)
    (hn_le : n ≤ 2 * n') (hn'_le : n' ≤ n) :
    (n' : ℝ) * rowCost β n' ≤ 32896 * ((β : ℝ) + 3) * interpolationScale n := by
  calc (n' : ℝ) * rowCost β n'
      ≤ 2056 * ((β : ℝ) + 3) *
          ((n : ℝ) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n)) :=
        hF.mul_rowCost_le_of_le_two_mul hn_le hn'_le
    _ ≤ 2056 * ((β : ℝ) + 3) * (16 * interpolationScale n) :=
        mul_le_mul_of_nonneg_left (mul_iter_clog_sq_div_sqrt_clog_le_interpolationScale hn)
          (by positivity)
    _ = 32896 * ((β : ℝ) + 3) * interpolationScale n := by ring

/-- **Evaluation-box prefactor bound against `interpolationScale n`:**
Whenever `16384 ≤ n` and `n' ≤ n`,
`2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) ≤ interpolationScale n`. -/
theorem two_mul_numNodes_mul_numGroups_le_interpolationScale {n n' : ℕ}
    (hn : 16384 ≤ n) (hn'_le : n' ≤ n) :
    2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) ≤ interpolationScale n := by
  obtain ⟨hlam14, hcube_le, hX_pos, hX_le_lam, hL2, _⟩ := log_add_sixteen_bounds hn
  set lam := Nat.clog 2 n
  set X := Real.log ((n : ℝ) + 16)
  set L := Real.log X
  have hQ_le : numNodes n' ≤ lam :=
    (Nat.div_le_self _ _).trans (Nat.clog_mono_right 2 hn'_le)
  have hr_le : numGroups n' ≤ lam :=
    ((Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)).trans (Nat.clog_mono_right 2 hn'_le)
  have hprod_nat : 2 * numNodes n' * numGroups n' ≤ 2 * lam ^ 2 := by
    calc 2 * numNodes n' * numGroups n'
        ≤ 2 * lam * lam := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hQ_le) hr_le
      _ = 2 * lam ^ 2 := by ring
  have hprod_r : 2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) ≤ 2 * (lam : ℝ) ^ 2 := by
    exact_mod_cast hprod_nat
  have hsqrtX_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX_pos
  have hsqrtX_le_lam : Real.sqrt X ≤ (lam : ℝ) := by
    have hlam1 : (1 : ℝ) ≤ lam := by exact_mod_cast (by omega : 1 ≤ lam)
    have hsqrt_lam : Real.sqrt (lam : ℝ) ≤ (lam : ℝ) := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    exact (Real.sqrt_le_sqrt hX_le_lam).trans hsqrt_lam
  have hcube_r : 2 * (lam : ℝ) ^ 3 ≤ (n : ℝ) := by exact_mod_cast hcube_le
  have hL_sq1 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  unfold interpolationScale
  refine hprod_r.trans ((le_div_iff₀ hsqrtX_pos).mpr ?_)
  calc 2 * (lam : ℝ) ^ 2 * Real.sqrt X
      ≤ 2 * (lam : ℝ) ^ 2 * (lam : ℝ) := mul_le_mul_of_nonneg_left hsqrtX_le_lam (by positivity)
    _ = 2 * (lam : ℝ) ^ 3 := by ring
    _ ≤ (n : ℝ) := hcube_r
    _ ≤ (n : ℝ) * L ^ 2 := le_mul_of_one_le_right (Nat.cast_nonneg n) hL_sq1

end Cslib.Complexity.SubexponentialSAT.ReplacementParams

namespace Cslib.BitString

open Finset
open Cslib.LinearAlgebra
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

variable {ι : Type*} {n' : ℕ}

/-! ### 3. General Section 5.5 `2 ^ (A * interpolationScale n)` domain-examination bounds -/

/-- Explicit exponent multiplier `2 + 65792 * (k * (2 * c + 4) + 4) * (β + 3)` bounding the
single-branch domain-examination count against `(2 : ℝ) ^ (A * interpolationScale n)`. -/
def branchExamScaleCoeff (β k c : ℕ) : ℕ :=
  2 + 65792 * (k * (2 * c + 4) + 4) * (β + 3)

private theorem exp_le_two_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x ≤ (2 : ℝ) ^ (2 * x) := by
  rw [Real.rpow_def_of_pos two_pos, Real.exp_le_exp]
  nlinarith [Real.log_two_gt_d9]

/-- **Section 5.5 single-branch `interpolationScale` domain-examination bound (printed p. 39):**
When `16384 ≤ Fintype.card ι`, `Fintype.card ι ≤ 2 * n'`, `n' ≤ Fintype.card ι`,
`#I ≤ c * Fintype.card ι`, and `hF : Feasible β n' b_occ w_width M'`, at
`d = k * (#I + 2 * (branchPrecision (Fintype.card ι) - 1))` and
`q = (d * rowBound β n') / numNodes n'`, the induced Section 3 counting design
`C := hF.toCountingDesign D s` satisfies
`(∑ t : Fin (numNodes n'), (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
  (2 * (#(C.measurementBox t) : ℝ) *
    ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ)))
  ≤ (2 : ℝ) ^ ((branchExamScaleCoeff β k c : ℝ) * interpolationScale (Fintype.card ι))`. -/
theorem Feasible.branch_domainExaminationBound_le_two_pow_interpolationScale [Fintype ι]
    {F_idx : Type*} [Fintype F_idx] {scope : F_idx → Finset (Fin n')}
    {β b_occ w_width M' k c : ℕ} {κ : Type*} (I : Finset κ)
    (hF : Feasible β n' b_occ w_width M')
    (D : ReplacementDesign scope (numNodes n') (numGroups n') (intervalStart β n')
      (rowBound β n') (tauRat n'))
    (s : Finset F_idx)
    (hI : #I ≤ c * Fintype.card ι)
    (hn : 16384 ≤ Fintype.card ι)
    (hn_le : Fintype.card ι ≤ 2 * n')
    (hn'_le : n' ≤ Fintype.card ι) :
    let d := k * (#I + 2 * (branchPrecision (Fintype.card ι) - 1))
    let q := (d * rowBound β n') / numNodes n'
    let C := hF.toCountingDesign D s
    (∑ t : Fin (numNodes n'),
        (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
          (2 * (#(C.measurementBox t) : ℝ) *
            ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
      2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n') ∧
    2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp (((k * (2 * c + 4) + 4 : ℕ) : ℝ) * (n' : ℝ) * rowCost β n') ≤
      (2 : ℝ) ^ ((branchExamScaleCoeff β k c : ℝ) * interpolationScale (Fintype.card ι)) := by
  intro d q C
  have hbound1 := (hF.branch_domainExaminationBound_le (k := k) I D s hI hn_le).1
  refine ⟨hbound1, ?_⟩
  set N := Fintype.card ι
  have hscale_nonneg : 0 ≤ interpolationScale N := by
    have hpre := two_mul_numNodes_mul_numGroups_le_interpolationScale hn hn'_le
    exact (by positivity : (0 : ℝ) ≤ 2 * (numNodes n' : ℝ) * (numGroups n' : ℝ)).trans hpre
  have hpre_pow :
      2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) ≤ (2 : ℝ) ^ (2 * interpolationScale N) := by
    calc 2 * (numNodes n' : ℝ) * (numGroups n' : ℝ)
        ≤ interpolationScale N := two_mul_numNodes_mul_numGroups_le_interpolationScale hn hn'_le
      _ ≤ Real.exp (interpolationScale N) :=
          (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      _ ≤ (2 : ℝ) ^ (2 * interpolationScale N) := exp_le_two_rpow_two_mul hscale_nonneg
  have hrc := hF.mul_rowCost_le_interpolationScale hn hn_le hn'_le
  have hrc_nonneg : 0 ≤ (n' : ℝ) * rowCost β n' := by
    unfold rowCost tau
    have hQ : 6 * rowBound β n' ≤ numNodes n' := hF.six_mul_rowBound_le_numNodes
    have hR : 32 ≤ rowBound β n' := hF.thirtyTwo_le_rowBound
    have hr : 2 ≤ numGroups n' := hF.two_le_numGroups
    have hpos_r : (0 : ℝ) < numGroups n' := Nat.cast_pos.mpr (by omega)
    have hpos_Q : (0 : ℝ) < numNodes n' := Nat.cast_pos.mpr (by omega)
    have hlog1 : 0 ≤ Real.log (2 * (numNodes n' : ℝ) / rowBound β n') := by
      refine Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)
      exact_mod_cast (by omega : rowBound β n' ≤ 2 * numNodes n')
    have haux_nn : (0 : ℝ) ≤ (auxDim n' : ℝ) := Nat.cast_nonneg _
    have hlog2 : 0 ≤ Real.log (2 * (auxDim n' : ℝ) + 1) :=
      Real.log_nonneg (by linarith)
    positivity
  set M_coeff : ℕ := k * (2 * c + 4) + 4
  have hexp_arg :
      (M_coeff : ℝ) * (n' : ℝ) * rowCost β n' ≤
        (M_coeff : ℝ) * (32896 * ((β : ℝ) + 3) * interpolationScale N) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hrc (Nat.cast_nonneg M_coeff)
  have hexp_pow :
      Real.exp ((M_coeff : ℝ) * (n' : ℝ) * rowCost β n') ≤
        (2 : ℝ) ^ ((65792 * M_coeff * (β + 3) : ℕ) * interpolationScale N) := by
    calc Real.exp ((M_coeff : ℝ) * (n' : ℝ) * rowCost β n')
        ≤ (2 : ℝ) ^ (2 * ((M_coeff : ℝ) * (n' : ℝ) * rowCost β n')) :=
          exp_le_two_rpow_two_mul
            (by rw [mul_assoc]; exact mul_nonneg (Nat.cast_nonneg _) hrc_nonneg)
      _ ≤ (2 : ℝ) ^
            (2 * ((M_coeff : ℝ) * (32896 * ((β : ℝ) + 3) * interpolationScale N))) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = (2 : ℝ) ^ ((65792 * M_coeff * (β + 3) : ℕ) * interpolationScale N) := by
          congr 1; push_cast; ring
  calc 2 * (numNodes n' : ℝ) * (numGroups n' : ℝ) *
        Real.exp ((M_coeff : ℝ) * (n' : ℝ) * rowCost β n')
      ≤ (2 : ℝ) ^ (2 * interpolationScale N) *
          (2 : ℝ) ^ ((65792 * M_coeff * (β + 3) : ℕ) * interpolationScale N) :=
        mul_le_mul hpre_pow hexp_pow (Real.exp_pos _).le (by positivity)
    _ = (2 : ℝ) ^ ((branchExamScaleCoeff β k c : ℝ) * interpolationScale N) := by
        rw [← Real.rpow_add two_pos]
        congr 1
        unfold branchExamScaleCoeff
        dsimp only [M_coeff]
        push_cast
        ring

/-- **Branch-assignment sum bound against `interpolationScale`:**
Whenever `16384 ≤ Fintype.card ι` and
`#(branchAssignments S) ≤ 2 ^ (Fintype.card ι / (Nat.clog 2 (Fintype.card ι)).sqrt)`, any
per-branch family `examSum` bounded by
`(2 : ℝ) ^ ((A : ℝ) * interpolationScale (Fintype.card ι))` sums across `branchAssignments S` to at
most `(2 : ℝ) ^ (((A + 32 : ℕ) : ℝ) * interpolationScale (Fintype.card ι))`. -/
theorem sum_branchAssignments_le_two_pow_interpolationScale [Fintype ι] [DecidableEq ι]
    {A : ℕ} {S : Finset ι}
    (hn : 16384 ≤ Fintype.card ι)
    (hbranches : #(branchAssignments S) ≤
      2 ^ (Fintype.card ι / (Nat.clog 2 (Fintype.card ι)).sqrt))
    (examSum : (ι → Bool) → ℝ)
    (hexam : ∀ b ∈ branchAssignments S,
      examSum b ≤ (2 : ℝ) ^ ((A : ℝ) * interpolationScale (Fintype.card ι))) :
    (∑ b ∈ branchAssignments S, examSum b) ≤
      (2 : ℝ) ^ (((A + 32 : ℕ) : ℝ) * interpolationScale (Fintype.card ι)) := by
  have hbranches_r :
      (#(branchAssignments S) : ℝ) ≤ (2 : ℝ) ^ (32 * interpolationScale (Fintype.card ι)) := by
    calc (#(branchAssignments S) : ℝ)
        ≤ ((2 ^ (Fintype.card ι / (Nat.clog 2 (Fintype.card ι)).sqrt) : ℕ) : ℝ) :=
          Nat.cast_le.mpr hbranches
      _ = (2 : ℝ) ^ (Fintype.card ι / (Nat.clog 2 (Fintype.card ι)).sqrt) := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ (32 * interpolationScale (Fintype.card ι)) :=
          two_pow_div_sqrt_clog_le_interpolationScale hn
  calc ∑ b ∈ branchAssignments S, examSum b
      ≤ ∑ _b ∈ branchAssignments S,
          (2 : ℝ) ^ ((A : ℝ) * interpolationScale (Fintype.card ι)) :=
        sum_le_sum hexam
    _ = (#(branchAssignments S) : ℝ) *
          (2 : ℝ) ^ ((A : ℝ) * interpolationScale (Fintype.card ι)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (32 * interpolationScale (Fintype.card ι)) *
          (2 : ℝ) ^ ((A : ℝ) * interpolationScale (Fintype.card ι)) :=
        mul_le_mul_of_nonneg_right hbranches_r (by positivity)
    _ = (2 : ℝ) ^ (((A + 32 : ℕ) : ℝ) * interpolationScale (Fintype.card ι)) := by
        rw [← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring

/-- **Section 5.5 multi-branch `interpolationScale` domain-examination bound (printed p. 39):**
When `16384 ≤ Fintype.card ι`, `1 ≤ b₀`, and
`totalIncidence I (fun i => equationScope (P i)) * (Nat.clog 2 (Fintype.card ι)).sqrt ≤`
`b₀ * Fintype.card ι`, the sum of the per-branch examination bounds across all
`b ∈ branchAssignments S` is at most
`(2 : ℝ) ^ (((branchExamScaleCoeff β k c + 32 : ℕ) : ℝ) * interpolationScale (Fintype.card ι))`. -/
theorem sum_branch_domainExaminationBound_le_two_pow_interpolationScale [Fintype ι] [DecidableEq ι]
    {β k c b₀ : ℕ} {κ : Type*}
    (I : Finset κ) (P : κ → Finset (Finset ι))
    (hn : 16384 ≤ Fintype.card ι)
    (hb₀ : 1 ≤ b₀)
    (hM : totalIncidence I (fun i => equationScope (P i)) * (Nat.clog 2 (Fintype.card ι)).sqrt ≤
      b₀ * Fintype.card ι)
    (examSum : (ι → Bool) → ℝ)
    (hexam : ∀ b ∈ branchAssignments (heavyVars univ I (fun i => equationScope (P i)) b₀),
      examSum b ≤
        (2 : ℝ) ^ ((branchExamScaleCoeff β k c : ℝ) * interpolationScale (Fintype.card ι))) :
    (∑ b ∈ branchAssignments (heavyVars univ I (fun i => equationScope (P i)) b₀), examSum b) ≤
      (2 : ℝ) ^ (((branchExamScaleCoeff β k c + 32 : ℕ) : ℝ) *
        interpolationScale (Fintype.card ι)) := by
  have hsqrt1 : 1 ≤ (Nat.clog 2 (Fintype.card ι)).sqrt := by
    refine Nat.le_sqrt.mpr ?_
    have h4 : 2 ^ 0 < Fintype.card ι := by omega
    have hclog : 0 < Nat.clog 2 (Fintype.card ι) := (Nat.lt_clog_iff_pow_lt one_lt_two).mpr h4
    omega
  have hbranches :=
    card_branchAssignments_heavyVars_le_two_pow_div I (fun i => equationScope (P i)) hb₀
      hsqrt1 hM
  exact sum_branchAssignments_le_two_pow_interpolationScale hn hbranches examSum hexam

end Cslib.BitString

namespace Cslib.Logic.PL

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

variable {V : Type*} {n' : ℕ}

/-! ### 4. Section 6.3 `CNF.parityRowSystem` domain-examination bounds against `interpolationScale`
-/

/-- Explicit exponent multiplier `branchExamScaleCoeff (2 * β_B + 5) k 6` for a width-`≤ k` CNF
with clause-to-variable ratio `B ≤ C_B * (Nat.clog 2 n) ^ β_B`. -/
def CNF.parityBranchExamScaleCoeff (k β_B : ℕ) : ℕ :=
  branchExamScaleCoeff (2 * β_B + 5) k 6

/-- **Section 6.3 single-branch `interpolationScale` domain-examination bound for
`CNF.parityRowSystem` (equation-count ratio `c = 6`, printed p. 43):**
When `16384 ≤ Fintype.card V`, `rows.length ≤ 6 * Fintype.card V`, `Fintype.card V ≤ 2 * n'`,
`n' ≤ Fintype.card V`, and `hF : Feasible β n' b_occ w_width M'`, the single-branch
domain-examination sum of `C := hF.toCountingDesign D s` is bounded by
`(2 : ℝ) ^ ((branchExamScaleCoeff β k 6 : ℝ) * interpolationScale (Fintype.card V))`. -/
theorem CNF.branch_domainExaminationBound_parityRowSystem_le_two_pow_interpolationScale [Fintype V]
    {F_idx : Type*} [Fintype F_idx] {scope : F_idx → Finset (Fin n')}
    {φ : CNF V} {β b_occ w_width M' k : ℕ}
    (rows : List (Fin φ.length → Bool))
    (hF : Feasible β n' b_occ w_width M')
    (D : ReplacementDesign scope (numNodes n') (numGroups n') (intervalStart β n')
      (rowBound β n') (tauRat n'))
    (s : Finset F_idx)
    (hlen : rows.length ≤ 6 * Fintype.card V)
    (hn : 16384 ≤ Fintype.card V)
    (hn_le : Fintype.card V ≤ 2 * n')
    (hn'_le : n' ≤ Fintype.card V) :
    let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
    let q := (d * rowBound β n') / numNodes n'
    let C := hF.toCountingDesign D s
    (∑ t : Fin (numNodes n'),
        (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
          (2 * (#(C.measurementBox t) : ℝ) *
            ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
      (2 : ℝ) ^ ((branchExamScaleCoeff β k 6 : ℝ) * interpolationScale (Fintype.card V)) := by
  intro d q C
  have hcard : #(univ : Finset (Fin rows.length)) ≤ 6 * Fintype.card V := by
    simpa only [card_univ, Fintype.card_fin] using hlen
  have h := Feasible.branch_domainExaminationBound_le_two_pow_interpolationScale
    (ι := V) (k := k) (c := 6) (univ : Finset (Fin rows.length)) hF D s hcard hn hn_le hn'_le
  simpa only [card_univ, Fintype.card_fin] using h.1.trans h.2

/-- **Section 6.3 multi-branch `interpolationScale` domain-examination bound for
`CNF.parityRowSystem` (equation-count ratio `c = 6`, printed p. 43):**
When `16384 ≤ Fintype.card V`, `∀ c ∈ φ, c.length ≤ k`, `∀ r ∈ rows, weight r ≤ W`,
`rows.length ≤ 6 * Fintype.card V`, `1 ≤ b₀`, and
`(6 * (k * (W * 2 ^ k))) * (Nat.clog 2 (Fintype.card V)).sqrt ≤ b₀`, if each branch
`b ∈ branchAssignments S` has its examination sum bounded by
`(2 : ℝ) ^ ((branchExamScaleCoeff β k 6 : ℝ) * interpolationScale (Fintype.card V))`, then the
sum across all `b ∈ branchAssignments S` is bounded by
`(2 : ℝ) ^ (((branchExamScaleCoeff β k 6 + 32 : ℕ) : ℝ) * interpolationScale (Fintype.card V))`. -/
theorem CNF.sum_branch_domainExaminationBound_parityRowSystem_le_two_pow_interpolationScale
    [Fintype V] [DecidableEq V]
    {φ : CNF V} {β k W b₀ : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {rows : List (Fin φ.length → Bool)} (hW : ∀ r ∈ rows, weight r ≤ W)
    (hlen : rows.length ≤ 6 * Fintype.card V)
    (hn : 16384 ≤ Fintype.card V)
    (hb₀ : 1 ≤ b₀)
    (h_thresh : (6 * (k * (W * 2 ^ k))) * (Nat.clog 2 (Fintype.card V)).sqrt ≤ b₀)
    (examSum : (V → Bool) → ℝ)
    (hexam : ∀ b ∈ branchAssignments
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀),
      examSum b ≤
        (2 : ℝ) ^ ((branchExamScaleCoeff β k 6 : ℝ) * interpolationScale (Fintype.card V))) :
    (∑ b ∈ branchAssignments
        (heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀),
        examSum b) ≤
      (2 : ℝ) ^ (((branchExamScaleCoeff β k 6 + 32 : ℕ) : ℝ) *
        interpolationScale (Fintype.card V)) := by
  have hM :
      totalIncidence (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) *
        (Nat.clog 2 (Fintype.card V)).sqrt ≤
      b₀ * Fintype.card V := by
    calc totalIncidence (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) *
          (Nat.clog 2 (Fintype.card V)).sqrt
        ≤ ((6 * (k * (W * 2 ^ k))) * Fintype.card V) *
            (Nat.clog 2 (Fintype.card V)).sqrt :=
          Nat.mul_le_mul_right _ (CNF.totalIncidence_parityRowSystem_le_six_mul hk hW hlen)
      _ = ((6 * (k * (W * 2 ^ k))) * (Nat.clog 2 (Fintype.card V)).sqrt) * Fintype.card V := by
          ring
      _ ≤ b₀ * Fintype.card V := Nat.mul_le_mul_right _ h_thresh
  exact sum_branch_domainExaminationBound_le_two_pow_interpolationScale
    (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) hn hb₀ hM examSum hexam

/-- **End-to-end Section 6.3 schedule feasibility, `ReplacementDesign` existence, and
`2 ^ (A * interpolationScale n)` examination bound for `CNF.parityRowSystem`**:
For any `k C_B β_B : ℕ`, there exists `N₁ ≥ 16384` such that for any width-`≤ k` CNF `φ : CNF V`
with `N₁ ≤ Fintype.card V`, `φ.length ≤ B * Fintype.card V`, and
`B ≤ C_B * (Nat.clog 2 (Fintype.card V)) ^ β_B`, and any `rows : List (Fin φ.length → Bool)` with
`rows.length ≤ 6 * Fintype.card V`, `∀ r ∈ rows, weight r ≤ W`, and
`W ≤ initialRowWeightBound B φ.length`, at `b₀ = CNF.parityBranchThreshold k W (Fintype.card V)`
and `β = 2 * β_B + 5`:
1. Every branch `b : V → Bool` unconditionally satisfies `Feasible (2 * β_B + 5) n'` and admits a
   concrete `ReplacementDesign`, whose single-branch examination count is bounded by
   `(2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) * interpolationScale (Fintype.card V))`.
2. Any per-branch examination family bounded by that single-branch quantity sums across
   `branchAssignments S` to at most
   `(2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *`
   `interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_branch_schedule_and_examBound_parityRowSystem_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' B W : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        N₁ ≤ Fintype.card V →
        φ.length ≤ B * Fintype.card V →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        W ≤ initialRowWeightBound B φ.length →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r ∈ rows, weight r ≤ W) →
          rows.length ≤ 6 * Fintype.card V →
          let b₀ := CNF.parityBranchThreshold k W (Fintype.card V)
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ (e : ↥(univ \ S) ≃ Fin n'),
            (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
            (∀ b : V → Bool,
              ∃ (hF : Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                  (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                    #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f)))
                (D : ReplacementDesign
                  (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                  (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                  (rowBound (2 * β_B + 5) n') (tauRat n')),
                ∀ s_active : Finset
                    ({j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n'),
                  let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                  let q := (d * rowBound (2 * β_B + 5) n') / numNodes n'
                  let C := hF.toCountingDesign D s_active
                  (∑ t : Fin (numNodes n'),
                      (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                        (2 * (#(C.measurementBox t) : ℝ) *
                          ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                    (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                      interpolationScale (Fintype.card V))) ∧
            ∀ (examSum : (V → Bool) → ℝ),
              (∀ b ∈ branchAssignments S,
                examSum b ≤
                  (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                    interpolationScale (Fintype.card V))) →
              (∑ b ∈ branchAssignments S, examSum b) ≤
                (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *
                  interpolationScale (Fintype.card V)) := by
  obtain ⟨N₀, _, hsched⟩ := CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow k C_B β_B
  refine ⟨max N₀ 16384, le_max_right _ _,
    fun {V _ _ φ n' B W} hk hN₁ hm hB hW_bound {rows} hW hlen => ?_⟩
  intro b₀ S e
  have hN₀ : N₀ ≤ Fintype.card V := (le_max_left _ _).trans hN₁
  have hn16384 : 16384 ≤ Fintype.card V := (le_max_right _ _).trans hN₁
  obtain ⟨_, ⟨hn_le, _⟩, hbranches, hfeas⟩ := hsched hk hN₀ hm hB hW_bound hW hlen e
  have hn'_le : n' ≤ Fintype.card V := by
    have heq : #(univ \ S) = n' := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr e
    rw [← heq]
    exact card_le_univ (univ \ S)
  refine ⟨⟨hn_le, hn'_le⟩, fun b => ?_, fun examSum hexam => ?_⟩
  · obtain ⟨hF, ⟨D⟩⟩ := hfeas b
    refine ⟨hF, D, fun s_active => ?_⟩
    exact CNF.branch_domainExaminationBound_parityRowSystem_le_two_pow_interpolationScale
      rows hF D s_active hlen hn16384 hn_le hn'_le
  · exact sum_branchAssignments_le_two_pow_interpolationScale hn16384 hbranches examSum hexam

/-- **End-to-end Lemma 6.1 + Lemma 6.2 + Section 6.3 greedy parity-test schedule with
`2 ^ (A * interpolationScale n)` domain-examination bounds**:
For any `k C_B β_B : ℕ`, there exists `N₁ ≥ 16384` such that for any width-`≤ k` CNF `φ : CNF V`
with `N₁ ≤ Fintype.card V`, `1 ≤ B`, `B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B`, and
`φ.length ≤ B * Fintype.card V`, at `D₀ = initialRowWeightBound B φ.length`,
`P = greedyRowListLength B φ.length`, `b₀ = CNF.parityBranchThreshold k D₀ (Fintype.card V)`,
and `β = 2 * β_B + 5`:
1. There exists an initial row list `A₀` of length `≤ 3 * Fintype.card V` and row weight `≤ D₀`
   such that any greedy extension `A` up to stage `3 * Fintype.card V` satisfies
   `commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) = φ.modelCountOn univ`.
2. At every greedy stage `i ≤ 3 * Fintype.card V`, `(A i).length ≤ 6 * Fintype.card V`, every
   branch `b : V → Bool` admits a concrete `ReplacementDesign` with single-branch examination count
   at most `(2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *`
   `interpolationScale (Fintype.card V))`, and any per-branch examination family bounded by that
   quantity sums across `branchAssignments S_i` to at most
   `(2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *`
   `interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_greedy_parityRowSystem_branch_schedule_and_examBound_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        N₁ ≤ Fintype.card V →
        1 ≤ B →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := initialRowWeightBound B φ.length
        let P := greedyRowListLength B φ.length
        let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
        ∃ A₀ : List (Fin φ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
          (∀ r ∈ A₀, weight r ≤ D₀) ∧
          ∀ (A : ℕ → List (Fin φ.length → Bool))
            (γ : ℕ → Fin P → Fin φ.length × Bool),
            A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
            (∀ i (γ' : Fin P → Fin φ.length × Bool),
              commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))) →
            commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) =
              φ.modelCountOn Finset.univ ∧
            ∀ i ≤ 3 * Fintype.card V,
              (A i).length ≤ 6 * Fintype.card V ∧
              let S := heavyVars univ (univ : Finset (Fin (A i).length))
                (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀
              ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
                (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
                (∀ b : V → Bool,
                  ∃ (hF : Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (D₀ * 2 ^ k)) 1)
                      (∑ f : {j : Fin (A i).length //
                          j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n',
                        #(branchAugmentedScope S e univ (φ.parityRowSystem (A i)) b f)))
                    (D : ReplacementDesign
                      (branchAugmentedScope S e univ (φ.parityRowSystem (A i)) b)
                      (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                      (rowBound (2 * β_B + 5) n') (tauRat n')),
                    ∀ s_active : Finset
                        ({j : Fin (A i).length //
                            j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n'),
                      let d := k * ((A i).length + 2 * (branchPrecision (Fintype.card V) - 1))
                      let q := (d * rowBound (2 * β_B + 5) n') / numNodes n'
                      let C := hF.toCountingDesign D s_active
                      (∑ t : Fin (numNodes n'),
                          (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                            (2 * (#(C.measurementBox t) : ℝ) *
                              ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                        (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                          interpolationScale (Fintype.card V))) ∧
                ∀ (examSum : (V → Bool) → ℝ),
                  (∀ b ∈ branchAssignments S,
                    examSum b ≤
                      (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                        interpolationScale (Fintype.card V))) →
                  (∑ b ∈ branchAssignments S, examSum b) ≤
                    (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *
                      interpolationScale (Fintype.card V)) := by
  obtain ⟨N₀, _, hgreedy_sched⟩ :=
    CNF.exists_greedy_parityRowSystem_branch_schedule_of_le_clog_pow k C_B β_B
  refine ⟨max N₀ 16384, le_max_right _ _,
    fun {V _ _} φ {B} hk hN₁ hB1 hB_le hm => ?_⟩
  intro D₀ P b₀
  have hN₀ : N₀ ≤ Fintype.card V := (le_max_left _ _).trans hN₁
  have hn16384 : 16384 ≤ Fintype.card V := (le_max_right _ _).trans hN₁
  obtain ⟨A₀, hlen0, hw0, hgreedy⟩ := hgreedy_sched φ hk hN₀ hB1 hB_le hm
  refine ⟨A₀, hlen0, hw0, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hstage⟩ := hgreedy A γ h0 hA hγ
  refine ⟨hcount, fun i hi => ?_⟩
  obtain ⟨hlen_i, hstage_e⟩ := hstage i hi
  refine ⟨hlen_i, fun {n'} e => ?_⟩
  obtain ⟨⟨hn_le, _⟩, hbranches, hfeas⟩ := hstage_e e
  have hn'_le : n' ≤ Fintype.card V := by
    have heq :
        #(univ \ heavyVars univ (univ : Finset (Fin (A i).length))
            (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀) = n' := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr e
    rw [← heq]
    exact card_le_univ _
  refine ⟨⟨hn_le, hn'_le⟩, fun b => ?_, fun examSum hexam => ?_⟩
  · obtain ⟨hF, ⟨D⟩⟩ := hfeas b
    refine ⟨hF, D, fun s_active => ?_⟩
    exact CNF.branch_domainExaminationBound_parityRowSystem_le_two_pow_interpolationScale
      (A i) hF D s_active hlen_i hn16384 hn_le hn'_le
  · exact sum_branchAssignments_le_two_pow_interpolationScale hn16384 hbranches examSum hexam

end Cslib.Logic.PL
