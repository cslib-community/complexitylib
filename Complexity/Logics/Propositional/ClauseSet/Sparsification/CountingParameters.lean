/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.Choose.Real
public import Complexity.Foundations.Data.Nat.Log
import Mathlib.Data.Nat.Find

/-!
# First-success geometric thresholds for counting sparsification

For fixed width `k ≥ 2` and inverse error budget `B ≥ 1`, Appendix A.3 of [OpenAI2026ETH]
tests dyadic threshold bases `M` in increasing order. The exact test is `Γ ≤ M` and
`B * Γ * ⌈log₂ (4 * C * M)⌉ ≤ M`, where `C = 4 ∑ r < k - 1, (3 * M) ^ r` and
`Γ = 4 ∑ r < k - 1, 3 ^ r`. `countingThresholdBase` implements this first-success search.
The parameters depend only on `k` and `B`, before any input formula or variable budget.

An explicit successful candidate proves termination and the sharp bound
`M = O_k(B log(2B))`; that candidate does not replace the first-success output. Widths zero
and one have empty coefficient sums and use the separate default `M = 2`. The same total
default is used at `B = 0`, which is outside the positive-error-budget specification.

This module proves numerical selection and size bounds, not a native bit-cost certificate,
tree-word counting, or the complete counting sparsification theorem.

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.countingDepthCoeff`: the source coefficient `C`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingBChoiceCoeff`: the source coefficient `Γ`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingThresholdBase`: the first successful dyadic base.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.countingDepthCoeff_le_mul_pow`:
  the degree-`k - 2` bound on the depth coefficient in terms of the threshold base.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingThresholdBase_spec`: the exact integer test.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingThresholdBase_first`: dyadic minimality.
* `Cslib.Logic.PL.ClauseSet.Sparsification.exists_countingThresholdBase_le_mul_clog`:
  the sharp size dependence on the inverse error budget.
* `Cslib.Logic.PL.ClauseSet.Sparsification.isBigO_countingThresholdBase`:
  the real logarithmic bound.
* `Cslib.Logic.PL.ClauseSet.Sparsification.exists_clog_countingThresholdBase_le`:
  a logarithmic bound on the number of dyadic candidates tested.
* `Cslib.Logic.PL.ClauseSet.Sparsification.sum_choose_le_countingThresholdBase`:
  the all-input-size numerical binomial-tail bound for the selected parameter.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.3, pp. 46–47][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

/-- The linear path-depth coefficient `C` in Appendix A.3. -/
def countingDepthCoeff (k M : ℕ) : ℕ := 4 * ∑ r ∈ range (k - 1), (3 * M) ^ r

/-- The coefficient `Γ` in the weighted B-choice bound of Appendix A.3. -/
def countingBChoiceCoeff (k : ℕ) : ℕ := 4 * ∑ r ∈ range (k - 1), 3 ^ r

/-- The depth coefficient is at least four once width two is allowed. -/
theorem four_le_countingDepthCoeff {k M : ℕ} (hk : 2 ≤ k) : 4 ≤ countingDepthCoeff k M := by
  have h := single_le_sum (f := fun r => (3 * M) ^ r)
    (fun r _ => Nat.zero_le _) (show 0 ∈ range (k - 1) by simp only [mem_range]; omega)
  simp only [pow_zero] at h
  exact Nat.mul_le_mul_left 4 h

/-- The B-choice coefficient is at least four once width two is allowed. -/
theorem four_le_countingBChoiceCoeff {k : ℕ} (hk : 2 ≤ k) : 4 ≤ countingBChoiceCoeff k := by
  simpa only [countingDepthCoeff, countingBChoiceCoeff, mul_one] using
    (four_le_countingDepthCoeff (M := 1) hk)

/-- The geometric depth coefficient has degree at most `k - 2` in a positive threshold base.
The coefficient depends only on the fixed width, including the empty sums at widths zero and one. -/
theorem countingDepthCoeff_le_mul_pow {k M : ℕ} (hM : 1 ≤ M) :
    countingDepthCoeff k M ≤ countingBChoiceCoeff k * M ^ (k - 2) := by
  calc countingDepthCoeff k M
      ≤ 4 * ∑ r ∈ range (k - 1), 3 ^ r * M ^ (k - 2) := by
        apply Nat.mul_le_mul_left 4
        apply sum_le_sum
        intro r hr
        rw [Nat.mul_pow]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by
          have := mem_range.mp hr
          omega))
    _ = countingBChoiceCoeff k * M ^ (k - 2) := by
      rw [← sum_mul]
      exact (Nat.mul_assoc _ _ _).symm

private abbrev Accepts (k B m : ℕ) : Prop :=
  countingBChoiceCoeff k ≤ 2 ^ m ∧
    B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k (2 ^ m) * 2 ^ m) ≤
      2 ^ m

private def offset (k : ℕ) : ℕ :=
  2 * (countingBChoiceCoeff k * (Nat.clog 2 (4 * countingBChoiceCoeff k) + 3 * (k - 1) + 1))

private def candidateExponent (k B : ℕ) : ℕ :=
  offset k + Nat.clog 2 B + Nat.clog 2 (Nat.clog 2 B + 1)

private theorem clog_depthCoeff_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    Nat.clog 2 (4 * countingDepthCoeff k (2 ^ m) * 2 ^ m) ≤
      Nat.clog 2 (4 * countingBChoiceCoeff k) + (k - 1) * m := by
  apply Nat.clog_le_of_le_pow
  calc 4 * countingDepthCoeff k (2 ^ m) * 2 ^ m
      ≤ 4 * (countingBChoiceCoeff k * (2 ^ m) ^ (k - 2)) * 2 ^ m :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (countingDepthCoeff_le_mul_pow Nat.one_le_two_pow))
    _ = (4 * countingBChoiceCoeff k) * (2 ^ m) ^ (k - 1) := by
      rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
      ring
    _ ≤ 2 ^ Nat.clog 2 (4 * countingBChoiceCoeff k) * (2 ^ m) ^ (k - 1) :=
      Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
    _ = 2 ^ (Nat.clog 2 (4 * countingBChoiceCoeff k) + (k - 1) * m) := by
      rw [← pow_mul, ← pow_add, Nat.mul_comm m]

private theorem offset_budget {k : ℕ} (hk : 2 ≤ k) :
    countingBChoiceCoeff k * (Nat.clog 2 (4 * countingBChoiceCoeff k) +
      (k - 1) * offset k + 2 * (k - 1)) ≤ 2 ^ offset k := by
  let g := countingBChoiceCoeff k
  let a := Nat.clog 2 (4 * g)
  let s := k - 1
  let t := g * (a + 3 * s + 1)
  have hg : 1 ≤ g := (by have := four_le_countingBChoiceCoeff hk; omega)
  have hga : g * a + 2 * g * s ≤ t := by dsimp only [t]; nlinarith
  have hgs : g * s + 1 ≤ t := by dsimp only [t]; nlinarith
  have hpoly : g * (a + s * (2 * t) + 2 * s) ≤ 2 * t ^ 2 + 1 := by
    nlinarith [Nat.mul_le_mul_right (2 * t) hgs]
  exact hpoly.trans (Nat.two_mul_sq_add_one_le_two_pow_two_mul t)

private theorem gamma_le_two_pow_offset {k : ℕ} (hk : 2 ≤ k) :
    countingBChoiceCoeff k ≤ 2 ^ offset k := by
  have hg : 1 ≤ countingBChoiceCoeff k := (by have := four_le_countingBChoiceCoeff hk; omega)
  have hgo : countingBChoiceCoeff k ≤ offset k := by unfold offset; nlinarith
  exact hgo.trans Nat.lt_two_pow_self.le

private theorem candidate_accepts {k B : ℕ} (hk : 2 ≤ k) :
    Accepts k B (candidateExponent k B) := by
  let L := Nat.clog 2 B
  have hL : Nat.clog 2 (L + 1) ≤ L := Nat.clog_le_of_le_pow Nat.lt_two_pow_self
  have hm : candidateExponent k B ≤ offset k + 2 * L := by
    dsimp only [candidateExponent, L] at *
    omega
  have hbudget := offset_budget hk
  have hcoeff : countingBChoiceCoeff k *
      (Nat.clog 2 (4 * countingBChoiceCoeff k) + (k - 1) * candidateExponent k B) ≤
      2 ^ offset k * (L + 1) := by
    have h1 := Nat.mul_le_mul_left (countingBChoiceCoeff k * (k - 1)) hm
    have h2 := Nat.mul_le_mul_right (L + 1) hbudget
    nlinarith [Nat.zero_le (countingBChoiceCoeff k *
      (Nat.clog 2 (4 * countingBChoiceCoeff k) + (k - 1) * offset k) * L)]
  refine ⟨(gamma_le_two_pow_offset hk).trans (Nat.pow_le_pow_right (by decide) (by
    unfold candidateExponent; omega)), ?_⟩
  calc B * countingBChoiceCoeff k *
        Nat.clog 2 (4 * countingDepthCoeff k (2 ^ candidateExponent k B) *
          2 ^ candidateExponent k B)
      ≤ B * (countingBChoiceCoeff k *
          (Nat.clog 2 (4 * countingBChoiceCoeff k) + (k - 1) * candidateExponent k B)) := by
        have := Nat.mul_le_mul_left (B * countingBChoiceCoeff k)
          (clog_depthCoeff_le hk (candidateExponent k B))
        simpa only [Nat.mul_assoc] using this
    _ ≤ B * (2 ^ offset k * (L + 1)) := Nat.mul_le_mul_left B hcoeff
    _ ≤ 2 ^ L * (2 ^ offset k * 2 ^ Nat.clog 2 (L + 1)) :=
      Nat.mul_le_mul (Nat.le_pow_clog (by decide) B)
        (Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) (L + 1)))
    _ = 2 ^ candidateExponent k B := by
      unfold candidateExponent
      rw [pow_add, pow_add]
      ring

private theorem exists_accepts {k : ℕ} (hk : 2 ≤ k) (B : ℕ) :
    ∃ m, Accepts k B m := ⟨candidateExponent k B, candidate_accepts hk⟩

/-- The first dyadic `M ≥ Γ` passing Appendix A.3's exact test for error budget `σ = 1/B`.
Widths at most one and the out-of-domain input `B = 0` use the total default `2`. The existence
proof only bounds the search: `Nat.find` executes the decidable tests from exponent zero upward. -/
def countingThresholdBase (k B : ℕ) : ℕ :=
  if h : 2 ≤ k ∧ 1 ≤ B then
    2 ^ Nat.find (p := fun m => countingBChoiceCoeff k ≤ 2 ^ m ∧
      B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k (2 ^ m) * 2 ^ m) ≤
        2 ^ m) (by exact exists_accepts h.1 B)
  else 2

/-- The selected dyadic base passes both exact integer tests. -/
theorem countingThresholdBase_spec {k B : ℕ} (hk : 2 ≤ k) (hB : 1 ≤ B) :
    countingBChoiceCoeff k ≤ countingThresholdBase k B ∧
    B * countingBChoiceCoeff k *
      Nat.clog 2 (4 * countingDepthCoeff k (countingThresholdBase k B) *
        countingThresholdBase k B) ≤ countingThresholdBase k B := by
  simp only [countingThresholdBase, hk, hB, and_self, ↓reduceDIte]
  exact Nat.find_spec (exists_accepts hk B)

/-- The returned base is dyadic and every earlier power of two fails the exact test. -/
theorem countingThresholdBase_first {k B : ℕ} (hk : 2 ≤ k) (hB : 1 ≤ B) :
    ∃ m, countingThresholdBase k B = 2 ^ m ∧ ∀ j < m,
      ¬ (countingBChoiceCoeff k ≤ 2 ^ j ∧
        B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k (2 ^ j) * 2 ^ j) ≤
          2 ^ j) := by
  refine ⟨Nat.find (exists_accepts hk B), ?_, fun j hj => Nat.find_min _ hj⟩
  simp only [countingThresholdBase, hk, hB, and_self, ↓reduceDIte]

/-- A passing candidate with no earlier success computes the selected threshold base. This
permits finite evaluation proofs without unfolding the termination argument of `Nat.find`. -/
theorem countingThresholdBase_eq_two_pow {k B m : ℕ} (hk : 2 ≤ k) (hB : 1 ≤ B)
    (hpass : countingBChoiceCoeff k ≤ 2 ^ m ∧
      B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k (2 ^ m) * 2 ^ m) ≤
        2 ^ m)
    (hfirst : ∀ j < m, ¬ (countingBChoiceCoeff k ≤ 2 ^ j ∧
      B * countingBChoiceCoeff k * Nat.clog 2 (4 * countingDepthCoeff k (2 ^ j) * 2 ^ j) ≤
        2 ^ j)) : countingThresholdBase k B = 2 ^ m := by
  simp only [countingThresholdBase, hk, hB, and_self, ↓reduceDIte]
  congr 1
  exact (Nat.find_eq_iff _).mpr ⟨hpass, hfirst⟩

/-- Widths zero and one use `M = 2` separately from the geometric search. -/
theorem countingThresholdBase_of_lt_two {k : ℕ} (hk : k < 2) (B : ℕ) :
    countingThresholdBase k B = 2 := by simp [countingThresholdBase, show ¬ 2 ≤ k by omega]

/-- The inverse error budget zero is outside the specification and uses the total default. -/
theorem countingThresholdBase_zero (k : ℕ) : countingThresholdBase k 0 = 2 := by
  simp [countingThresholdBase]

private theorem thresholdBase_le_candidate {k B : ℕ} (hk : 2 ≤ k) (hB : 1 ≤ B) :
    countingThresholdBase k B ≤ 2 ^ candidateExponent k B := by
  simp only [countingThresholdBase, hk, hB, and_self, ↓reduceDIte]
  exact Nat.pow_le_pow_right (by decide) (Nat.find_min' _ (candidate_accepts hk))

/-- The first-success base has the sharp `B log(2B)` dependence. The constant depends only on
the fixed width; the proof supplies the explicit constant `2 ^ (offset k + 2)`. -/
theorem exists_countingThresholdBase_le_mul_clog {k : ℕ} (hk : 2 ≤ k) :
    ∃ A : ℕ, ∀ B : ℕ, 1 ≤ B →
      countingThresholdBase k B ≤ A * B * (Nat.clog 2 B + 1) := by
  refine ⟨2 ^ (offset k + 2), fun B hB => (thresholdBase_le_candidate hk hB).trans ?_⟩
  calc 2 ^ candidateExponent k B
      = 2 ^ offset k * 2 ^ Nat.clog 2 B * 2 ^ Nat.clog 2 (Nat.clog 2 B + 1) := by
        simp only [candidateExponent, pow_add]
    _ ≤ 2 ^ offset k * (2 * B) * (2 * (Nat.clog 2 B + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_clog_le_mul (by decide) (by omega)))
        (Nat.pow_clog_le_mul (by decide) (by omega))
    _ = 2 ^ (offset k + 2) * B * (Nat.clog 2 B + 1) := by rw [pow_add]; ring

/-- For fixed width the first-success parameter is `O(B log(2B))` as `B` tends to infinity. -/
theorem isBigO_countingThresholdBase {k : ℕ} (hk : 2 ≤ k) :
    (fun B : ℕ => (countingThresholdBase k B : ℝ)) =O[Filter.atTop]
      (fun B : ℕ => (B : ℝ) * Real.log (2 * B)) := by
  obtain ⟨A, hA⟩ := exists_countingThresholdBase_le_mul_clog hk
  refine Asymptotics.IsBigO.of_bound (2 * A / Real.log 2) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with B hB
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hlog : 0 ≤ Real.logb 2 (B : ℝ) := Real.logb_nonneg (by norm_num) hBR
  have hclog : (Nat.clog 2 B : ℝ) ≤ Real.logb 2 (B : ℝ) + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact (Nat.ceil_lt_add_one hlog).le
  have hlogmul : Real.logb 2 (2 * (B : ℝ)) = 1 + Real.logb 2 (B : ℝ) := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  have hclog' : (Nat.clog 2 B : ℝ) + 1 ≤ 2 * Real.logb 2 (2 * (B : ℝ)) := by
    rw [hlogmul]
    linarith
  have hlog0 : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by linarith)
  have hM0 : (0 : ℝ) ≤ countingThresholdBase k B := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hM0,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg B) hlog0)]
  calc (countingThresholdBase k B : ℝ)
      ≤ A * B * ((Nat.clog 2 B : ℝ) + 1) := by exact_mod_cast hA B hB
    _ ≤ A * B * (2 * Real.logb 2 (2 * (B : ℝ))) :=
      mul_le_mul_of_nonneg_left hclog' (by positivity)
    _ = (2 * A / Real.log 2) * ((B : ℝ) * Real.log (2 * B)) := by rw [Real.logb]; ring

/-- The selected exponent is at most `D + 2 * ⌈log₂ B⌉`, for a width-dependent constant `D`.
Thus testing exponents from zero through the first success uses at most this bound plus one
tests. This is a count of candidates, not a native bit-operation bound. -/
theorem exists_clog_countingThresholdBase_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ D : ℕ, ∀ B : ℕ, 1 ≤ B →
      Nat.clog 2 (countingThresholdBase k B) ≤ D + 2 * Nat.clog 2 B := by
  refine ⟨offset k, fun B hB => (Nat.clog_le_of_le_pow (thresholdBase_le_candidate hk hB)).trans ?_⟩
  have h : Nat.clog 2 (Nat.clog 2 B + 1) ≤ Nat.clog 2 B :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self
  unfold candidateExponent
  omega

/-- The selected geometric parameter gives the rounded binomial-tail bound for every variable
budget `N`, including zero. This is only a numerical bound; counting tree words is separate. -/
theorem sum_choose_le_countingThresholdBase {k B : ℕ} (hk : 2 ≤ k) (hB : 1 ≤ B) (N : ℕ) :
    ∑ j ∈ range (countingBChoiceCoeff k * N / countingThresholdBase k B + 1),
      (countingDepthCoeff k (countingThresholdBase k B) * N).choose j ≤ 2 ^ (N / B + 1) := by
  obtain ⟨hM, hbudget⟩ := countingThresholdBase_spec hk hB
  exact Cslib.sum_choose_le_two_pow_div_add_one (four_le_countingDepthCoeff hk)
    (four_le_countingBChoiceCoeff hk) hM hB hbudget N

/-- Every selected base, including the total defaults, is at least two. -/
theorem two_le_countingThresholdBase (k B : ℕ) : 2 ≤ countingThresholdBase k B := by
  by_cases h : 2 ≤ k ∧ 1 ≤ B
  · exact (by decide : 2 ≤ 4).trans
      ((four_le_countingBChoiceCoeff h.1).trans (countingThresholdBase_spec h.1 h.2).1)
  · simp [countingThresholdBase, h]

end Cslib.Logic.PL.ClauseSet.Sparsification
