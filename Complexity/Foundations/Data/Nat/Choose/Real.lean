/-
Copyright (c) 2026 Samuel Schlesinger, Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI, Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real bounds for partial binomial sums

The binomial generating function gives `∑ j ≤ e, q.choose j ≤ exp (q / T) * T ^ e`
for any real `T ≥ 1`. For `0 < e ≤ q`, choosing `T = q / e` gives `(exp 1 * q / e) ^ e`.
This bound remains valid above half the dimension. At radius zero the sum and bound are both one.

The generating-function proof is shared with the sparsification lemma. The logarithmic
consequences turn an exponential lower bound on the square of a partial binomial sum into
size-activity bounds; they include the zero-radius case using the usual total real operations.

An exact integer logarithm test also bounds the tail of dimension `C * N` and radius
`Γ * N / M` by `2 ^ (N / B)` for every `N`. This is an original specialization of the
generating-function bound, motivated by the geometric thresholds in Appendix A.3 of
[OpenAI2026ETH]; it does not construct the parameters or bound the cost of selecting them.

## Main results

* `Cslib.sum_choose_le_exp_mul_pow`: a real-parameter generating-function bound.
* `Cslib.sum_choose_le_exp_one_mul_div_pow`: the bound with parameter `q / e`.
* `Nat.choose_le_exp_mul_div_pow`: its single-binomial-coefficient consequence, for all `n, k`.
* `Cslib.sum_choose_le_two_rpow_div`: the geometric tail under an exact integer budget test.
* `Cslib.sum_choose_le_two_pow_div_add_one`: its natural-number rounded form.
* `Cslib.le_mul_logb_of_two_pow_le_sum_choose_sq`: the logarithmic consequence.
* `Cslib.mul_rpow_le_of_two_pow_le_sum_choose_sq`: the rearranged size lower bound.
* `Real.exists_one_le_and_mul_pow_le_pow`: a polynomial is eventually below an exponential with base
  `r > 1`.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 3.2]
  [ThresholdCircuitRepresentations2026]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.3, pp. 46–47][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib

open Finset

/-- A partial binomial sum is at most `exp (q / T) * T ^ e` for every real `T ≥ 1`.
The radius `e` may exceed `q`. -/
theorem sum_choose_le_exp_mul_pow (q e : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ Real.exp (q / T) * T ^ e := by
  have hT0 : 0 < T := by linarith
  set t : ℝ := 1 / T with ht
  have ht0 : 0 ≤ t := by positivity
  have hg : ∀ j, 0 ≤ (q.choose j : ℝ) * t ^ j := fun j => by positivity
  have hpartial : ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j ≤ (1 + t) ^ q := by
    set m := max (e + 1) (q + 1)
    calc ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j
        ≤ ∑ j ∈ range m, (q.choose j : ℝ) * t ^ j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (le_max_left _ _))
            fun j _ _ => hg j
      _ = ∑ j ∈ range (q + 1), (q.choose j : ℝ) * t ^ j := by
          refine (sum_subset (range_subset_range.mpr (le_max_right _ _)) fun j _ hj => ?_).symm
          rw [Nat.choose_eq_zero_of_lt (by simpa using hj), Nat.cast_zero, zero_mul]
      _ = (1 + t) ^ q := by
          rw [add_comm (1 : ℝ) t, add_pow]
          refine sum_congr rfl fun j _ => ?_
          rw [one_pow, mul_one, mul_comm]
  calc (∑ j ∈ range (e + 1), (q.choose j : ℝ))
      ≤ ∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j * T ^ e := by
        refine sum_le_sum fun j hj => ?_
        have hje : j ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have : 1 ≤ t ^ j * T ^ e := by
          rw [← Nat.add_sub_cancel' hje, pow_add, ← mul_assoc, ht, ← mul_pow, one_div,
            inv_mul_cancel₀ hT0.ne', one_pow, one_mul]
          exact one_le_pow₀ hT
        calc (q.choose j : ℝ) = (q.choose j : ℝ) * 1 := (mul_one _).symm
          _ ≤ (q.choose j : ℝ) * (t ^ j * T ^ e) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = (q.choose j : ℝ) * t ^ j * T ^ e := by ring
    _ = (∑ j ∈ range (e + 1), (q.choose j : ℝ) * t ^ j) * T ^ e := by rw [sum_mul]
    _ ≤ (1 + t) ^ q * T ^ e := by gcongr
    _ ≤ Real.exp t ^ q * T ^ e := by
        gcongr
        linarith [Real.add_one_le_exp t]
    _ = Real.exp (q / T) * T ^ e := by
        rw [← Real.exp_nat_mul, ht]
        ring_nf

/-- The standard bound `(exp 1 * q / e) ^ e` holds throughout `e ≤ q`, not just for
`e ≤ q / 2`. At `e = 0` both sides are one. -/
theorem sum_choose_le_exp_one_mul_div_pow {q e : ℕ} (heq : e ≤ q) :
    (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ (Real.exp 1 * q / e) ^ e := by
  by_cases he : e = 0
  · simp [he]
  have he0 : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le he0 (by exact_mod_cast heq)
  have hT : (1 : ℝ) ≤ q / e :=
    (le_div_iff₀ he0).mpr (by simpa only [one_mul] using (Nat.cast_le.mpr heq : (e : ℝ) ≤ q))
  have hqe : (q : ℝ) / (q / e) = e := by field_simp
  calc (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ≤ Real.exp e * ((q : ℝ) / e) ^ e := by
        simpa only [hqe] using sum_choose_le_exp_mul_pow q e ((q : ℝ) / e) hT
    _ = (Real.exp 1 * q / e) ^ e := by
        rw [mul_div_assoc, mul_pow, ← Real.exp_nat_mul]
        simp

end Cslib

namespace Nat

/-- A single binomial coefficient is at most `(exp 1 * n / k)^k`, including `k = 0`.
This follows from `Cslib.sum_choose_le_exp_one_mul_div_pow` when `k ≤ n`; otherwise the
coefficient vanishes. The statement is also present in
[Anthropic's formal source](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Util/Choose.lean#L52-L53);
this proof reuses the partial-sum bound. -/
theorem choose_le_exp_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  by_cases hkn : k ≤ n
  · calc
      (n.choose k : ℝ) ≤ ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) :=
        Finset.single_le_sum (fun j _ => Nat.cast_nonneg (n.choose j))
          (Finset.mem_range.mpr (by omega))
      _ ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k :=
        Cslib.sum_choose_le_exp_one_mul_div_pow hkn
  · rw [choose_eq_zero_of_lt (by omega), cast_zero]
    positivity

end Nat

namespace Cslib

open Finset

/-- For any input size `N`, the tail with dimension `C * N` and radius `Γ * N / M` is at most
`2 ^ (N / B)` when the exact integer test `B * Γ * ⌈log₂ (4 * C * M)⌉ ≤ M` holds.
This is an original corollary of `sum_choose_le_exp_mul_pow`, motivated by Appendix A.3 of
[OpenAI2026ETH], rather than a verbatim result from that source. Zero input and zero radius are
included. The parameters are supplied; no parameter-selection or complexity bound is asserted. -/
theorem sum_choose_le_two_rpow_div {C Γ M B : ℕ} (hC : 4 ≤ C) (hΓ : 4 ≤ Γ)
    (hM : Γ ≤ M) (hB : 1 ≤ B) (hbudget : B * Γ * Nat.clog 2 (4 * C * M) ≤ M)
    (N : ℕ) :
    (∑ j ∈ range (Γ * N / M + 1), ((C * N).choose j : ℝ)) ≤ (2 : ℝ) ^ ((N : ℝ) / B) := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hΓ0 : (0 : ℝ) < Γ := by exact_mod_cast (show 0 < Γ by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  let T : ℝ := C * M / Γ
  let a : ℝ := Γ * N / M
  let h := Nat.clog 2 (4 * C * M)
  have hT : 1 ≤ T := by
    apply (le_div_iff₀ hΓ0).mpr
    have hCM : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
    have hΓM : (Γ : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hradius : ((Γ * N / M : ℕ) : ℝ) ≤ a := by
    apply (le_div_iff₀ hM0).mpr
    exact_mod_cast Nat.div_mul_le_self (Γ * N) M
  have hratio : ((C * N : ℕ) : ℝ) / T = a := by
    dsimp only [T, a]
    push_cast
    field_simp
  have hexp : Real.exp 1 ≤ (Γ : ℝ) :=
    Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ Γ by omega))
  have hbase : Real.exp 1 * T ≤ (4 * C * M : ℕ) := by
    calc Real.exp 1 * T ≤ Γ * T := mul_le_mul_of_nonneg_right hexp hT0.le
      _ = C * M := by dsimp only [T]; field_simp
      _ ≤ (4 * C * M : ℕ) := by push_cast; nlinarith
  have hpow : ((4 * C * M : ℕ) : ℝ) ≤ (2 : ℝ) ^ h := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (4 * C * M)
  have hexponent : (h : ℝ) * a ≤ (N : ℝ) / B := by
    have hb : (B : ℝ) * Γ * h ≤ M := by exact_mod_cast hbudget
    dsimp only [a]
    rw [← mul_div_assoc, div_le_div_iff₀ hM0 hB0]
    nlinarith [mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg N)]
  calc (∑ j ∈ range (Γ * N / M + 1), ((C * N).choose j : ℝ))
      ≤ Real.exp (((C * N : ℕ) : ℝ) / T) * T ^ (Γ * N / M) :=
        sum_choose_le_exp_mul_pow (C * N) (Γ * N / M) T hT
    _ = Real.exp a * T ^ (Γ * N / M) := by rw [hratio]
    _ ≤ Real.exp a * T ^ a := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos a).le
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hT hradius
    _ = (Real.exp 1 * T) ^ a := by
      rw [Real.mul_rpow (Real.exp_pos 1).le hT0.le, ← Real.exp_mul, one_mul]
    _ ≤ ((4 * C * M : ℕ) : ℝ) ^ a :=
      Real.rpow_le_rpow (by positivity) hbase ha
    _ ≤ ((2 : ℝ) ^ h) ^ a := Real.rpow_le_rpow (by positivity) hpow ha
    _ = (2 : ℝ) ^ ((h : ℝ) * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    _ ≤ (2 : ℝ) ^ ((N : ℝ) / B) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- The natural-number rounding of `sum_choose_le_two_rpow_div`, suitable for a discrete
leaf-count or round budget. The division in the conclusion is natural-number division. -/
theorem sum_choose_le_two_pow_div_add_one {C Γ M B : ℕ} (hC : 4 ≤ C) (hΓ : 4 ≤ Γ)
    (hM : Γ ≤ M) (hB : 1 ≤ B) (hbudget : B * Γ * Nat.clog 2 (4 * C * M) ≤ M)
    (N : ℕ) :
    ∑ j ∈ range (Γ * N / M + 1), (C * N).choose j ≤ 2 ^ (N / B + 1) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hround : (N : ℝ) / B ≤ ((N / B + 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ hB0).mpr
    have hn : N < B * (N / B + 1) := by
      have := Nat.mod_lt N (show 0 < B by omega)
      have := Nat.div_add_mod N B
      nlinarith
    exact_mod_cast (show N ≤ (N / B + 1) * B by simpa only [Nat.mul_comm] using hn.le)
  have h := (sum_choose_le_two_rpow_div hC hΓ hM hB hbudget N).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hround)
  rw [Real.rpow_natCast] at h
  exact_mod_cast h

/-- If the square of the radius-`e` binomial sum is at least `2 ^ m`, then
`m / 2 ≤ e * log₂ (exp 1 * q / e)`. The statement includes `e = 0`, which forces `m = 0`. -/
theorem le_mul_logb_of_two_pow_le_sum_choose_sq {m q e : ℕ} (heq : e ≤ q)
    (h : 2 ^ m ≤ (∑ j ∈ range (e + 1), q.choose j) ^ 2) :
    (m : ℝ) / 2 ≤ e * Real.logb 2 (Real.exp 1 * q / e) := by
  have hreal : (2 : ℝ) ^ m ≤ (∑ j ∈ range (e + 1), (q.choose j : ℝ)) ^ 2 := by
    exact_mod_cast h
  have hs : 0 ≤ ∑ j ∈ range (e + 1), (q.choose j : ℝ) := sum_nonneg fun _ _ => by positivity
  have hpow := hreal.trans (pow_le_pow_left₀ hs
    (sum_choose_le_exp_one_mul_div_pow heq) 2)
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (by positivity : (0 : ℝ) < 2 ^ m) hpow
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    Nat.cast_ofNat, mul_one] at hlog
  linarith

/-- The logarithmic partial-binomial-sum bound rearranged as a lower bound on `q`.
At radius zero the lower bound is zero. -/
theorem mul_rpow_le_of_two_pow_le_sum_choose_sq {m q e : ℕ} (heq : e ≤ q)
    (h : 2 ^ m ≤ (∑ j ∈ range (e + 1), q.choose j) ^ 2) :
    e / Real.exp 1 * (2 : ℝ) ^ ((m : ℝ) / (2 * e)) ≤ q := by
  by_cases he : e = 0
  · simp [he]
  have he0 : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le he0 (by exact_mod_cast heq)
  have hlog := le_mul_logb_of_two_pow_le_sum_choose_sq heq h
  have hx : (m : ℝ) / (2 * e) ≤ Real.logb 2 (Real.exp 1 * q / e) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * e)).mpr
    linarith
  have hp := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).mp hx
  calc e / Real.exp 1 * (2 : ℝ) ^ ((m : ℝ) / (2 * e))
      ≤ e / Real.exp 1 * (Real.exp 1 * q / e) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = q := by field_simp

end Cslib

namespace Real

open Filter

/-- A polynomial is eventually below an exponential with base `r > 1`. -/
theorem exists_one_le_and_mul_pow_le_pow (C : ℝ) (d : ℕ) {r : ℝ} (hr : 1 < r) :
    ∃ α : ℕ, 1 ≤ α ∧ C * (α : ℝ) ^ d ≤ r ^ α := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt d hr
  have hC : 0 < |C| + 1 := by positivity
  have hev := (hlim.eventually (gt_mem_nhds (inv_pos.mpr hC))).and (eventually_ge_atTop 1)
  obtain ⟨α, hα, hα1⟩ := hev.exists
  refine ⟨α, hα1, ?_⟩
  have hrα : 0 < r ^ α := pow_pos (by linarith) α
  rw [div_lt_iff₀ hrα] at hα
  have hpow : 0 ≤ (α : ℝ) ^ d := by positivity
  calc C * (α : ℝ) ^ d ≤ (|C| + 1) * (α : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hpow
    _ ≤ (|C| + 1) * ((|C| + 1)⁻¹ * r ^ α) := mul_le_mul_of_nonneg_left hα.le hC.le
    _ = r ^ α := by field_simp

end Real
