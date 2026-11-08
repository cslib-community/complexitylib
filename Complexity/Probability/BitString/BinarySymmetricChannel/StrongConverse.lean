/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.BitString.BinarySymmetricChannel
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Filter.AtTopBot.Defs
import Complexity.Foundations.Combinatorics.BinomialTail
import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Shannon's coding theorem for the binary symmetric channel: the strong converse

Above the capacity `1 - h₂(p)` of the binary symmetric channel `BSC_p`, where
`h₂(p) = Real.binEntropy p / Real.log 2` is the binary entropy in bits, the error probability of
every code tends to `1` exponentially fast: the **strong converse** of Shannon's noisy-channel
coding theorem for `BSC_p` [Guruswami, Rudra and Sudan, Theorem 6.3.1(2) and Remark
6.3.2][GuruswamiRudraSudan2019], due to Wolfowitz for discrete memoryless channels. The weak
converse (`Complexity.Probability.BitString.BinarySymmetricChannel.Converse`) only bounds the error
away from `0`.

The proof is the packing argument of [Guruswami, Rudra and Sudan, Section 6.3.1]
[GuruswamiRudraSudan2019], applied to the average error. For `p ≤ 1 / 2`, a noise pattern with at
least `a` flipped bits has probability at most `p ^ a (1 - p) ^ (n - a)`, and the decoding regions
`{y | D y = m}` partition the `2 ^ n` received words. So the average success probability of a code
with `|M|` messages is at most `T + 2 ^ n p ^ a (1 - p) ^ (n - a) / |M|`, where `T` is the
probability that fewer than `a` bits flip (`Cslib.BitString.one_sub_expect_decodingError_le`). With
`a = ⌈(p - γ) n⌉₊`, Hoeffding's inequality bounds `T` by `exp (-2 γ ^ 2 n)`, and
`p ^ a (1 - p) ^ (n - a) ≤ exp (-n (H(p) - γ log ((1 - p) / p)))` with `H(p)` in nats; for small
`γ > 0` both terms are exponentially small when `|M| ≥ 2 ^ (R n)` with `R > 1 - h₂(p)`. Crossover
probabilities `p > 1 / 2` reduce to `1 - p` by complementing the received word
(`Cslib.BitString.decodingError_symm`).

The source states the result for `0 ≤ p < 1 / 2` and the *maximal* error: some message is misdecoded
with probability more than `1 / 2`, or more than `1 - 2 ^ (-β n)` (Remark 6.3.2). The theorems here
bound the *average* error by `1 - 2 exp (-δ n)` for every `p ∈ [0, 1]` and every `n`, which implies
the maximal-error form. Unlike the source, they need the rate to be strictly above capacity: the
source's case `ε = 0`, a rate of exactly `1 - h₂(p)`, is not covered. Together with
`Cslib.BitString.eventually_exists_code_decodingError_le` they determine the capacity of `BSC_p`
(`Complexity.Probability.BitString.BinarySymmetricChannel.Capacity`). General discrete memoryless
channels and channels with feedback are not formalized here.

## Main results

* `Cslib.BitString.one_sub_expect_decodingError_le`: the packing bound on the average success
  probability.
* `Cslib.BitString.exists_pos_one_sub_two_mul_exp_le_expect_decodingError`: the strong converse,
  with average error at least `1 - 2 exp (-δ n)` for every length.
* `Cslib.BitString.eventually_one_sub_le_expect_decodingError`: the asymptotic form.
* `Cslib.BitString.eventually_exists_lt_decodingError`: the source's form, with some message
  misdecoded with probability more than any fixed `ε < 1`.

## References

* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019], draft of
  26 August 2025
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators unitInterval

variable {ι : Type*} [Fintype ι] {M : Type*}

/-! ### The packing bound -/

/-- The likelihood `p ^ k (1 - p) ^ (n - k)` of a fixed noise pattern of weight `k` decreases in `k`
for `p ≤ 1 / 2`. -/
private theorem pow_mul_pow_sub_anti {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) {n a k : ℕ}
    (hak : a ≤ k) (hkn : k ≤ n) : p ^ k * (1 - p) ^ (n - k) ≤ p ^ a * (1 - p) ^ (n - a) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hak
  have hpq : p ≤ 1 - p := by linarith
  have hq0 : 0 ≤ 1 - p := by linarith
  rw [show n - a = j + (n - (a + j)) by omega, pow_add, pow_add]
  calc p ^ a * p ^ j * (1 - p) ^ (n - (a + j))
      ≤ p ^ a * (1 - p) ^ j * (1 - p) ^ (n - (a + j)) := by gcongr
    _ = _ := by ring

/-- **The packing bound** behind the strong converse for `BSC_p`, `p ≤ 1 / 2`: for every code
`E : M → (ι → Bool)` with `|M|` messages, every decoder `D` and every `a : ℕ`, the average success
probability is at most `T + 2 ^ n p ^ a (1 - p) ^ (n - a) / |M|`, where `n = |ι|` and
`T = ∑_{k < a} C(n, k) p ^ k (1 - p) ^ (n - k)` is the probability that fewer than `a` bits flip.
A noise pattern of weight at least `a` has probability at most `p ^ a (1 - p) ^ (n - a)`, and the
decoding regions `{y | D y = m}` partition the `2 ^ n` received words. -/
theorem one_sub_expect_decodingError_le [Fintype M] [Nonempty M] (p : I) (hp : (p : ℝ) ≤ 1 / 2)
    (E : M → ι → Bool) (D : (ι → Bool) → M) (a : ℕ) :
    1 - 𝔼 m, decodingError p E D m ≤
      ∑ k ∈ range (Fintype.card ι + 1) with k < a,
          ((Fintype.card ι).choose k : ℝ) * p ^ k * (1 - p) ^ (Fintype.card ι - k) +
        2 ^ Fintype.card ι * ((p : ℝ) ^ a * (1 - p) ^ (Fintype.card ι - a)) / Fintype.card M := by
  classical
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hq0 : (0 : ℝ) ≤ 1 - p := sub_nonneg.mpr hp1
  set n := Fintype.card ι with hn
  set T := ∑ k ∈ range (n + 1) with k < a, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) with hT
  set q : ℝ := (p : ℝ) ^ a * (1 - p) ^ (n - a) with hq
  have hT' : T = bernoulliAverage p (fun e : ι → Bool => if weight e < a then 1 else 0) := by
    rw [hT, sum_filter]
    exact (sum_congr rfl fun k _ => by split_ifs <;> ring).trans
      (bernoulliAverage_comp_weight p fun k => if k < a then 1 else 0).symm
  -- the success probability at each message
  have hsucc (m : M) : 1 - decodingError p E D m =
      ∑ e, bernoulliWeight p e * (if D (E m + e) = m then 1 else 0) := by
    have hw1 : ∑ e : ι → Bool, bernoulliWeight p e = 1 := by
      simpa [bernoulliAverage] using bernoulliAverage_const (ι := ι) p 1
    have hsplit : ∑ e, bernoulliWeight p e * (if D (E m + e) = m then (1 : ℝ) else 0) +
        ∑ e, bernoulliWeight p e * (if D (E m + e) ≠ m then (1 : ℝ) else 0) =
          ∑ e : ι → Bool, bernoulliWeight p e := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun e _ => ?_
      by_cases h : D (E m + e) = m <;> simp [h]
    rw [decodingError_eq_bernoulliAverage, bernoulliAverage]
    linarith
  -- pointwise split by the weight of the noise
  have hpt (m : M) (e : ι → Bool) :
      bernoulliWeight p e * (if D (E m + e) = m then 1 else 0) ≤
        bernoulliWeight p e * (if weight e < a then 1 else 0) +
          q * (if D (E m + e) = m then 1 else 0) := by
    have hw0 : 0 ≤ bernoulliWeight p e := by
      rw [bernoulliWeight_eq_pow_mul_pow]
      positivity
    by_cases hD : D (E m + e) = m
    · by_cases hw : weight e < a
      · simp only [hD, hw, ite_true, mul_one]
        have : 0 ≤ q := by rw [hq]; positivity
        linarith
      · simp only [hD, hw, ite_true, ite_false, mul_one, mul_zero, zero_add]
        rw [bernoulliWeight_eq_pow_mul_pow, hq]
        exact pow_mul_pow_sub_anti hp0 hp (not_lt.mp hw) (weight_le e)
    · simp only [hD, ite_false, mul_zero, add_zero]
      split_ifs <;> simp [hw0]
  -- the decoding regions partition the received words
  have hcount : ∑ m, ∑ e : ι → Bool, (if D (E m + e) = m then (1 : ℝ) else 0) = 2 ^ n := by
    have h1 (m : M) : ∑ e : ι → Bool, (if D (E m + e) = m then (1 : ℝ) else 0) =
        ∑ y : ι → Bool, (if D y = m then (1 : ℝ) else 0) :=
      Fintype.sum_equiv (Equiv.addLeft (E m)) _ _ fun e => rfl
    simp_rw [h1]
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, Fintype.card_fun,
      Fintype.card_bool, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat, ← hn]
  -- sum over the messages
  have hsum : ∑ m, (1 - decodingError p E D m) ≤ Fintype.card M * T + q * 2 ^ n := by
    calc ∑ m, (1 - decodingError p E D m)
        = ∑ m, ∑ e, bernoulliWeight p e * (if D (E m + e) = m then 1 else 0) :=
          sum_congr rfl fun m _ => hsucc m
      _ ≤ ∑ m, ∑ e, (bernoulliWeight p e * (if weight e < a then 1 else 0) +
            q * (if D (E m + e) = m then 1 else 0)) :=
          sum_le_sum fun m _ => sum_le_sum fun e _ => hpt m e
      _ = ∑ _m : M, T + q * ∑ m, ∑ e : ι → Bool, (if D (E m + e) = m then (1 : ℝ) else 0) := by
          simp only [sum_add_distrib, mul_sum]
          congr 1
          refine sum_congr rfl fun m _ => ?_
          rw [hT', bernoulliAverage]
      _ = Fintype.card M * T + q * 2 ^ n := by
          rw [hcount, sum_const, card_univ, nsmul_eq_mul]
  have hM : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
  have hexp : 1 - 𝔼 m, decodingError p E D m = (∑ m, (1 - decodingError p E D m)) /
      Fintype.card M := by
    rw [Fintype.expect_eq_sum_div_card, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
      mul_one, sub_div, div_self hM.ne']
  rw [hexp, div_le_iff₀ hM, add_mul, div_mul_cancel₀ _ hM.ne']
  linarith

/-! ### The exponent -/

/-- The likelihood of a noise pattern of weight `a = ⌈(p - γ) n⌉₊` is at most
`exp (-n (H(p) - γ L))`, where `H(p) = Real.binEntropy p` is in nats and
`L = log (1 - p) - log p ≥ 0`. -/
private theorem pow_mul_pow_ceil_le {p γ : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hγ : 0 ≤ γ) (n : ℕ) :
    p ^ ⌈(p - γ) * n⌉₊ * (1 - p) ^ (n - ⌈(p - γ) * n⌉₊) ≤
      Real.exp (-(n * (Real.binEntropy p - γ * (Real.log (1 - p) - Real.log p)))) := by
  rcases eq_or_lt_of_le hp0 with rfl | hpos
  · have h0 : ⌈(0 - γ) * n⌉₊ = 0 :=
      Nat.ceil_eq_zero.mpr (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    rw [h0]
    simp
  set a := ⌈(p - γ) * n⌉₊ with ha
  have hq : 0 < 1 - p := by linarith
  have hlog : Real.log p ≤ Real.log (1 - p) := Real.log_le_log hpos (by linarith)
  have han : a ≤ n := Nat.ceil_le.mpr (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hpa : (p - γ) * n ≤ a := Nat.le_ceil _
  have hpow : p ^ a * (1 - p) ^ (n - a) =
      Real.exp (a * Real.log p + ((n : ℝ) - a) * Real.log (1 - p)) := by
    rw [Real.exp_add, ← Real.log_pow, ← Nat.cast_sub han, ← Real.log_pow,
      Real.exp_log (pow_pos hpos _), Real.exp_log (pow_pos hq _)]
  rw [hpow, Real.exp_le_exp, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog,
    Real.negMulLog]
  nlinarith [mul_le_mul_of_nonneg_right hpa (sub_nonneg.mpr hlog)]

/-- Fewer than `⌈(p - γ) n⌉₊` of the `n` bits flip with probability at most `exp (-2 γ ^ 2 n)`, by
Hoeffding's inequality. -/
private theorem sum_filter_lt_ceil_le {p γ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hγ : 0 ≤ γ) (n : ℕ) :
    ∑ k ∈ range (n + 1) with k < ⌈(p - γ) * n⌉₊, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤
      Real.exp (-(2 * γ ^ 2 * n)) := by
  have hq0 : 0 ≤ 1 - p := by linarith
  refine (sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => by positivity).trans
    ((sum_filter_le_mul_sub_choose_mul_pow_le n hp0 hp1
      (mul_nonneg hγ n.cast_nonneg)).trans_eq ?_)
  · obtain ⟨hk, hka⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hk, ?_⟩
    have : (k : ℝ) < (p - γ) * n := Nat.lt_ceil.mp hka
    linarith
  · rcases eq_or_ne (n : ℝ) 0 with hn | hn
    · rw [hn]
      simp
    · congr 1
      rw [div_eq_iff hn]
      ring

/-! ### The strong converse -/

/-- For `p ≤ 1 / 2` and `R` above capacity, the packing bound is exponentially small: there is
`δ > 0` such that for every length `n` and every `K ≥ 2 ^ (R n)` some cutoff `a` makes
`T + 2 ^ n p ^ a (1 - p) ^ (n - a) / K ≤ 2 exp (-δ n)`. -/
private theorem exists_pos_bound (p : I) (hp : (p : ℝ) ≤ 1 / 2) {R : ℝ}
    (hR : 1 - Real.binEntropy p / Real.log 2 < R) :
    ∃ δ > 0, ∀ (n : ℕ) (K : ℝ), 0 < K → R * n ≤ Real.logb 2 K → ∃ a : ℕ,
      ∑ k ∈ range (n + 1) with k < a, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) +
        2 ^ n * ((p : ℝ) ^ a * (1 - p) ^ (n - a)) / K ≤ 2 * Real.exp (-(δ * n)) := by
  have hL2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  obtain ⟨L, hL, hL0⟩ : ∃ L, L = Real.log (1 - p) - Real.log p ∧ 0 ≤ L := by
    refine ⟨_, rfl, ?_⟩
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h, sub_zero, Real.log_one, Real.log_zero, sub_zero]
    · exact sub_nonneg.mpr (Real.log_le_log h (by linarith))
  obtain ⟨g, hg, hg0⟩ : ∃ g, g = R * Real.log 2 - Real.log 2 + Real.binEntropy p ∧ 0 < g := by
    refine ⟨_, rfl, ?_⟩
    have h := mul_lt_mul_of_pos_right hR hL2
    rw [sub_mul, div_mul_cancel₀ _ hL2.ne', one_mul] at h
    linarith
  obtain ⟨γ, hγ, hγ0⟩ : ∃ γ, γ = g / (2 * (L + 1)) ∧ 0 < γ :=
    ⟨_, rfl, div_pos hg0 (by linarith)⟩
  have hγL : γ * L ≤ g / 2 := by
    rw [hγ, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) two_pos]
    nlinarith
  refine ⟨min (2 * γ ^ 2) (g / 2), lt_min (by positivity) (by linarith), fun n K hK hRK => ?_⟩
  refine ⟨⌈((p : ℝ) - γ) * n⌉₊, ?_⟩
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hT := sum_filter_lt_ceil_le hp0 hp1 hγ0.le n
  have hq := pow_mul_pow_ceil_le hp0 hp hγ0.le n
  rw [← hL] at hq
  -- `2 ^ (R n) ≤ K`
  have hK' : Real.exp (R * n * Real.log 2) ≤ K := by
    rw [Real.logb, le_div_iff₀ hL2] at hRK
    calc Real.exp (R * n * Real.log 2) ≤ Real.exp (Real.log K) := Real.exp_le_exp.mpr hRK
      _ = K := Real.exp_log hK
  have h2n : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hngL : n * (γ * L) ≤ n * (g / 2) := mul_le_mul_of_nonneg_left hγL hn
  have hsecond : 2 ^ n * ((p : ℝ) ^ ⌈((p : ℝ) - γ) * n⌉₊ * (1 - p) ^ (n - ⌈((p : ℝ) - γ) * n⌉₊)) /
      K ≤ Real.exp (-(g / 2 * n)) := by
    rw [div_le_iff₀ hK, h2n]
    calc Real.exp (n * Real.log 2) *
          ((p : ℝ) ^ ⌈((p : ℝ) - γ) * n⌉₊ * (1 - p) ^ (n - ⌈((p : ℝ) - γ) * n⌉₊))
        ≤ Real.exp (n * Real.log 2) * Real.exp (-(n * (Real.binEntropy p - γ * L))) := by
          gcongr
      _ = Real.exp (n * Real.log 2 - n * (Real.binEntropy p - γ * L)) := by
          rw [← Real.exp_add, ← sub_eq_add_neg]
      _ ≤ Real.exp (-(g / 2 * n) + R * n * Real.log 2) := by
          rw [Real.exp_le_exp, hg]
          nlinarith
      _ = Real.exp (-(g / 2 * n)) * Real.exp (R * n * Real.log 2) := Real.exp_add _ _
      _ ≤ Real.exp (-(g / 2 * n)) * K := by gcongr
  have hd1 : Real.exp (-(2 * γ ^ 2 * n)) ≤ Real.exp (-(min (2 * γ ^ 2) (g / 2) * n)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hn))
  have hd2 : Real.exp (-(g / 2 * n)) ≤ Real.exp (-(min (2 * γ ^ 2) (g / 2) * n)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hn))
  linarith

/-- **The strong converse of Shannon's noisy-channel coding theorem for the binary symmetric
channel**, with an exponential rate: for every `p ∈ [0, 1]` and every rate `R` above the capacity
`1 - h₂(p)`, there is `δ > 0` such that every code `E : M → (ι → Bool)` with
`log₂ |M| ≥ R n` messages of length `n = |ι|` has average error probability at least
`1 - 2 exp (-δ n)`, for every decoder `D` and every `n`.

This strengthens [Guruswami, Rudra and Sudan, Theorem 6.3.1(2) and Remark
6.3.2][GuruswamiRudraSudan2019], which take `0 ≤ p < 1 / 2` and bound the *maximal* error
below by `1 - 2 ^ (-β n)` for large `n`: here the *average* error is bounded, for every crossover
probability. -/
theorem exists_pos_one_sub_two_mul_exp_le_expect_decodingError (p : I) {R : ℝ}
    (hR : 1 - Real.binEntropy p / Real.log 2 < R) :
    ∃ δ > 0, ∀ {ι : Type*} [Fintype ι] {M : Type*} [Fintype M] [Nonempty M]
      (E : M → ι → Bool) (D : (ι → Bool) → M),
      R * Fintype.card ι ≤ Real.logb 2 (Fintype.card M) →
        1 - 2 * Real.exp (-(δ * Fintype.card ι)) ≤ 𝔼 m, decodingError p E D m := by
  rcases le_or_gt (p : ℝ) (1 / 2) with hp | hp
  · obtain ⟨δ, hδ, h⟩ := exists_pos_bound p hp hR
    refine ⟨δ, hδ, fun {ι} _ {M} _ _ E D hM => ?_⟩
    have hK : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
    obtain ⟨a, ha⟩ := h (Fintype.card ι) (Fintype.card M) hK hM
    have := one_sub_expect_decodingError_le p hp E D a
    linarith
  · have hσ : ((σ p : I) : ℝ) ≤ 1 / 2 := by
      rw [unitInterval.coe_symm_eq]
      linarith
    have hRσ : 1 - Real.binEntropy (σ p : I) / Real.log 2 < R := by
      rwa [unitInterval.coe_symm_eq, Real.binEntropy_one_sub]
    obtain ⟨δ, hδ, h⟩ := exists_pos_bound (σ p) hσ hRσ
    refine ⟨δ, hδ, fun {ι} _ {M} _ _ E D hM => ?_⟩
    have hK : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
    obtain ⟨a, ha⟩ := h (Fintype.card ι) (Fintype.card M) hK hM
    have := one_sub_expect_decodingError_le (σ p) hσ E (fun y => D fun i => !y i) a
    simp only [decodingError_symm] at this
    linarith

open Filter in
/-- **The strong converse for `BSC_p`**, asymptotic form: for every `p ∈ [0, 1]`, every rate
`R > 1 - h₂(p)` and every `ε > 0`, for all sufficiently large `n` every code with at least
`2 ^ (R n)` messages of length `n` has average error probability at least `1 - ε`, for every
decoder. -/
theorem eventually_one_sub_le_expect_decodingError (p : I) {R : ℝ}
    (hR : 1 - Real.binEntropy p / Real.log 2 < R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ {M : Type*} [Fintype M] [Nonempty M] (E : M → BitString n)
      (D : BitString n → M), R * n ≤ Real.logb 2 (Fintype.card M) →
        1 - ε ≤ 𝔼 m, decodingError p E D m := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_one_sub_two_mul_exp_le_expect_decodingError p hR
  have hlim : Tendsto (fun n : ℕ => 2 * Real.exp (-(δ * n))) atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hδ)).const_mul 2
  filter_upwards [hlim.eventually (eventually_le_nhds hε)] with n hn M _ _ E D hM
  have := h E D (by rwa [Fintype.card_fin])
  rw [Fintype.card_fin] at this
  linarith

open Filter in
/-- **The strong converse for `BSC_p`** in the form of
[Guruswami, Rudra and Sudan, Theorem 6.3.1(2)][GuruswamiRudraSudan2019]: if `R > 1 - h₂(p)`,
then for all sufficiently large `n`, every encoder `E : {0, 1} ^ k → {0, 1} ^ n` with
`k ≥ R n` and every decoder `D` misdecode some message `m` with probability greater than `ε`, for
any fixed `ε < 1`. The source has `ε = 1 / 2` and `0 ≤ p < 1 / 2`, and also allows `R = 1 - h₂(p)`
(its `ε = 0`), which is not covered here. -/
theorem eventually_exists_lt_decodingError (p : I) {R : ℝ}
    (hR : 1 - Real.binEntropy p / Real.log 2 < R) {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (k : ℕ), R * n ≤ k → ∀ (E : BitString k → BitString n)
      (D : BitString n → BitString k), ∃ m, ε < decodingError p E D m := by
  filter_upwards [eventually_one_sub_le_expect_decodingError p hR (ε := (1 - ε) / 2)
    (by linarith)] with n hn k hk E D
  have hM : R * n ≤ Real.logb 2 (Fintype.card (BitString k)) := by
    rwa [BitString.card, Nat.cast_pow, Nat.cast_two, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one]
  have h := hn E D hM
  obtain ⟨m, -, hm⟩ := exists_lt_of_lt_expect univ_nonempty (show ε < 𝔼 m, decodingError p E D m
    by linarith)
  exact ⟨m, hm⟩

end Cslib.BitString
