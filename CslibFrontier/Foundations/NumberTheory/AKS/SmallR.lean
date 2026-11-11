/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# A small modulus of large order

The AKS algorithm needs a modulus `r` of size polynomial in `log n` such that the multiplicative
order of `n` modulo `r` exceeds `log₂² n`. With `c = ⌈log₂ n⌉`, some `r ≤ 4 c⁵` has order above
`c²` (`Cslib.AKS.exists_lt_orderOf`), so `r ≤ 128 log₂⁵ n` and the order exceeds `log₂² n`
(`Cslib.AKS.exists_lt_orderOf_logb`). This is [Agrawal, Kayal, Saxena, Lemma 4.3][AKS2004] up to
the constant: they prove `r ≤ max(3, ⌈log₂⁵ n⌉)` using Nair's bound `lcm(1, …, m) ≥ 2^m`, while this
file uses the weaker bound `C(2m, m) ≥ 4^m / (2m + 1)` for numbers divisible by `1, …, 2m`
(`Cslib.AKS.centralBinom_dvd_of_forall_dvd`).

The proof takes the least `s` not dividing `X = n^K ∏_{i = 1}^{c²} (n^i - 1)`, where
`K = ⌊log₂ (4c⁵)⌋`; it exists since `C(4c⁵, 2c⁵) > X`. Such an `s` is coprime to `n`: a prime
`p ∣ gcd(s, n)` would give `s = p^v s'` with `p^v ∣ n^K` and `s' < s`, so `s ∣ X`. If the order `o`
of `n` modulo `s` were at most `c²`, then `s ∣ n^o - 1 ∣ X`. The published proof passes from `s`
to `s / gcd(s, n)`; here the factor `n^K` in `X` and the minimality of `s` give coprimality
directly.

## Main results

* `Cslib.AKS.centralBinom_dvd_of_forall_dvd`: `C(2m, m)` divides every number divisible by
  `1, …, 2m`.
* `Cslib.AKS.exists_lt_orderOf`: some `r ≤ 4 ⌈log₂ n⌉⁵` has `ord_r(n) > ⌈log₂ n⌉²`.
* `Cslib.AKS.exists_lt_orderOf_logb`: some `r ≤ 128 log₂⁵ n` has `ord_r(n) > log₂² n`.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.AKS

open Finset

/-- **The central binomial coefficient divides every common multiple of `1, …, 2m`**: each prime
power `p^v` exactly dividing `C(2m, m)` is at most `2m`. -/
theorem centralBinom_dvd_of_forall_dvd {m X : ℕ} (hX : X ≠ 0)
    (h : ∀ s, 1 ≤ s → s ≤ 2 * m → s ∣ X) : m.centralBinom ∣ X := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [Nat.centralBinom_eq_two_mul_choose,
    ← Nat.factorization_le_iff_dvd (Nat.choose_pos (by omega)).ne' hX]
  intro p
  by_cases hp : p.Prime
  · rw [← hp.pow_dvd_iff_le_factorization hX]
    exact h _ (Nat.one_le_pow _ _ hp.pos) (Nat.pow_factorization_choose_le (by omega))
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The exponent arithmetic of the size bound: `3 + 7c + 5c² + c⁵ < 4c⁵` for `c ≥ 2`. -/
private theorem exponent_lt {c : ℕ} (hc : 2 ≤ c) : 3 + 7 * c + 5 * c ^ 2 + c ^ 5 < 4 * c ^ 5 := by
  have h2 : 4 ≤ c ^ 2 := by nlinarith
  have h3 : 2 * c ^ 2 ≤ c ^ 3 := by nlinarith
  have h5 : 4 * c ^ 3 ≤ c ^ 5 := by nlinarith
  nlinarith

/-- **A small modulus of large order**: for `n ≥ 2` and `c = ⌈log₂ n⌉`, some `2 ≤ r ≤ 4 c⁵` has
`ord_r(n) > c²` [Agrawal, Kayal, Saxena, Lemma 4.3][AKS2004], up to the constant. -/
theorem exists_lt_orderOf {n : ℕ} (hn : 2 ≤ n) :
    ∃ r, 2 ≤ r ∧ r ≤ 4 * Nat.clog 2 n ^ 5 ∧ Nat.clog 2 n ^ 2 < orderOf (n : ZMod r) := by
  classical
  set c := Nat.clog 2 n
  have hc1 : 1 ≤ c := Nat.clog_pos one_lt_two (by omega)
  have hnc : n ≤ 2 ^ c := Nat.le_pow_clog one_lt_two n
  rcases (show c = 1 ∨ 2 ≤ c by omega) with hc | hc
  · -- `n = 2`: take `r = 3`.
    have hn2 : n = 2 := by rw [hc, pow_one] at hnc; omega
    have h3 : orderOf ((2 : ℕ) : ZMod 3) = 2 := by
      rw [orderOf_eq_iff (by norm_num)]
      exact ⟨by decide, fun m hm hm0 => by interval_cases m; decide⟩
    refine ⟨3, by norm_num, by rw [hc]; norm_num, ?_⟩
    rw [hc, hn2, h3]
    norm_num
  set L := c ^ 2
  set M := 4 * c ^ 5
  set K := Nat.log 2 M
  set N := ∏ i ∈ Icc 1 L, (n ^ i - 1)
  set X := n ^ K * N
  have hfac : ∀ i ∈ Icc 1 L, 1 ≤ n ^ i - 1 := by
    intro i hi
    have : 2 ≤ n ^ i := le_trans hn (Nat.le_self_pow (by simp at hi; omega) n)
    omega
  have hN : N ≠ 0 := prod_ne_zero_iff.mpr fun i hi => by have := hfac i hi; omega
  have hX : X ≠ 0 := mul_ne_zero (pow_ne_zero _ (by omega)) hN
  -- Some `s ≤ M` does not divide `X`.
  have hex : ∃ s, 1 ≤ s ∧ s ≤ M ∧ ¬ s ∣ X := by
    by_contra hall
    push Not at hall
    have hdvd : (2 * c ^ 5).centralBinom ∣ X :=
      centralBinom_dvd_of_forall_dvd (m := 2 * c ^ 5) hX fun s hs hsM => hall s hs (by omega)
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hX) hdvd
    have hcb := Nat.four_pow_le_two_mul_add_one_mul_centralBinom (2 * c ^ 5)
    -- Size bounds.
    have hcpow : c ^ 5 < 2 ^ (5 * c) := by
      rw [pow_mul']
      exact Nat.pow_lt_pow_left (Nat.lt_two_pow_self) (by norm_num)
    have hK : K < 2 + 5 * c := by
      apply Nat.log_lt_of_lt_pow (by positivity)
      rw [pow_add]
      omega
    have hNle : N ≤ n ^ (c ^ 4) := by
      calc
        N ≤ ∏ _i ∈ Icc 1 L, n ^ L :=
          prod_le_prod fun i hi => (Nat.sub_le _ _).trans
            (Nat.pow_le_pow_right (by omega) (by simp at hi; omega))
        _ = n ^ (c ^ 4) := by
          rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul]
          congr 1
          ring
    have hXle : X ≤ 2 ^ (c * (2 + 5 * c) + c ^ 5) := by
      calc
        X ≤ n ^ (2 + 5 * c) * n ^ (c ^ 4) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hK.le) hNle
        _ ≤ (2 ^ c) ^ (2 + 5 * c) * (2 ^ c) ^ (c ^ 4) := by gcongr
        _ = 2 ^ (c * (2 + 5 * c) + c ^ 5) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
    have hcoef : 2 * (2 * c ^ 5) + 1 ≤ 2 ^ (3 + 5 * c) := by
      rw [pow_add]
      omega
    have hfour : 4 ^ (2 * c ^ 5) = 2 ^ (4 * c ^ 5) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    have hchain : 4 ^ (2 * c ^ 5) ≤ 2 ^ (3 + 5 * c) * 2 ^ (c * (2 + 5 * c) + c ^ 5) :=
      hcb.trans (Nat.mul_le_mul hcoef (hle.trans hXle))
    rw [hfour, ← pow_add] at hchain
    have := Nat.pow_le_pow_iff_right (by norm_num : 1 < 2) |>.mp hchain
    have := exponent_lt hc
    nlinarith
  -- Take the least such `s`.
  have hex' : ∃ s, 1 ≤ s ∧ ¬ s ∣ X := let ⟨s, hs, _, hsX⟩ := hex; ⟨s, hs, hsX⟩
  set s := Nat.find hex'
  have hs : 1 ≤ s ∧ ¬ s ∣ X := Nat.find_spec hex'
  have hsM : s ≤ M := by
    obtain ⟨s₀, hs₀, hs₀M, hs₀X⟩ := hex
    exact (Nat.find_min' hex' ⟨hs₀, hs₀X⟩).trans hs₀M
  have hmin : ∀ s', 1 ≤ s' → s' < s → s' ∣ X := fun s' hs' hlt => by
    by_contra h
    exact Nat.find_min hex' hlt ⟨hs', h⟩
  have hs2 : 2 ≤ s := by
    by_contra h
    have h1 : s = 1 := by omega
    rw [h1] at hs
    exact hs.2 (one_dvd X)
  -- `s` is coprime to `n`.
  have hcop : s.Coprime n := by
    by_contra hnc
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hnc
    have hps : p ∣ s := hpg.trans (Nat.gcd_dvd_left s n)
    have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_right s n)
    set v := s.factorization p
    have hs0 : s ≠ 0 := by omega
    have hv : 1 ≤ v := (hp.dvd_iff_one_le_factorization hs0).mp hps
    have hsplit : p ^ v * (s / p ^ v) = s := Nat.ordProj_mul_ordCompl_eq_self s p
    have hpv : 2 ≤ p ^ v := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hlt : s / p ^ v < s := Nat.div_lt_self (by omega) (by omega)
    have hpos : 1 ≤ s / p ^ v := by
      rcases Nat.eq_zero_or_pos (s / p ^ v) with h | h
      · rw [h, mul_zero] at hsplit; omega
      · exact h
    have hvK : v ≤ K := by
      apply Nat.le_log_of_pow_le one_lt_two
      calc
        2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp.two_le v
        _ ≤ s := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd s p)
        _ ≤ M := hsM
    have hpvX : p ^ v ∣ X :=
      ((pow_dvd_pow p hvK).trans (pow_dvd_pow_of_dvd hpn K)).trans (dvd_mul_right _ _)
    have hcop' : (p ^ v).Coprime (s / p ^ v) := (Nat.coprime_ordCompl hp hs0).pow_left v
    exact hs.2 (hsplit ▸ hcop'.mul_dvd_of_dvd_of_dvd hpvX (hmin _ hpos hlt))
  -- The order of `n` modulo `s` exceeds `c²`.
  refine ⟨s, hs2, hsM, ?_⟩
  have : NeZero s := ⟨by omega⟩
  have hunit : IsUnit (n : ZMod s) := (ZMod.isUnit_iff_coprime n s).mpr hcop.symm
  have hord : 0 < orderOf (n : ZMod s) := hunit.isOfFinOrder.orderOf_pos
  by_contra hle
  replace hle := not_lt.mp hle
  have hmem : orderOf (n : ZMod s) ∈ Icc 1 L := mem_Icc.mpr ⟨hord, hle⟩
  have hsdvd : s ∣ n ^ orderOf (n : ZMod s) - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow,
      pow_orderOf_eq_one, Nat.cast_one, sub_self]
  exact hs.2 ((hsdvd.trans (dvd_prod_of_mem (fun i => n ^ i - 1) hmem)).trans
    (dvd_mul_left N (n ^ K)))

/-- **A small modulus of large order, with logarithms**: for `n ≥ 2`, some `2 ≤ r ≤ 128 log₂⁵ n`
has `ord_r(n) > log₂² n` [Agrawal, Kayal, Saxena, Lemma 4.3][AKS2004], up to the constant. -/
theorem exists_lt_orderOf_logb {n : ℕ} (hn : 2 ≤ n) :
    ∃ r : ℕ, 2 ≤ r ∧ (r : ℝ) ≤ 128 * Real.logb 2 n ^ 5 ∧
      Real.logb 2 n ^ 2 < orderOf (n : ZMod r) := by
  obtain ⟨r, hr2, hrc, hord⟩ := exists_lt_orderOf hn
  set c := Nat.clog 2 n
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hn0]
    norm_num
    exact_mod_cast hn
  -- `log₂ n ≤ c`.
  have hlogc : Real.logb 2 n ≤ c := by
    rw [Real.logb_le_iff_le_rpow one_lt_two hn0, Real.rpow_natCast]
    exact_mod_cast Nat.le_pow_clog one_lt_two n
  -- `c ≤ 2 log₂ n`, since `2^(c - 1) < n`.
  have hcpred : ((c - 1 : ℕ) : ℝ) < Real.logb 2 n := by
    rw [Real.lt_logb_iff_rpow_lt one_lt_two hn0, Real.rpow_natCast]
    exact_mod_cast Nat.pow_pred_clog_lt_self one_lt_two (by omega)
  have hc1 : 1 ≤ c := Nat.clog_pos one_lt_two (by omega)
  have hc2 : (c : ℝ) ≤ 2 * Real.logb 2 n := by
    have : ((c - 1 : ℕ) : ℝ) = c - 1 := by push_cast [Nat.cast_sub hc1]; ring
    linarith
  refine ⟨r, hr2, ?_, ?_⟩
  · calc
      (r : ℝ) ≤ 4 * (c : ℝ) ^ 5 := by exact_mod_cast hrc
      _ ≤ 4 * (2 * Real.logb 2 n) ^ 5 := by gcongr
      _ = 128 * Real.logb 2 n ^ 5 := by ring
  · have h1 : Real.logb 2 n ^ 2 ≤ (c : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hlogc 2
    have h2 : ((c ^ 2 : ℕ) : ℝ) < (orderOf (n : ZMod r) : ℝ) := by exact_mod_cast hord
    push_cast at h2
    linarith

end Cslib.AKS
