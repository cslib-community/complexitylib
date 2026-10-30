/-
Copyright (c) 2026 Anthropic, PBC, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting the primes up to m, in natural numbers

Three elementary bounds on the number `π(m)` of primes up to `m`, the cardinality of
`Nat.primesLE m`, together with elementary upper bounds on `Nat.lcmUpto n`.

* `π(m) ≤ m` (`Nat.card_primesLE_le`).
* `m ≤ (⌊log₂ m⌋ + 1)(π(m) + 1)` (`Nat.le_log_mul_card_primesLE`), from the bound
  `2^m ≤ (m + 1) lcm(1, …, m)` of Mathlib: each prime power in the least common multiple is at most
  `m`.
* So there are at least `w` primes up to `(w + 1)(2⌊log₂(w + 1)⌋ + 4)`
  (`Nat.le_card_primesLE_mul_log`).
* For `n ≤ m`, `Nat.lcmUpto (m + n)` divides `Nat.lcmUpto m * (m + n).choose m`
  (`Nat.lcmUpto_add_dvd`), yielding `2 * Nat.lcmUpto n ≤ 4 ^ n` (`Nat.two_mul_lcmUpto_le_four_pow`)
  and `Nat.lcmUpto n < 4 ^ n` (`Nat.lcmUpto_lt_four_pow`) for `1 ≤ n`.

Adapted from [PrimeCounting.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Util/PrimeCounting.lean) in
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5` and lean/Proofs/PrimeCycles.lean
in [S. Schlesinger,
*Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].

## Main results

* `Nat.le_card_primesLE_mul_log`: an explicit prime-counting lower bound.
* `Nat.lcmUpto_add_dvd`, `Nat.lcmUpto_add_le`: binomial divisibility and upper bound on
  `Nat.lcmUpto (m + n)`.
* `Nat.two_mul_lcmUpto_le_four_pow`, `Nat.lcmUpto_lt_four_pow`: `2 * lcm(1, …, n) ≤ 4 ^ n` and
  `lcm(1, …, n) < 4 ^ n` for `1 ≤ n`.

-/

@[expose] public section

namespace Nat

open Finset

/-- There are at most `m` primes up to `m`. -/
theorem card_primesLE_le (m : ℕ) : #(Nat.primesLE m) ≤ m := by
  rw [Nat.primesLE_eq_filter_Icc_one]
  exact (card_filter_le _ _).trans_eq (by simp)

/-- A lower bound of Chebyshev's type in natural numbers: `m ≤ (⌊log₂ m⌋ + 1)(π(m) + 1)`. -/
theorem le_log_mul_card_primesLE (m : ℕ) : m ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set l := Nat.log 2 m
  have hlt : m < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
  calc 2 ^ m ≤ (m + 1) * Nat.lcmUpto m := Chebyshev.two_pow_le_mul_lcmUpto m
    _ = (m + 1) * ∏ p ∈ Nat.primesLE m, p ^ p.log m := by rw [Nat.lcmUpto_eq_prod_pow_log]
    _ ≤ 2 ^ (l + 1) * (2 ^ (l + 1)) ^ #(Nat.primesLE m) := Nat.mul_le_mul hlt
        (prod_le_pow_card _ _ _ fun p _ => (Nat.pow_log_le_self p hm.ne').trans hlt.le)
    _ = 2 ^ ((l + 1) * (#(Nat.primesLE m) + 1)) := by rw [← pow_succ', ← pow_mul]

/-- There are at least `w` primes up to `(w + 1)(2⌊log₂(w + 1)⌋ + 4)`. -/
theorem le_card_primesLE_mul_log (w : ℕ) :
    w ≤ #(Nat.primesLE ((w + 1) * (2 * Nat.log 2 (w + 1) + 4))) := by
  set a := Nat.log 2 (w + 1)
  set m := (w + 1) * (2 * a + 4) with hm
  have hw : w + 1 < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have ha : 2 * a + 4 ≤ 2 ^ (a + 2) := by
    have := Nat.lt_two_pow_self (n := a + 1)
    rw [pow_succ]
    omega
  have hlog : Nat.log 2 m < 2 * a + 3 := Nat.log_lt_of_lt_pow (by positivity) <|
    calc m < 2 ^ (a + 1) * 2 ^ (a + 2) := Nat.mul_lt_mul_of_lt_of_le hw ha (by positivity)
      _ = 2 ^ (2 * a + 3) := by rw [← pow_add]; congr 1; omega
  have hlt : (2 * a + 3) * (w + 1) < (2 * a + 3) * (#(Nat.primesLE m) + 1) :=
    calc (2 * a + 3) * (w + 1) < (2 * a + 4) * (w + 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = m := mul_comm _ _
      _ ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := le_log_mul_card_primesLE m
      _ ≤ (2 * a + 3) * (#(Nat.primesLE m) + 1) := Nat.mul_le_mul_right _ hlog
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega

/-- For `n ≤ m`, `Nat.lcmUpto (m + n)` divides `Nat.lcmUpto m * (m + n).choose m`. Every prime power
`p ^ L ≤ m + n` exceeding `m` satisfies `m < p ^ L ≤ m + n`, which forces a base-`p` carry at
digit `L` when adding `m` and `n`. -/
theorem lcmUpto_add_dvd {m n : ℕ} (h : n ≤ m) :
    Nat.lcmUpto (m + n) ∣ Nat.lcmUpto m * (m + n).choose m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · have hn : n = 0 := by omega
    subst hn
    decide
  · have hpos : 0 < (m + n).choose m := Nat.choose_pos (Nat.le_add_right m n)
    rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero _)
      (Nat.mul_ne_zero (Nat.lcmUpto_ne_zero _) hpos.ne')]
    intro p hp
    rw [Nat.factorization_lcmUpto (m + n) hp,
      Nat.factorization_mul (Nat.lcmUpto_ne_zero m) hpos.ne',
      Finsupp.coe_add, Pi.add_apply, Nat.factorization_lcmUpto m hp]
    set L := p.log (m + n)
    by_cases hL : L ≤ p.log m
    · omega
    · have hL : p.log m < L := by omega
      have hLpos : 1 ≤ L := by omega
      have hpow : p ^ L ≤ m + n := Nat.pow_log_le_self p (by omega)
      have hpow_pred : p ^ (L - 1) ≤ m := by
        have h1 : p ^ (L - 1) * p ≤ p * m := by
          calc
            p ^ (L - 1) * p = p ^ L := by rw [← pow_succ, Nat.sub_add_cancel hLpos]
            _ ≤ m + n := hpow
            _ ≤ 2 * m := by omega
            _ ≤ p * m := Nat.mul_le_mul_right m hp.two_le
        exact Nat.le_of_mul_le_mul_left (by linarith) hp.pos
      have hlog_ge : L - 1 ≤ p.log m := Nat.le_log_of_pow_le hp.one_lt hpow_pred
      have hLeq : L = p.log m + 1 := by omega
      have hm_lt : m < p ^ L := Nat.lt_pow_of_log_lt hp.one_lt hL
      have hn_lt : n < p ^ L := lt_of_le_of_lt h hm_lt
      have hchoose : 1 ≤ ((m + n).choose m).factorization p := by
        rw [Nat.add_comm m n,
          Nat.factorization_choose' hp (by rw [Nat.add_comm n m]; exact Nat.lt_succ_self L)]
        refine Finset.card_pos.mpr
          ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hLpos, Nat.lt_succ_self L⟩, ?_⟩⟩
        rw [Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hn_lt]
        exact hpow
      omega

/-- For `n ≤ m`, `Nat.lcmUpto (m + n) ≤ Nat.lcmUpto m * (m + n).choose m`. -/
theorem lcmUpto_add_le {m n : ℕ} (h : n ≤ m) :
    Nat.lcmUpto (m + n) ≤ Nat.lcmUpto m * (m + n).choose m :=
  Nat.le_of_dvd (Nat.mul_pos (Nat.lcmUpto_pos m) (Nat.choose_pos (Nat.le_add_right m n)))
    (lcmUpto_add_dvd h)

/-- Elementary upper bound `2 * lcm(1, …, n) ≤ 4 ^ n` for all `n ≥ 1`. -/
theorem two_mul_lcmUpto_le_four_pow (n : ℕ) (hn : 1 ≤ n) :
    2 * Nat.lcmUpto n ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | ind n ihn =>
    rcases le_or_gt n 2 with hn2 | hn2
    · interval_cases n <;> decide
    · rcases n.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hm : 1 ≤ m := by omega
        have hlt : m < m + m := by omega
        have hih := ihn m hlt hm
        have hdvd := lcmUpto_add_le (le_rfl : m ≤ m)
        have hbin : (m + m).choose m ≤ 4 ^ m := by
          calc
            (m + m).choose m ≤ ∑ i ∈ Finset.range (m + m + 1), (m + m).choose i :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                (Finset.mem_range.mpr (by omega))
            _ = 2 ^ (m + m) := Nat.sum_range_choose (m + m)
            _ = 4 ^ m := by rw [← two_mul, pow_mul]; norm_num
        calc
          2 * Nat.lcmUpto (m + m) ≤ 2 * (Nat.lcmUpto m * (m + m).choose m) :=
            Nat.mul_le_mul_left 2 hdvd
          _ = (2 * Nat.lcmUpto m) * (m + m).choose m := by ring
          _ ≤ 4 ^ m * 4 ^ m := Nat.mul_le_mul hih hbin
          _ = 4 ^ (m + m) := by rw [← pow_add]
      · have hm1 : 1 ≤ m + 1 := by omega
        have hlt : m + 1 < 2 * m + 1 := by omega
        have hih := ihn (m + 1) hlt hm1
        have hdvd : Nat.lcmUpto (2 * m + 1) ≤ Nat.lcmUpto (m + 1) * (2 * m + 1).choose m := by
          have h1 : Nat.lcmUpto ((m + 1) + m) ≤
              Nat.lcmUpto (m + 1) * ((m + 1) + m).choose (m + 1) :=
            lcmUpto_add_le (Nat.le_succ m)
          have hchoose : ((m + 1) + m).choose (m + 1) = (2 * m + 1).choose m := by
            rw [Nat.choose_symm_add]
            congr 1
            omega
          have h2 : (m + 1) + m = 2 * m + 1 := by omega
          rwa [hchoose, h2] at h1
        have hbin : (2 * m + 1).choose m ≤ 4 ^ m := Nat.choose_middle_le_pow m
        calc
          2 * Nat.lcmUpto (2 * m + 1) ≤ 2 * (Nat.lcmUpto (m + 1) * (2 * m + 1).choose m) :=
            Nat.mul_le_mul_left 2 hdvd
          _ = (2 * Nat.lcmUpto (m + 1)) * (2 * m + 1).choose m := by ring
          _ ≤ 4 ^ (m + 1) * 4 ^ m := Nat.mul_le_mul hih hbin
          _ = 4 ^ (2 * m + 1) := by
            rw [← pow_add]
            congr 1
            omega

/-- For every `n ≥ 1`, `lcm(1, …, n) < 4 ^ n`. -/
theorem lcmUpto_lt_four_pow (n : ℕ) (hn : 1 ≤ n) :
    Nat.lcmUpto n < 4 ^ n := by
  have hpos := Nat.lcmUpto_pos n
  have hle := two_mul_lcmUpto_le_four_pow n hn
  omega

end Nat
