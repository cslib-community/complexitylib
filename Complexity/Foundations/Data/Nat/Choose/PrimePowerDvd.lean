/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Choose/Lucas.lean`)

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Divisibility by prime powers through binomial coefficients

For a prime `p`, the base-`p` digits of `c` are read off modulo `p` by binomial coefficients:
`C(c, p ^ i) ≡ ⌊c / p ^ i⌋ (mod p)` by Lucas's theorem. Hence `p ^ e ∣ c` exactly when
`p ∣ C(c, p ^ i)` for every `i < e` (`Nat.pow_dvd_iff_forall_dvd_choose`), and `c` is not divisible
by a positive `m` exactly when `p ∤ C(c, p ^ i)` for some prime `p` and some `i` with
`p ^ (i + 1) ∣ m` (`Nat.mod_ne_zero_iff_exists_not_dvd_choose`). This is the reduction of a
`MOD_m` gate to `MOD_p` tests of polynomials of degree below `m` [BeigelTarui1994, Lemma 2.1 and
Fact 2.2].

## Main results

* `Nat.pow_dvd_iff_forall_dvd_choose`: `p ^ e ∣ c ↔ ∀ i < e, p ∣ C(c, p ^ i)`.
* `Nat.mod_ne_zero_iff_exists_not_dvd_choose`: `c % m ≠ 0` through prime-power binomial
  coefficients.

## References

* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
-/

public section

namespace Nat

/-- `C(c, p ^ (i + 1)) ≡ C(c / p, p ^ i) (mod p)` for a prime `p`: one step of Lucas's theorem. -/
theorem choose_pow_succ_modEq {p : ℕ} (hp : p.Prime) (c i : ℕ) :
    c.choose (p ^ (i + 1)) ≡ (c / p).choose (p ^ i) [MOD p] := by
  have := Fact.mk hp
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := c) (k := p ^ (i + 1)) (p := p)
  rwa [pow_succ, Nat.mul_mod_left, Nat.choose_zero_right, one_mul,
    Nat.mul_div_cancel _ hp.pos] at h

/-- **Prime-power divisibility from binomial coefficients.** For a prime `p`, `p ^ e ∣ c` exactly
when `p ∣ C(c, p ^ i)` for every `i < e`: the binomial coefficient `C(c, p ^ i)` is the `i`-th
base-`p` digit of `c` modulo `p` [BeigelTarui1994, Fact 2.2]. -/
theorem pow_dvd_iff_forall_dvd_choose {p : ℕ} (hp : p.Prime) (e c : ℕ) :
    p ^ e ∣ c ↔ ∀ i < e, p ∣ c.choose (p ^ i) := by
  induction e generalizing c with
  | zero => simp
  | succ e ih =>
    have hsplit : p ^ (e + 1) ∣ c ↔ p ∣ c ∧ p ^ e ∣ c / p := by
      constructor
      · intro h
        have hpc : p ∣ c := (dvd_pow_self p e.succ_ne_zero).trans h
        refine ⟨hpc, ?_⟩
        rw [Nat.dvd_div_iff_mul_dvd hpc, ← pow_succ']
        exact h
      · rintro ⟨hpc, h⟩
        rw [Nat.dvd_div_iff_mul_dvd hpc, ← pow_succ'] at h
        exact h
    rw [hsplit, ih]
    constructor
    · rintro ⟨h0, hrest⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · exact ((choose_pow_succ_modEq hp c i).dvd_iff dvd_rfl).2 (hrest i (by omega))
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      exact ((choose_pow_succ_modEq hp c i).dvd_iff dvd_rfl).1 (h (i + 1) (by omega))

/-- **Non-divisibility through prime-power binomial coefficients.** For `m > 0`, `c` is not
divisible by `m` exactly when some prime `p` and some `i` with `p ^ (i + 1) ∣ m` have
`p ∤ C(c, p ^ i)`. Such `p` and `i` satisfy `p ≤ m` and `i < m`. -/
theorem mod_ne_zero_iff_exists_not_dvd_choose {m : ℕ} (hm : 0 < m) (c : ℕ) :
    c % m ≠ 0 ↔ ∃ p i, p.Prime ∧ p ^ (i + 1) ∣ m ∧ ¬ p ∣ c.choose (p ^ i) := by
  constructor
  · intro hc
    have hmc : ¬ m ∣ c := fun h => hc (Nat.mod_eq_zero_of_dvd h)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hmc (dvd_zero m)
    have hle : ¬ m.factorization ≤ c.factorization := fun h =>
      hmc ((Nat.factorization_le_iff_dvd hm.ne' hc0).1 h)
    rw [Finsupp.le_def] at hle
    push Not at hle
    obtain ⟨p, hlt⟩ := hle
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.2 ((Nat.zero_le _).trans_lt hlt).ne')
    have hpm : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
    have hpc : ¬ p ^ m.factorization p ∣ c := by
      rw [hp.pow_dvd_iff_le_factorization hc0]
      omega
    rw [pow_dvd_iff_forall_dvd_choose hp] at hpc
    push Not at hpc
    obtain ⟨i, hi, hndvd⟩ := hpc
    exact ⟨p, i, hp, (pow_dvd_pow p hi).trans hpm, hndvd⟩
  · rintro ⟨p, i, hp, hpm, hpc⟩ hc
    have hmc : m ∣ c := Nat.dvd_of_mod_eq_zero hc
    exact hpc ((pow_dvd_iff_forall_dvd_choose hp (i + 1) c).1 (hpm.trans hmc) i (by omega))

end Nat
