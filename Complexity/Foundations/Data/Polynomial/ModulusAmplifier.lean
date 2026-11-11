/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Polynomial.ParityAmplifier
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# Modulus amplification for an arbitrary modulus

The polynomial `p_ℓ = parityAmplifier ℓ` satisfies `p_ℓ ≡ 1 (mod X ^ ℓ)` and
`p_ℓ ≡ 0 (mod (1 - X) ^ ℓ)`; its complement `1 - p_ℓ` is the optimal-degree modulus-amplifying
polynomial `P_ℓ` of Beigel and Tarui [BeigelTarui1994, Section 2.3], refining Toda's [Toda1991].
Hence for every integer modulus `m` and integer `y`,
`m ∣ y → p_ℓ(y) ≡ 1 (mod m ^ ℓ)` (`Polynomial.parityAmplifier_eval_modEq_one_of_dvd`) and
`m ∣ y - 1 → p_ℓ(y) ≡ 0 (mod m ^ ℓ)`
(`Polynomial.parityAmplifier_eval_modEq_zero_of_dvd_sub_one`); `ParityAmplifier` proves the
`m = 2` case. Composed with Fermat's little theorem, `1 - p_ℓ(z ^ (p - 1))` is the indicator of
`z ≢ 0 (mod p)` modulo `p ^ ℓ` for a prime `p`
(`Polynomial.one_sub_parityAmplifier_eval_pow_modEq`); its degree in `z` is at most
`(2ℓ - 1)(p - 1)` (`Polynomial.natDegree_parityAmplifier_le`).

## Main results

* `Polynomial.parityAmplifier_eval_modEq_one_of_dvd`,
  `Polynomial.parityAmplifier_eval_modEq_zero_of_dvd_sub_one`: amplification from modulus `m` to
  `m ^ ℓ`.
* `Polynomial.one_sub_parityAmplifier_eval_pow_modEq`: the Fermat-normalized `MOD_p` indicator
  modulo `p ^ ℓ`.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
-/

public section

namespace Polynomial

/-- If `m ∣ y`, then `p_ℓ(y) ≡ 1 (mod m ^ ℓ)`. -/
theorem parityAmplifier_eval_modEq_one_of_dvd (ℓ : ℕ) {m y : ℤ} (hy : m ∣ y) :
    (parityAmplifier ℓ).eval y ≡ 1 [ZMOD m ^ ℓ] := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp only [pow_zero, Int.modEq_one]
  rw [Int.modEq_iff_dvd]
  obtain ⟨q, hq⟩ := X_pow_dvd_one_sub_parityAmplifier hℓ
  have heval : 1 - (parityAmplifier ℓ).eval y = y ^ ℓ * q.eval y := by
    have := congr_arg (eval y) hq
    simpa only [eval_sub, eval_one, eval_mul, eval_pow, eval_X] using this
  rw [heval]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hy ℓ) _

/-- If `m ∣ y - 1`, then `p_ℓ(y) ≡ 0 (mod m ^ ℓ)`. -/
theorem parityAmplifier_eval_modEq_zero_of_dvd_sub_one (ℓ : ℕ) {m y : ℤ} (hy : m ∣ y - 1) :
    (parityAmplifier ℓ).eval y ≡ 0 [ZMOD m ^ ℓ] := by
  rw [Int.modEq_iff_dvd, zero_sub, dvd_neg]
  obtain ⟨q, hq⟩ := one_sub_X_pow_dvd_parityAmplifier ℓ
  have heval : (parityAmplifier ℓ).eval y = (1 - y) ^ ℓ * q.eval y := by
    have := congr_arg (eval y) hq
    simpa only [eval_mul, eval_pow, eval_sub, eval_one, eval_X] using this
  rw [heval]
  have h1 : m ∣ 1 - y := by
    rw [← neg_sub]
    exact dvd_neg.2 hy
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd h1 ℓ) _

/-- **Fermat-normalized modulus amplification.** For a prime `p`, `1 - p_ℓ(z ^ (p - 1))` is
congruent modulo `p ^ ℓ` to the indicator of `z ≢ 0 (mod p)`. -/
theorem one_sub_parityAmplifier_eval_pow_modEq {p : ℕ} (hp : p.Prime) (ℓ : ℕ) (z : ℤ) :
    1 - (parityAmplifier ℓ).eval (z ^ (p - 1)) ≡
      (if z % p ≠ 0 then 1 else 0) [ZMOD (p : ℤ) ^ ℓ] := by
  split_ifs with hz
  · have hcop : IsCoprime z p := by
      rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
      exact fun h => hz (Int.emod_eq_zero_of_dvd h)
    have h0 := parityAmplifier_eval_modEq_zero_of_dvd_sub_one ℓ
      (Int.modEq_iff_dvd.1 (Int.ModEq.pow_card_sub_one_eq_one hp hcop).symm)
    calc 1 - (parityAmplifier ℓ).eval (z ^ (p - 1)) ≡ 1 - 0 [ZMOD (p : ℤ) ^ ℓ] :=
          Int.ModEq.sub_left 1 h0
      _ = 1 := sub_zero 1
  · have hdvd : (p : ℤ) ∣ z ^ (p - 1) :=
      dvd_pow (Int.dvd_of_emod_eq_zero (not_not.1 hz)) (Nat.sub_ne_zero_of_lt hp.one_lt)
    calc 1 - (parityAmplifier ℓ).eval (z ^ (p - 1)) ≡ 1 - 1 [ZMOD (p : ℤ) ^ ℓ] :=
          Int.ModEq.sub_left 1 (parityAmplifier_eval_modEq_one_of_dvd ℓ hdvd)
      _ = 0 := sub_self 1

end Polynomial
