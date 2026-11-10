/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Polynomial.ParityAmplifier
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
(`Polynomial.parityAmplifier_eval_modEq_zero_of_dvd_sub_one`), both proved in `ParityAmplifier`.
Composed with Fermat's little theorem, `1 - p_ℓ(z ^ (p - 1))` is the indicator of
`z ≢ 0 (mod p)` modulo `p ^ ℓ` for a prime `p`
(`Polynomial.one_sub_parityAmplifier_eval_pow_modEq`); its degree in `z` is at most
`(2ℓ - 1)(p - 1)` (`Polynomial.natDegree_parityAmplifier_le`).

## Main results

* `Polynomial.one_sub_parityAmplifier_eval_pow_modEq`: the Fermat-normalized `MOD_p` indicator
  modulo `p ^ ℓ`.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
-/

public section

namespace Polynomial

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
