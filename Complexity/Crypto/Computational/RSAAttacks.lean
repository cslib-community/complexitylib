/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.RSATrapdoor
public import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.ZMod.Units

/-!
# Attacks on plain RSA and factoring from RSA secrets

Algebraic attacks on plain (textbook) RSA encryption `c = m ^ e % N` (`rsaEval`), and the
elementary steps that recover the factorization of `N` from secret RSA data. Each attack is stated
for the exact arithmetic it exploits; none of them uses a hardness assumption.

* **Malleability.** `rsaEval` is multiplicative, so anyone can turn an encryption of `m` into an
  encryption of `m * s % N`.
* **Common modulus.** Two encryptions of the same unit `m` under one modulus and coprime exponents
  `e₁, e₂` reveal `m`: with Bézout coefficients `a * e₁ + b * e₂ = 1`, `c₁ ^ a * c₂ ^ b = m`
  (`commonModulusAttack`).
* **Small messages and the broadcast attack.** If `m ^ e < N`, the ciphertext is `m ^ e` over the
  integers, so `m` is its integer `e`-th root. If the same `m` is sent to receivers with pairwise
  coprime moduli whose product exceeds `m ^ e`, the Chinese remainder combination of the
  ciphertexts is again `m ^ e`.
* **Factoring from `φ(N)`.** `N = p * q` and `φ(N) = (p - 1) * (q - 1)` determine `p + q` and
  `(p - q) ^ 2`, hence `p` and `q` (`factorOfTotient`).
* **Factoring from `(N, e, d)`.** Every unit `x` modulo `N` satisfies `x ^ (e * d - 1) ≡ 1`, and a
  square root `y` of `1` modulo `N` other than `±1` gives the proper factor `gcd(y - 1, N)`.

## Main definitions

* `Cslib.Crypto.zmodIntPow`: integer powers of a residue, inverting for negative exponents.
* `Cslib.Crypto.commonModulusAttack`: the common-modulus recovery `c₁ ^ a * c₂ ^ b` modulo `N`.
* `Cslib.Crypto.factorOfTotient`: the two factors of `N` computed from `N` and `φ(N)`.

## Main results

* `Cslib.Crypto.rsaEval_mul`, `Cslib.Crypto.rsaInvert_rsaEval_mul`: plain RSA is multiplicatively
  homomorphic, and the blinded ciphertext decrypts to `m * s % N`.
* `Cslib.Crypto.commonModulusAttack_rsaEval`: the common-modulus attack recovers every unit `m`.
* `Cslib.Crypto.rsaEval_eq_pow_of_pow_lt`, `Cslib.Crypto.eq_of_pow_eq_rsaEval`: a short message is
  the unique integer `e`-th root of its ciphertext.
* `Cslib.Crypto.chineseRemainderOfList_rsaEval_eq_pow`: the broadcast attack.
* `Cslib.Crypto.factorOfTotient_eq`, `Cslib.Crypto.RSADesc.factorOfTotient_eq`: factoring from
  `φ(N)`.
* `Cslib.Crypto.RSADesc.pow_mul_sub_one_modEq_one`, `Cslib.Crypto.RSADesc.gcd_sub_one_proper`:
  the number-theoretic steps of factoring from `(N, e, d)`.

## Implementation notes

The common-modulus attack is stated in `ZMod N`, where `zmodIntPow` uses Mathlib's `ZMod.inv`; the
statement requires `m` to be coprime to `N`. The two statements on factoring from `(N, e, d)`
are deterministic ingredients of the proof of [KatzLindell2020], Corollary 9.51 (Section 9.2.5),
which also needs the probability bound that a random unit leads to a nontrivial square root of
`1`; that probabilistic algorithm and its analysis are not formalized here, so Corollary 9.51
itself is not claimed. Factoring from `φ(N)` and the common-modulus attack are standard and are
not attributed to a particular locator in [KatzLindell2020].

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 12.5.1 (plain RSA encryption and its attacks for small messages and for one message
  sent to several receivers) and Section 9.2.5 (Corollary 9.51).
-/

@[expose] public section

namespace Cslib.Crypto

/-! ### Malleability -/

/-- Plain RSA is multiplicatively homomorphic: the encryption of a product is the product of the
encryptions, reduced modulo `N`. -/
theorem rsaEval_mul (N e m s : ℕ) :
    rsaEval N e (m * s) = rsaEval N e m * rsaEval N e s % N := by
  unfold rsaEval
  rw [mul_pow, Nat.mul_mod]

/-- Malleability of plain RSA: multiplying a ciphertext of `m` by the encryption of any `s` gives
a ciphertext that decrypts to `m * s % N`. -/
theorem rsaInvert_rsaEval_mul (desc : RSADesc) (m s : ℕ) :
    rsaInvert desc.modulus desc.d
        (rsaEval desc.modulus desc.e m * rsaEval desc.modulus desc.e s % desc.modulus) =
      m * s % desc.modulus := by
  rw [← rsaEval_mul, show rsaEval desc.modulus desc.e (m * s) =
      rsaEval desc.modulus desc.e (m * s % desc.modulus) by unfold rsaEval; rw [Nat.pow_mod]]
  exact rsaInvert_rsaEval desc (Nat.mod_lt _ desc.modulus_pos)

/-! ### Common modulus -/

/-- The integer power `x ^ k` of a residue `x : ZMod N`, computed as `(x⁻¹) ^ (-k)` with
Mathlib's `ZMod.inv` when `k < 0`. -/
def zmodIntPow {N : ℕ} (x : ZMod N) (k : ℤ) : ZMod N :=
  if 0 ≤ k then x ^ k.toNat else x⁻¹ ^ (-k).toNat

/-- On units, `zmodIntPow` is the group integer power. -/
theorem zmodIntPow_units {N : ℕ} (u : (ZMod N)ˣ) (k : ℤ) :
    zmodIntPow (u : ZMod N) k = ((u ^ k : (ZMod N)ˣ) : ZMod N) := by
  unfold zmodIntPow
  split_ifs with hk
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by omega⟩
    rw [Int.toNat_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [ZMod.inv_coe_unit, neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast, ← inv_pow,
      Units.val_pow_eq_pow_val]

/-- The common-modulus attack on plain RSA: given encryptions `c₁, c₂` of one message under the
same modulus `N` and exponents `e₁, e₂`, output `c₁ ^ a * c₂ ^ b` in `ZMod N`, where
`a = Nat.gcdA e₁ e₂` and `b = Nat.gcdB e₁ e₂` are Bézout coefficients. -/
def commonModulusAttack (N e₁ e₂ c₁ c₂ : ℕ) : ZMod N :=
  zmodIntPow (c₁ : ZMod N) (Nat.gcdA e₁ e₂) * zmodIntPow (c₂ : ZMod N) (Nat.gcdB e₁ e₂)

/-- The common-modulus attack recovers the residue of every message `m` coprime to `N` (so `m`
itself when `m < N`) from its plain RSA encryptions under coprime exponents `e₁, e₂`. -/
theorem commonModulusAttack_rsaEval {N e₁ e₂ m : ℕ} (he : Nat.Coprime e₁ e₂)
    (hm : Nat.Coprime m N) :
    commonModulusAttack N e₁ e₂ (rsaEval N e₁ m) (rsaEval N e₂ m) = m := by
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime m hm
  have hcast (k : ℕ) : ((rsaEval N k m : ℕ) : ZMod N) = ((u ^ k : (ZMod N)ˣ) : ZMod N) := by
    rw [rsaEval, ZMod.natCast_mod, Nat.cast_pow, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime]
  have hbezout : (e₁ : ℤ) * Nat.gcdA e₁ e₂ + e₂ * Nat.gcdB e₁ e₂ = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, he.gcd_eq_one, Nat.cast_one]
  rw [commonModulusAttack, hcast, hcast, ← zpow_natCast, ← zpow_natCast, zmodIntPow_units,
    zmodIntPow_units, ← Units.val_mul, ← zpow_mul, ← zpow_mul, ← zpow_add, hbezout, zpow_one,
    ZMod.coe_unitOfCoprime]

/-! ### Small messages and the broadcast attack -/

/-- For a short message, `m ^ e < N`, plain RSA performs no modular reduction: the ciphertext is
`m ^ e` over the integers. -/
theorem rsaEval_eq_pow_of_pow_lt {N e m : ℕ} (hsmall : m ^ e < N) : rsaEval N e m = m ^ e :=
  Nat.mod_eq_of_lt hsmall

/-- A short message is the unique integer `e`-th root of its ciphertext, so it is recovered by an
integer root computation. -/
theorem eq_of_pow_eq_rsaEval {N e m m' : ℕ} (he : e ≠ 0) (hsmall : m ^ e < N)
    (hroot : m' ^ e = rsaEval N e m) : m' = m :=
  Nat.pow_left_injective he (hroot.trans (rsaEval_eq_pow_of_pow_lt hsmall))

/-- The broadcast attack: if one message `m` is encrypted under pairwise coprime moduli `N i`
(`i ∈ l`) with a common exponent `e` and `m ^ e` is smaller than the product of the moduli, then
the Chinese remainder combination of the ciphertexts is `m ^ e` over the integers. -/
theorem chineseRemainderOfList_rsaEval_eq_pow {ι : Type*} {N : ι → ℕ} {e m : ℕ} (l : List ι)
    (co : l.Pairwise (Function.onFun Nat.Coprime N)) (hN : ∀ i ∈ l, N i ≠ 0)
    (hsmall : m ^ e < (l.map N).prod) :
    (Nat.chineseRemainderOfList (fun i => rsaEval (N i) e m) N l co : ℕ) = m ^ e := by
  have hmod : m ^ e ≡ Nat.chineseRemainderOfList (fun i => rsaEval (N i) e m) N l co
      [MOD (l.map N).prod] :=
    Nat.chineseRemainderOfList_modEq_unique _ N l co fun i _ => (Nat.mod_modEq _ _).symm
  have hlt := Nat.chineseRemainderOfList_lt_prod (fun i => rsaEval (N i) e m) N l co hN
  rw [Nat.ModEq, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hlt] at hmod
  exact hmod.symm

/-- The broadcast attack recovers the message: `m` is the unique integer `e`-th root of the Chinese
remainder combination of its ciphertexts. -/
theorem eq_of_pow_eq_chineseRemainderOfList_rsaEval {ι : Type*} {N : ι → ℕ} {e m m' : ℕ}
    (he : e ≠ 0) (l : List ι) (co : l.Pairwise (Function.onFun Nat.Coprime N))
    (hN : ∀ i ∈ l, N i ≠ 0)
    (hsmall : m ^ e < (l.map N).prod)
    (hroot : m' ^ e = Nat.chineseRemainderOfList (fun i => rsaEval (N i) e m) N l co) :
    m' = m :=
  Nat.pow_left_injective he (hroot.trans (chineseRemainderOfList_rsaEval_eq_pow l co hN hsmall))

/-! ### Factoring from `φ(N)` -/

/-- The factors of `N` computed from `N` and `φ = φ(N)`: with `s = N + 1 - φ` (which is `p + q`)
and `r = ⌊√(s ^ 2 - 4 * N)⌋` (which is `|p - q|`), output `((s + r) / 2, (s - r) / 2)`. -/
def factorOfTotient (N φ : ℕ) : ℕ × ℕ :=
  ((N + 1 - φ + Nat.sqrt ((N + 1 - φ) ^ 2 - 4 * N)) / 2,
    (N + 1 - φ - Nat.sqrt ((N + 1 - φ) ^ 2 - 4 * N)) / 2)

/-- For positive `q ≤ p`, `factorOfTotient` recovers `(p, q)` from `p * q` and
`(p - 1) * (q - 1)`. -/
theorem factorOfTotient_eq {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) :
    factorOfTotient (p * q) ((p - 1) * (q - 1)) = (p, q) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hqp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt hq
  have hsum : (b + 1 + t) * (b + 1) + 1 - (b + 1 + t - 1) * (b + 1 - 1) = 2 * (b + 1) + t := by
    rw [show b + 1 + t - 1 = b + t by omega, show b + 1 - 1 = b by omega]
    rw [show (b + 1 + t) * (b + 1) + 1 = (b + t) * b + (2 * (b + 1) + t) by ring]
    omega
  have hdisc : (2 * (b + 1) + t) ^ 2 - 4 * ((b + 1 + t) * (b + 1)) = t ^ 2 := by
    rw [show (2 * (b + 1) + t) ^ 2 = t ^ 2 + 4 * ((b + 1 + t) * (b + 1)) by ring]
    omega
  simp only [zero_add] at *
  rw [factorOfTotient, hsum, hdisc, Nat.sqrt_eq']
  ext <;> dsimp only <;> omega

namespace RSADesc

/-- The factorization `(max p q, min p q)` of an RSA modulus is computed from `N` and `φ(N)`. -/
theorem factorOfTotient_eq (desc : RSADesc) :
    factorOfTotient desc.modulus desc.totient = (max desc.p desc.q, min desc.p desc.q) := by
  rcases le_total desc.q desc.p with h | h
  · rw [max_eq_left h, min_eq_right h]
    exact Cslib.Crypto.factorOfTotient_eq desc.hq.pos h
  · rw [max_eq_right h, min_eq_left h, modulus, totient, mul_comm desc.p, mul_comm (desc.p - 1)]
    exact Cslib.Crypto.factorOfTotient_eq desc.hp.pos h

/-! ### Factoring from `(N, e, d)` -/

/-- `e * d - 1` is a multiple of the order of every unit modulo `N`: `x ^ (e * d - 1) ≡ 1` for
every `x` coprime to `N`. -/
theorem pow_mul_sub_one_modEq_one (desc : RSADesc) {x : ℕ} (hx : Nat.Coprime x desc.modulus) :
    x ^ (desc.e * desc.d - 1) ≡ 1 [MOD desc.modulus] := by
  have hed_pos : 0 < desc.e * desc.d := by
    have h : desc.e * desc.d % desc.totient = 1 := by
      have h := desc.hed
      rwa [Nat.ModEq, Nat.mod_eq_of_lt desc.totient_gt_one] at h
    by_contra h0
    rw [Nat.eq_zero_of_not_pos h0, Nat.zero_mod] at h
    exact zero_ne_one h
  have hmul : x ^ (desc.e * desc.d - 1) * x ≡ 1 * x [MOD desc.modulus] := by
    rw [← pow_succ, Nat.sub_add_cancel hed_pos, one_mul]
    exact rsa_pow_mul_modEq desc x
  exact Nat.ModEq.cancel_right_of_coprime (Nat.coprime_comm.mp hx).gcd_eq_one hmul

/-- A square root `y` of `1` modulo an RSA modulus `N = p * q`, other than `±1`, gives a proper
factor `gcd(y - 1, N)` of `N`. -/
theorem gcd_sub_one_proper (desc : RSADesc) {y : ℕ} (hsq : y ^ 2 ≡ 1 [MOD desc.modulus])
    (hone : ¬ y ≡ 1 [MOD desc.modulus]) (hneg : ¬ y + 1 ≡ 0 [MOD desc.modulus]) :
    1 < Nat.gcd (y - 1) desc.modulus ∧ Nat.gcd (y - 1) desc.modulus < desc.modulus := by
  have hN := desc.modulus_gt_one
  have hy : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with rfl | h
    · exfalso
      have h := hsq
      rw [Nat.ModEq, zero_pow two_ne_zero, Nat.zero_mod, Nat.mod_eq_of_lt hN] at h
      exact zero_ne_one h
    · exact h
  have hcop : Nat.Coprime desc.p desc.q := (Nat.coprime_primes desc.hp desc.hq).mpr desc.hpq
  -- `N` divides `(y - 1) * (y + 1) = y ^ 2 - 1`.
  have hdvd : desc.modulus ∣ (y - 1) * (y + 1) := by
    have h := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hy)).mp hsq.symm
    rwa [show y ^ 2 - 1 = (y - 1) * (y + 1) by
      obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hy
      rw [show 1 + z - 1 = z by omega]
      rw [show (1 + z) ^ 2 = z * (1 + z + 1) + 1 by ring]
      omega] at h
  have hone' : ¬ desc.modulus ∣ y - 1 := fun h => hone ((Nat.modEq_iff_dvd' hy).mpr h).symm
  have hneg' : ¬ desc.modulus ∣ y + 1 := fun h => hneg (Nat.modEq_zero_iff_dvd.mpr h)
  have hp := (Nat.Prime.dvd_mul desc.hp).mp (dvd_trans (dvd_mul_right _ _) hdvd)
  have hq := (Nat.Prime.dvd_mul desc.hq).mp (dvd_trans (dvd_mul_left _ _) hdvd)
  -- Exactly one of `p, q` divides `y - 1`.
  have hfactor : desc.p ∣ y - 1 ∨ desc.q ∣ y - 1 := by
    rcases hp with hp | hp
    · exact Or.inl hp
    rcases hq with hq | hq
    · exact Or.inr hq
    · exact absurd (hcop.mul_dvd_of_dvd_of_dvd hp hq) hneg'
  refine ⟨?_, lt_of_le_of_ne (Nat.gcd_le_right _ desc.modulus_pos) fun h => hone' ?_⟩
  · rcases hfactor with h | h
    · exact lt_of_lt_of_le desc.hp.one_lt
        (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ desc.modulus_pos)
          (Nat.dvd_gcd h (dvd_mul_right _ _)))
    · exact lt_of_lt_of_le desc.hq.one_lt
        (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ desc.modulus_pos)
          (Nat.dvd_gcd h (dvd_mul_left _ _)))
  · rw [← h]
    exact Nat.gcd_dvd_left _ _

end RSADesc

end Cslib.Crypto
