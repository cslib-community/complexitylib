/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity

/-!
# The group structure behind Paillier encryption

Paillier encryption works in the unit group of `ZMod (N ^ 2)` for a modulus `N = p * q`. This file
proves the three facts that make up [KatzLindell2020], Proposition 15.6:

* for distinct odd primes `p` and `q` of the same bit length, `gcd(N, φ(N)) = 1` (Claim 15.7);
* for every positive `N`, `(1 + N) ^ a = 1 + a * N` in `ZMod (N ^ 2)`, so `1 + N` has order
  exactly `N` there (Claim 15.8);
* when `gcd(N, φ(N)) = 1`, the map `(a, b) ↦ (1 + N) ^ a * b ^ N` is a group isomorphism from
  `ZMod N × (ZMod N)ˣ` onto `(ZMod (N ^ 2))ˣ` (Claim 15.9).

It also proves the identity behind Paillier decryption: raising `(1 + N) ^ m * r ^ N` to the
power `φ(N)` removes the randomness `r` and leaves `1 + m * φ(N) * N`.

## Main definitions

* `Cslib.Crypto.Paillier.unitsEquiv`: the isomorphism
  `Multiplicative (ZMod N) × (ZMod N)ˣ ≃* (ZMod (N ^ 2))ˣ` of Claim 15.9.

## Main results

* `Cslib.Crypto.Paillier.coprime_totient`: Claim 15.7.
* `Cslib.Crypto.Paillier.one_add_pow`, `Cslib.Crypto.Paillier.one_add_pow_self`,
  `Cslib.Crypto.Paillier.orderOf_one_add`: Claim 15.8.
* `Cslib.Crypto.Paillier.coe_unitsEquiv_ofAdd`: Claim 15.9.
* `Cslib.Crypto.Paillier.one_add_pow_mul_pow_pow_totient`: the decryption identity.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Chapter 15,
  Proposition 15.6 and Claims 15.7, 15.8 and 15.9.
-/

@[expose] public section

namespace Cslib.Crypto.Paillier

/-! ### Claim 15.7 -/

/-- A positive number has less than twice the value of any number of the same bit length. -/
private theorem lt_two_mul_of_size_eq {p q : ℕ} (hp : 0 < p) (hsize : p.size = q.size) :
    q < 2 * p := by
  have hpos : 0 < p.size := Nat.size_pos.mpr hp
  have hlow : 2 ^ (p.size - 1) ≤ p := Nat.lt_size.mp (by lia)
  have hhigh : q < 2 ^ p.size := by
    rw [hsize]
    exact Nat.lt_size_self q
  have hpow : 2 ^ p.size = 2 * 2 ^ (p.size - 1) := by
    rw [← pow_succ']
    congr 1
    lia
  lia

/-- An odd prime `p` does not divide `q - 1` for an odd prime `q < 2 * p`. -/
private theorem coprime_sub_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : 2 < p)
    (hq2 : 2 < q) (hlt : q < 2 * p) : p.Coprime (q - 1) := by
  rw [hp.coprime_iff_not_dvd]
  rintro ⟨k, hk⟩
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by lia))
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by lia))
  rcases k with _ | _ | k
  · lia
  · lia
  · have : 2 * p ≤ p * (k + 1 + 1) := by nlinarith
    lia

/-- **Claim 15.7** ([KatzLindell2020]): for distinct odd primes `p` and `q` of the same bit
length, `p * q` is coprime to `φ(p * q) = (p - 1) * (q - 1)`. -/
theorem coprime_totient {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hp2 : 2 < p)
    (hq2 : 2 < q) (hsize : p.size = q.size) : (p * q).Coprime (p * q).totient := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hne), Nat.totient_prime hp,
    Nat.totient_prime hq]
  have hpp : p.Coprime (p - 1) := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have := Nat.le_of_dvd (by lia) hdvd
    lia
  have hqq : q.Coprime (q - 1) := by
    rw [hq.coprime_iff_not_dvd]
    intro hdvd
    have := Nat.le_of_dvd (by lia) hdvd
    lia
  have hpq := coprime_sub_one hp hq hp2 hq2 (lt_two_mul_of_size_eq hp.pos hsize)
  have hqp := coprime_sub_one hq hp hq2 hp2 (lt_two_mul_of_size_eq hq.pos hsize.symm)
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hpp hpq) (Nat.Coprime.mul_right hqp hqq)

/-! ### Claim 15.8 -/

/-- `N * N` vanishes modulo `N ^ 2`. -/
theorem natCast_mul_self (N : ℕ) : (N : ZMod (N ^ 2)) * N = 0 := by
  rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]

/-- **Claim 15.8** ([KatzLindell2020]), first part: `(1 + N) ^ a = 1 + a * N` in
`ZMod (N ^ 2)`. -/
theorem one_add_pow (N a : ℕ) : (1 + (N : ZMod (N ^ 2))) ^ a = 1 + (a : ZMod (N ^ 2)) * N := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ (1 + (N : ZMod (N ^ 2))) a, ih]
    push_cast
    linear_combination (a : ZMod (N ^ 2)) * natCast_mul_self N

/-- **Claim 15.8** ([KatzLindell2020]), second part: `(1 + N) ^ N = 1` in `ZMod (N ^ 2)`. -/
theorem one_add_pow_self (N : ℕ) : (1 + (N : ZMod (N ^ 2))) ^ N = 1 := by
  rw [one_add_pow, natCast_mul_self, add_zero]

/-- **Claim 15.8** ([KatzLindell2020]), third part: for positive `N`, the residue `1 + N` has
order exactly `N` in `ZMod (N ^ 2)`. -/
theorem orderOf_one_add {N : ℕ} (hN : 0 < N) : orderOf (1 + (N : ZMod (N ^ 2))) = N := by
  rw [orderOf_eq_iff hN]
  refine ⟨one_add_pow_self N, fun a ha ha0 h => ?_⟩
  rw [one_add_pow, add_eq_left, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, pow_two] at h
  have := Nat.le_of_dvd ha0 (Nat.dvd_of_mul_dvd_mul_right hN h)
  lia

/-! ### Claim 15.9 -/

/-- Adding a multiple of `N` does not change an `N`-th power in `ZMod (N ^ 2)`. -/
theorem add_mul_pow_self (N : ℕ) (v k : ZMod (N ^ 2)) :
    (v + (N : ZMod (N ^ 2)) * k) ^ N = v ^ N := by
  have hdvd := sq_dvd_add_pow_sub_sub ((N : ZMod (N ^ 2)) * k) v N
  have hN := natCast_mul_self N
  have hmid : v ^ (N - 1) * (N * k) * (N : ZMod (N ^ 2)) = 0 := by
    calc v ^ (N - 1) * (N * k) * (N : ZMod (N ^ 2))
        = v ^ (N - 1) * k * ((N : ZMod (N ^ 2)) * N) := by ring
      _ = 0 := by rw [hN, mul_zero]
  rw [mul_pow, pow_two (N : ZMod (N ^ 2)), hN, zero_mul, zero_dvd_iff, hmid, sub_zero,
    sub_eq_zero] at hdvd
  exact hdvd

/-- The `N`-th power of a natural number in `ZMod (N ^ 2)` depends only on its residue
modulo `N`. -/
theorem natCast_pow_self_mod (N m : ℕ) :
    (m : ZMod (N ^ 2)) ^ N = ((m % N : ℕ) : ZMod (N ^ 2)) ^ N := by
  conv_lhs => rw [← Nat.mod_add_div m N]
  rw [Nat.cast_add, Nat.cast_mul, add_mul_pow_self]

/-- The unit `1 + N` of `ZMod (N ^ 2)`. -/
def oneAddUnit (N : ℕ) [NeZero N] : (ZMod (N ^ 2))ˣ :=
  Units.ofPowEqOne _ N (one_add_pow_self N) (NeZero.ne N)

@[simp]
theorem coe_oneAddUnit (N : ℕ) [NeZero N] : (oneAddUnit N : ZMod (N ^ 2)) = 1 + N := rfl

/-- Powers of `1 + N` depend only on the exponent modulo `N`. -/
theorem oneAddUnit_pow_mod (N : ℕ) [NeZero N] (a : ℕ) :
    oneAddUnit N ^ a = oneAddUnit N ^ (a % N) :=
  pow_eq_pow_mod a (Units.pow_ofPowEqOne _ _)

/-- `a ↦ (1 + N) ^ a` on `ZMod N`, written multiplicatively. -/
def oneAddPowHom (N : ℕ) [NeZero N] : Multiplicative (ZMod N) →* (ZMod (N ^ 2))ˣ where
  toFun a := oneAddUnit N ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← oneAddUnit_pow_mod, pow_add]

@[simp]
theorem oneAddPowHom_apply (N : ℕ) [NeZero N] (a : Multiplicative (ZMod N)) :
    oneAddPowHom N a = oneAddUnit N ^ (Multiplicative.toAdd a).val := rfl

/-- A unit modulo `N`, read through its least representative, is a unit modulo `N ^ 2`. -/
def liftUnit (N : ℕ) (b : (ZMod N)ˣ) : (ZMod (N ^ 2))ˣ :=
  ZMod.unitOfCoprime (b : ZMod N).val (Nat.Coprime.pow_right 2 (ZMod.val_coe_unit_coprime b))

@[simp]
theorem coe_liftUnit (N : ℕ) (b : (ZMod N)ˣ) :
    (liftUnit N b : ZMod (N ^ 2)) = ((b : ZMod N).val : ZMod (N ^ 2)) := rfl

/-- `b ↦ b ^ N` from the units modulo `N` to the units modulo `N ^ 2`, through least
representatives. -/
def powSelfHom (N : ℕ) : (ZMod N)ˣ →* (ZMod (N ^ 2))ˣ where
  toFun b := liftUnit N b ^ N
  map_one' := by
    ext
    simp only [Units.val_pow_eq_pow_val, coe_liftUnit, Units.val_one, ZMod.val_one_eq_one_mod]
    rw [← natCast_pow_self_mod, Nat.cast_one, one_pow]
  map_mul' a b := by
    ext
    simp only [Units.val_pow_eq_pow_val, coe_liftUnit, Units.val_mul, ZMod.val_mul]
    rw [← natCast_pow_self_mod, Nat.cast_mul, mul_pow]

@[simp]
theorem powSelfHom_apply (N : ℕ) (b : (ZMod N)ˣ) :
    powSelfHom N b = liftUnit N b ^ N := rfl

/-- The image of `(a, b)` under `oneAddPowHom.coprod powSelfHom` is `(1 + N) ^ a * b ^ N`. -/
private theorem coe_coprod_ofAdd (N : ℕ) [NeZero N] (a : ZMod N) (b : (ZMod N)ˣ) :
    (((oneAddPowHom N).coprod (powSelfHom N) (Multiplicative.ofAdd a, b) : (ZMod (N ^ 2))ˣ) :
      ZMod (N ^ 2)) = (1 + N) ^ a.val * ((b : ZMod N).val : ZMod (N ^ 2)) ^ N := by
  simp only [MonoidHom.coprod_apply, oneAddPowHom_apply, powSelfHom_apply, toAdd_ofAdd,
    Units.val_mul, Units.val_pow_eq_pow_val, coe_oneAddUnit, coe_liftUnit]

/-- The totient of `N ^ 2` is `N * φ(N)`. -/
theorem totient_sq (N : ℕ) : (N ^ 2).totient = N * N.totient := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have key := Nat.totient_gcd_mul_totient_mul N N
  rw [Nat.gcd_self, ← pow_two N] at key
  have hpos : 0 < N.totient := Nat.totient_pos.mpr hN
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [key]; ring)

/-- When `gcd(N, φ(N)) = 1`, the map `(a, b) ↦ (1 + N) ^ a * b ^ N` is bijective. -/
theorem bijective_coprod (N : ℕ) [NeZero N] (hcop : N.Coprime N.totient) :
    Function.Bijective ((oneAddPowHom N).coprod (powSelfHom N)) := by
  have : NeZero (N ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne N)⟩
  have hinj : Function.Injective ((oneAddPowHom N).coprod (powSelfHom N)) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    -- Reducing modulo `N` kills `1 + N`, so `b ^ N = 1`, hence `b = 1` as `gcd(N, φ(N)) = 1`.
    have hval := congrArg Units.val hab
    have happ := coe_coprod_ofAdd N (Multiplicative.toAdd a) b
    simp only [ofAdd_toAdd] at happ
    rw [happ, Units.val_one] at hval
    have hcast := congrArg (ZMod.castHom (dvd_pow_self N two_ne_zero) (ZMod N)) hval
    simp only [map_mul, map_pow, map_add, map_one, map_natCast, ZMod.natCast_self, add_zero,
      one_pow, one_mul, ZMod.natCast_zmod_val] at hcast
    have hbN : b ^ N = 1 := Units.ext (by simpa using hcast)
    have hb : b = 1 := by
      have hdvdN : orderOf b ∣ N := orderOf_dvd_of_pow_eq_one hbN
      have hdvdT : orderOf b ∣ N.totient := by
        rw [← ZMod.card_units_eq_totient]
        exact orderOf_dvd_card
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdN hdvdT)
    subst hb
    -- Then `(1 + N) ^ a = 1`, and `1 + N` has order `N`, so `a = 0`.
    have ha : oneAddPowHom N a = 1 := by
      simpa only [MonoidHom.coprod_apply, map_one, mul_one] using hab
    have hpow : (1 + (N : ZMod (N ^ 2))) ^ (Multiplicative.toAdd a).val = 1 := by
      simpa only [oneAddPowHom_apply, Units.val_pow_eq_pow_val, coe_oneAddUnit,
        Units.val_one] using congrArg Units.val ha
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [orderOf_one_add (Nat.pos_of_ne_zero (NeZero.ne N))] at hdvd
    have hzero : (Multiplicative.toAdd a).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    rw [ZMod.val_eq_zero] at hzero
    have ha1 : a = 1 := hzero
    simp [ha1]
  have hcard : Fintype.card (Multiplicative (ZMod N) × (ZMod N)ˣ) =
      Fintype.card (ZMod (N ^ 2))ˣ := by
    rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, totient_sq,
      Fintype.card_congr Multiplicative.toAdd, ZMod.card]
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

/-- **Claim 15.9** ([KatzLindell2020]): when `gcd(N, φ(N)) = 1`, the map
`(a, b) ↦ (1 + N) ^ a * b ^ N` is a group isomorphism
`Multiplicative (ZMod N) × (ZMod N)ˣ ≃* (ZMod (N ^ 2))ˣ`. -/
noncomputable def unitsEquiv (N : ℕ) [NeZero N] (hcop : N.Coprime N.totient) :
    Multiplicative (ZMod N) × (ZMod N)ˣ ≃* (ZMod (N ^ 2))ˣ :=
  MulEquiv.ofBijective ((oneAddPowHom N).coprod (powSelfHom N)) (bijective_coprod N hcop)

/-- **Claim 15.9** ([KatzLindell2020]): `unitsEquiv` sends `(a, b)` to `(1 + N) ^ a * b ^ N`. -/
theorem coe_unitsEquiv_ofAdd (N : ℕ) [NeZero N] (hcop : N.Coprime N.totient) (a : ZMod N)
    (b : (ZMod N)ˣ) :
    ((unitsEquiv N hcop (Multiplicative.ofAdd a, b) : (ZMod (N ^ 2))ˣ) : ZMod (N ^ 2)) =
      (1 + N) ^ a.val * ((b : ZMod N).val : ZMod (N ^ 2)) ^ N :=
  coe_coprod_ofAdd N a b

/-! ### The decryption identity -/

/-- A natural number coprime to `N` has `N * φ(N)`-th power `1` modulo `N ^ 2`. -/
theorem natCast_pow_mul_totient {N r : ℕ} (hr : r.Coprime N) :
    (r : ZMod (N ^ 2)) ^ (N * N.totient) = 1 := by
  have hunit := ZMod.pow_totient (ZMod.unitOfCoprime r (Nat.Coprime.pow_right 2 hr))
  rw [totient_sq] at hunit
  simpa only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] using
    congrArg Units.val hunit

/-- **Decryption identity** ([KatzLindell2020], Construction 15.11): for `r` coprime to `N`,
raising `(1 + N) ^ m * r ^ N` to the power `φ(N)` gives `1 + m * φ(N) * N` in `ZMod (N ^ 2)`. -/
theorem one_add_pow_mul_pow_pow_totient {N r : ℕ} (m : ℕ) (hr : r.Coprime N) :
    ((1 + (N : ZMod (N ^ 2))) ^ m * (r : ZMod (N ^ 2)) ^ N) ^ N.totient =
      1 + ((m * N.totient : ℕ) : ZMod (N ^ 2)) * N := by
  rw [mul_pow, ← pow_mul, ← pow_mul, natCast_pow_mul_totient hr, mul_one, one_add_pow]

end Cslib.Crypto.Paillier
