/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.FieldTheory.Finite.BinaryField
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Foundations.Data.BitString.Binary
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Explicit binary fields defined by irreducible trinomials

For every `t : ℕ`, the cyclotomic polynomial `Φ_{3 ^ (t + 1)}(X)` over `𝔽₂ = ZMod 2` is the
explicit trinomial
`Cslib.trinomial t = X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1`.
Because `2` is a primitive root modulo `3 ^ (t + 1)` for every `t` (`orderOf 2 = 2 * 3 ^ t`),
`Cslib.trinomial t` is irreducible over `ZMod 2` (`Cslib.irreducible_trinomial`) [Lidl and
Niederreiter, Theorem 2.47][LidlNiederreiter1997].

Unlike `Cslib.BinaryField w`, whose modulus `Cslib.leastIrreducible w` is defined by an exhaustive
search over binary codes, `Cslib.TrinomialField t = AdjoinRoot (trinomial t)` has a closed-form
sparse modulus of degree `2 * 3 ^ t` for every `t : ℕ` without any runtime polynomial search.
Moreover, because `(X ^ (3 ^ t) + 1) * trinomial t = X ^ (3 ^ (t + 1)) + 1` over `ZMod 2`, any
binary polynomial of degree less than `4 * 3 ^ t` (whose binary code below `2 ^ (4 * 3 ^ t)` splits
into four `3 ^ t`-bit limbs, with the low two limbs kept together as a `2 * 3 ^ t`-bit word)
reduces modulo `trinomial t` in closed form using only bitwise shifts, masks, and exclusive-or
(`Cslib.reduceTrinomialCode`, `Cslib.mk_polyOfCode_reduceTrinomialCode`). Paired with carryless
multiplication `Cslib.clmul` (`Cslib.polyOfCode_clmul`), this gives loop-free arithmetic for
`Cslib.TrinomialField t` on unsigned machine words.

## Main definitions

* `Cslib.trinomial`: the binary trinomial `X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1`.
* `Cslib.clmul`: carryless multiplication of natural-number polynomial codes over `𝔽₂`.
* `Cslib.reduceTrinomialCode`: 4-limb bitwise reduction modulo `trinomial t` on natural-number
  codes below `2 ^ (4 * 3 ^ t)` (four `3 ^ t`-bit limbs).
* `Cslib.TrinomialField`: the explicit binary field `AdjoinRoot (trinomial t)` of degree
  `2 * 3 ^ t`.
* `Cslib.TrinomialField.basis`, `Cslib.TrinomialField.equivBits`,
  `Cslib.TrinomialField.equivFin`, `Cslib.TrinomialField.embed`,
  `Cslib.TrinomialField.embedFin`: power basis, coordinate equivalences with `BitString (2 * 3 ^ t)`
  and `Fin (2 ^ (2 * 3 ^ t))`, and embeddings of bit strings and bounded natural indices.

## Main results

* `Cslib.trinomial_eq_cyclotomic`, `Cslib.monic_trinomial`, `Cslib.natDegree_trinomial`,
  `Cslib.irreducible_trinomial`: `trinomial t` is the `3 ^ (t + 1)`-th cyclotomic polynomial over
  `ZMod 2`, monic of degree `2 * 3 ^ t`, and irreducible.
* `Cslib.coeff_polyOfCode`, `Cslib.polyOfCode_injective`, `Cslib.polyOfCode_xor`,
  `Cslib.polyOfCode_shiftLeft`, `Cslib.polyOfCode_eq_and_add_shiftRight`: bit-level correspondence
  between `polyOfCode` and bitwise operations on `ℕ`.
* `Cslib.polyOfCode_clmul`, `Cslib.clmul_lt_two_pow`: `clmul` computes polynomial multiplication
  over `ZMod 2` and respects bit-width bounds.
* `Cslib.reduceTrinomialCode_lt`, `Cslib.mk_polyOfCode_reduceTrinomialCode`: `reduceTrinomialCode`
  produces a `< 2 ^ (2 * 3 ^ t)` code congruent modulo `trinomial t`.
* `Cslib.TrinomialField.card`, `Cslib.TrinomialField.val_equivFin_add`,
  `Cslib.TrinomialField.val_equivFin_mul`: cardinality and unsigned-word arithmetic laws of
  `TrinomialField t`.

## References

* [R. Lidl, H. Niederreiter, *Finite Fields*, Section 2.4 and Chapter 3][LidlNiederreiter1997]
-/

public section

namespace Cslib

open BitString Module Polynomial

/-! ## Irreducibility of `X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1` over `ZMod 2` -/

/-- The binary trinomial `X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1` of degree `2 * 3 ^ t` over `ZMod 2`. -/
@[expose] noncomputable def trinomial (t : ℕ) : (ZMod 2)[X] :=
  X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1

/-- `trinomial t` is the `3 ^ (t + 1)`-th cyclotomic polynomial over `ZMod 2`. -/
theorem trinomial_eq_cyclotomic (t : ℕ) :
    trinomial t = cyclotomic (3 ^ (t + 1)) (ZMod 2) := by
  rw [cyclotomic_prime_pow_eq_geom_sum (R := ZMod 2) Nat.prime_three,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [trinomial, pow_zero, pow_one, ← pow_mul, mul_comm (3 ^ t) 2]
  ring

/-- `trinomial t` is monic for every `t : ℕ`. -/
theorem monic_trinomial (t : ℕ) : (trinomial t).Monic := by
  rw [trinomial_eq_cyclotomic]
  exact cyclotomic.monic (3 ^ (t + 1)) (ZMod 2)

/-- `trinomial t` has degree `2 * 3 ^ t`. -/
theorem natDegree_trinomial (t : ℕ) : (trinomial t).natDegree = 2 * 3 ^ t := by
  rw [trinomial_eq_cyclotomic, natDegree_cyclotomic,
    Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos t), Nat.succ_sub_one, mul_comm]

/-- In `(ZMod 2)[X]`, any polynomial added to itself vanishes. -/
private theorem zmod2_poly_add_self (p : (ZMod 2)[X]) : p + p = 0 := by
  ext i
  rw [coeff_add, coeff_zero]
  exact (by decide : ∀ c : ZMod 2, c + c = 0) (p.coeff i)

/-- Over `ZMod 2`, multiplying `trinomial t` by `X ^ (3 ^ t) + 1` yields `X ^ (3 ^ (t + 1)) + 1`. -/
theorem mul_trinomial_eq (t : ℕ) :
    (X ^ (3 ^ t) + 1) * trinomial t = X ^ (3 ^ (t + 1)) + 1 := by
  have h1 : (X ^ (3 ^ t) + 1) * trinomial t =
      (X ^ (3 * 3 ^ t) + 1) +
        ((X ^ (2 * 3 ^ t) + X ^ (3 ^ t)) + (X ^ (2 * 3 ^ t) + X ^ (3 ^ t))) := by
    unfold trinomial
    have hpow2 : X ^ (3 ^ t) * X ^ (3 ^ t) = (X : (ZMod 2)[X]) ^ (2 * 3 ^ t) := by
      rw [← pow_add, two_mul]
    have hpow3 : X ^ (3 ^ t) * X ^ (2 * 3 ^ t) = (X : (ZMod 2)[X]) ^ (3 * 3 ^ t) := by
      rw [← pow_add, show 3 ^ t + 2 * 3 ^ t = 3 * 3 ^ t by ring]
    calc (X ^ (3 ^ t) + 1) * (X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1)
        = X ^ (3 ^ t) * X ^ (2 * 3 ^ t) + X ^ (3 ^ t) * X ^ (3 ^ t) + X ^ (3 ^ t) +
            X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1 := by ring
      _ = (X ^ (3 * 3 ^ t) + 1) +
            ((X ^ (2 * 3 ^ t) + X ^ (3 ^ t)) + (X ^ (2 * 3 ^ t) + X ^ (3 ^ t))) := by
        rw [hpow2, hpow3]; ring
  rw [h1, zmod2_poly_add_self, add_zero, pow_succ', mul_comm 3 (3 ^ t)]

/-- In `ZMod 3`, `2 ^ (3 ^ t) = 2` for every `t : ℕ`. -/
private theorem zmod3_two_pow_three_pow (t : ℕ) : (2 : ZMod 3) ^ (3 ^ t) = 2 := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [pow_succ, pow_mul, ih]
    decide

/-- In `ZMod (3 ^ (t + 1))`, `2 ^ (3 ^ t) ≠ 1`. -/
private theorem zmod_three_pow_two_pow_ne_one (t : ℕ) :
    (2 : ZMod (3 ^ (t + 1))) ^ (3 ^ t) ≠ 1 := by
  intro h
  have hdvd : 3 ∣ 3 ^ (t + 1) := dvd_pow_self 3 (Nat.succ_ne_zero t)
  have hcast := congrArg (ZMod.castHom hdvd (ZMod 3)) h
  simp only [map_pow, map_ofNat, map_one] at hcast
  rw [zmod3_two_pow_three_pow] at hcast
  revert hcast
  decide

/-- The multiplicative order of `2` modulo `3 ^ (t + 1)` is `2 * 3 ^ t`. -/
theorem orderOf_two_zmod_three_pow (t : ℕ) :
    orderOf (2 : ZMod (3 ^ (t + 1))) = 2 * 3 ^ t := by
  have h4 : orderOf (4 : ZMod (3 ^ (t + 1))) = 3 ^ t := by
    simpa [show (1 + 3 : ZMod (3 ^ (t + 1))) = 4 by ring] using
      ZMod.orderOf_one_add_prime Nat.prime_three (by decide) t
  have hsq : (4 : ZMod (3 ^ (t + 1))) = (2 : ZMod (3 ^ (t + 1))) ^ 2 := by ring
  rw [hsq, orderOf_pow' (2 : ZMod (3 ^ (t + 1))) (by decide)] at h4
  set d := orderOf (2 : ZMod (3 ^ (t + 1)))
  have hgd_dvd : d.gcd 2 ∣ 2 := Nat.gcd_dvd_right d 2
  have hgd_le : d.gcd 2 ≤ 2 := Nat.le_of_dvd (by decide) hgd_dvd
  have hgd_pos : 0 < d.gcd 2 := Nat.gcd_pos_of_pos_right d (by decide)
  have h_mul : d = 3 ^ t * d.gcd 2 :=
    (Nat.div_eq_iff_eq_mul_left hgd_pos (Nat.gcd_dvd_left d 2)).mp h4
  rcases ( by omega : d.gcd 2 = 1 ∨ d.gcd 2 = 2 ) with h1 | h2
  · rw [h1, mul_one] at h_mul
    exfalso
    apply zmod_three_pow_two_pow_ne_one t
    rw [← h_mul]
    exact pow_orderOf_eq_one (2 : ZMod (3 ^ (t + 1)))
  · rw [h_mul, h2, mul_comm]

/-- **`trinomial t` is irreducible over `ZMod 2` for every `t : ℕ`**
[Lidl and Niederreiter, Theorem 2.47][LidlNiederreiter1997]. -/
theorem irreducible_trinomial (t : ℕ) : Irreducible (trinomial t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hndvd : ¬ 2 ∣ 3 ^ (t + 1) := by
    intro hdvd
    have h23 : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow hdvd
    omega
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree hndvd ?_ ?_
  · exact ⟨1, by rw [← trinomial_eq_cyclotomic, mul_one]⟩
  · rw [natDegree_trinomial]
    have hunit : orderOf (ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hndvd)) =
        orderOf (2 : ZMod (3 ^ (t + 1))) := by
      rw [← orderOf_injective (Units.coeHom (ZMod (3 ^ (t + 1)))) Units.coeHom_injective]
      rfl
    rw [hunit, orderOf_two_zmod_three_pow]

/-! ## Bitwise operations, carryless multiplication, and 4-limb reduction on `polyOfCode` -/

/-- Unfolding `polyOfCode m` into its constant term `m : ZMod 2` and `X * polyOfCode (m / 2)`. -/
theorem polyOfCode_eq_C_add_X_mul (m : ℕ) :
    polyOfCode m = C (m : ZMod 2) + X * polyOfCode (m / 2) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [polyOfCode_zero]
  · rw [polyOfCode, ite_eq_right hm]

/-- Helper characterizing `(m : ZMod 2)` from `m % 2`. -/
private theorem natCast_zmod_two_eq (m : ℕ) :
    (m : ZMod 2) = if m % 2 = 1 then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · have hm : (m : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff m 2).mpr (Nat.dvd_of_mod_eq_zero h0)
    simp [h0, hm]
  · have hm : (m : ZMod 2) = 1 := by
      rw [← Nat.div_add_mod m 2, h1, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
        zero_mul, zero_add, Nat.cast_one]
    simp [h1, hm]

/-- Coefficient `i` of `polyOfCode m` is bit `i` of `m` read in `ZMod 2`. -/
theorem coeff_polyOfCode (m i : ℕ) :
    (polyOfCode m).coeff i = bitEquiv.symm (m.testBit i) := by
  induction i generalizing m with
  | zero =>
    rw [polyOfCode_eq_C_add_X_mul]
    simp only [coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero, Nat.testBit_zero,
      natCast_zmod_two_eq]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
  | succ i ih =>
    rw [polyOfCode_eq_C_add_X_mul, coeff_add, coeff_C_succ, zero_add, coeff_X_mul,
      ih (m / 2), Nat.testBit_succ]

/-- `polyOfCode` is injective: distinct natural numbers have distinct binary polynomials. -/
theorem polyOfCode_injective : Function.Injective polyOfCode := by
  intro a b hab
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun p : (ZMod 2)[X] => bitEquiv (p.coeff i)) hab
  simpa [coeff_polyOfCode] using hi

/-- If `m < 2 ^ k`, then `polyOfCode m` has degree strictly less than `k`. -/
theorem degree_polyOfCode_lt {m k : ℕ} (hm : m < 2 ^ k) :
    (polyOfCode m).degree < k := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp only [polyOfCode_zero, degree_zero]
    exact WithBot.bot_lt_coe k
  · have hne : polyOfCode m ≠ 0 := (polyOfCode_ne_zero_and_natDegree hm0).1
    rw [degree_eq_natDegree hne, natDegree_polyOfCode hm0, Nat.cast_lt]
    exact Nat.log_lt_of_lt_pow hm0 hm

/-- Bitwise exclusive-or on codes corresponds to polynomial addition over `ZMod 2`. -/
@[simp]
theorem polyOfCode_xor (a b : ℕ) :
    polyOfCode (a ^^^ b) = polyOfCode a + polyOfCode b := by
  ext i
  rw [coeff_add, coeff_polyOfCode, coeff_polyOfCode, coeff_polyOfCode, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

/-- Left-shifting a code by `k` bits multiplies its polynomial by `X ^ k`. -/
@[simp]
theorem polyOfCode_shiftLeft (a k : ℕ) :
    polyOfCode (a <<< k) = X ^ k * polyOfCode a := by
  ext i
  rw [coeff_polyOfCode, coeff_X_pow_mul', Nat.testBit_shiftLeft]
  by_cases hik : k ≤ i
  · simp [hik, coeff_polyOfCode]
  · simp [hik]

/-- Splitting a code at bit `k` into its low `k` bits (`a &&& (2 ^ k - 1)`) and high bits
(`a >>> k`). -/
theorem polyOfCode_eq_and_add_shiftRight (a k : ℕ) :
    polyOfCode a = polyOfCode (a &&& (2 ^ k - 1)) + X ^ k * polyOfCode (a >>> k) := by
  ext i
  rw [coeff_add, coeff_X_pow_mul', coeff_polyOfCode, coeff_polyOfCode,
    Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hik : k ≤ i
  · have hlt : ¬ i < k := not_lt.mpr hik
    simp [hik, hlt, coeff_polyOfCode, Nat.testBit_shiftRight, Nat.add_sub_of_le hik]
  · have hlt : i < k := lt_of_not_ge hik
    simp [hik, hlt]

/-- Carryless multiplication of natural-number polynomial codes over `ZMod 2`. -/
@[expose] def clmul (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else (if b % 2 = 1 then a else 0) ^^^ (clmul a (b / 2) <<< 1)
decreasing_by omega

/-- Carryless multiplication by `0` on the right is `0`. -/
@[simp]
theorem clmul_zero_right (a : ℕ) : clmul a 0 = 0 := by
  rw [clmul, ite_eq_left rfl]

/-- Step equation for `clmul` in terms of bitwise shift and mask. -/
theorem clmul_step (a b : ℕ) :
    clmul a b = (if b &&& 1 = 1 then a else 0) ^^^ (clmul a (b >>> 1) <<< 1) := by
  have hand : b &&& 1 = b % 2 := Nat.and_two_pow_sub_one_eq_mod b 1
  have hshr : b >>> 1 = b / 2 := Nat.shiftRight_eq_div_pow b 1
  rw [hand, hshr]
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · rw [clmul, ite_eq_right hb]

/-- **`clmul` computes polynomial multiplication over `ZMod 2`**. -/
@[simp]
theorem polyOfCode_clmul (a b : ℕ) :
    polyOfCode (clmul a b) = polyOfCode a * polyOfCode b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · rw [clmul, ite_eq_right hb, polyOfCode_xor, polyOfCode_shiftLeft, pow_one,
        ih (b / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hb) one_lt_two)]
      conv_rhs => rw [polyOfCode_eq_C_add_X_mul b]
      have hbit : polyOfCode (if b % 2 = 1 then a else 0) = polyOfCode a * C (b : ZMod 2) := by
        rw [natCast_zmod_two_eq]
        split_ifs <;> simp
      rw [hbit]
      ring

/-- Carryless multiplication by `0` on the left is `0`. -/
@[simp]
theorem clmul_zero_left (b : ℕ) : clmul 0 b = 0 :=
  polyOfCode_injective (by simp)

/-- Carryless multiplication is commutative. -/
theorem clmul_comm (a b : ℕ) : clmul a b = clmul b a :=
  polyOfCode_injective (by simp [mul_comm])

/-- Carryless multiplication distributes over `^^^` on the left. -/
theorem clmul_xor_left (a b c : ℕ) : clmul (a ^^^ b) c = clmul a c ^^^ clmul b c :=
  polyOfCode_injective (by simp [add_mul])

/-- Carryless multiplication distributes over `^^^` on the right. -/
theorem clmul_xor_right (a b c : ℕ) : clmul a (b ^^^ c) = clmul a b ^^^ clmul a c :=
  polyOfCode_injective (by simp [mul_add])

/-- Carryless multiplication commutes with left shifts on the left. -/
theorem clmul_shiftLeft_left (a b k : ℕ) : clmul (a <<< k) b = clmul a b <<< k :=
  polyOfCode_injective (by simp [mul_assoc])

/-- Carryless multiplication commutes with left shifts on the right. -/
theorem clmul_shiftLeft_right (a b k : ℕ) : clmul a (b <<< k) = clmul a b <<< k :=
  polyOfCode_injective (by simp [mul_left_comm])

/-- If `a < 2 ^ m` and `b < 2 ^ n`, then `clmul a b < 2 ^ (m + n)`. -/
theorem clmul_lt_two_pow {a b m n : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ n) :
    clmul a b < 2 ^ (m + n) := by
  induction n generalizing b with
  | zero =>
    have hb0 : b = 0 := by omega
    subst hb0
    simp only [clmul_zero_right, add_zero]
    positivity
  | succ n ih =>
    rcases eq_or_ne b 0 with rfl | hb0
    · simp only [clmul_zero_right]
      positivity
    · rw [clmul, ite_eq_right hb0]
      have hdiv : b / 2 < 2 ^ n := by
        rw [pow_succ] at hb
        omega
      have hrec := ih hdiv
      have hsh : clmul a (b / 2) <<< 1 < 2 ^ (m + (n + 1)) := by
        rw [Nat.shiftLeft_eq, pow_one, ← add_assoc, pow_succ]
        omega
      have hlow : (if b % 2 = 1 then a else 0) < 2 ^ (m + (n + 1)) := by
        have hle : 2 ^ m ≤ 2 ^ (m + (n + 1)) :=
          Nat.pow_le_pow_right two_pos (Nat.le_add_right m (n + 1))
        split_ifs <;> omega
      exact Nat.xor_lt_two_pow hlow hsh

/-- If `a < 2 ^ q` and `b < 2 ^ q`, then `clmul a b < 2 ^ (2 * q)`. -/
theorem clmul_lt_two_pow_two_mul {a b q : ℕ} (ha : a < 2 ^ q) (hb : b < 2 ^ q) :
    clmul a b < 2 ^ (2 * q) := by
  rw [two_mul]
  exact clmul_lt_two_pow ha hb

/-- **8-operation loop-free 4-limb reduction modulo `trinomial t`**:
viewing a code `c < 2 ^ (4 * 3 ^ t)` as four `3 ^ t`-bit limbs (with the low two limbs kept
together as `cLow`), reduces `c` to a code `< 2 ^ (2 * 3 ^ t)` representing the same element of
`AdjoinRoot (trinomial t)`. -/
@[expose] def reduceTrinomialCode (t c : ℕ) : ℕ :=
  let r := 3 ^ t
  let c3 := c >>> (3 * r)
  let c2 := (c >>> (2 * r)) &&& (2 ^ r - 1)
  let cLow := c &&& (2 ^ (2 * r) - 1)
  ((cLow ^^^ c3) ^^^ c2) ^^^ (c2 <<< r)

/-- For `c < 2 ^ (4 * 3 ^ t)`, `reduceTrinomialCode t c < 2 ^ (2 * 3 ^ t)`. -/
theorem reduceTrinomialCode_lt (t : ℕ) {c : ℕ} (hc : c < 2 ^ (4 * 3 ^ t)) :
    reduceTrinomialCode t c < 2 ^ (2 * 3 ^ t) := by
  dsimp only [reduceTrinomialCode]
  set r := 3 ^ t
  have hr_le : 2 ^ r ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right two_pos (by omega)
  have hcLow : c &&& (2 ^ (2 * r) - 1) < 2 ^ (2 * r) := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt c (by positivity)
  have hc3 : c >>> (3 * r) < 2 ^ (2 * r) := by
    rw [Nat.shiftRight_eq_div_pow]
    have hlt : c / 2 ^ (3 * r) < 2 ^ r := by
      apply Nat.div_lt_of_lt_mul
      rwa [← pow_add, show 3 * r + r = 4 * r by omega]
    exact hlt.trans_le hr_le
  have hc2_r : (c >>> (2 * r)) &&& (2 ^ r - 1) < 2 ^ r := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  have hc2 : (c >>> (2 * r)) &&& (2 ^ r - 1) < 2 ^ (2 * r) := hc2_r.trans_le hr_le
  have hc2_sh : ((c >>> (2 * r)) &&& (2 ^ r - 1)) <<< r < 2 ^ (2 * r) := by
    have hpow : 2 ^ (2 * r) = 2 ^ r * 2 ^ r := by rw [two_mul, pow_add]
    rw [Nat.shiftLeft_eq, hpow]
    exact Nat.mul_lt_mul_of_pos_right hc2_r (by positivity)
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hcLow hc3) hc2) hc2_sh

/-- **`reduceTrinomialCode t c` is congruent to `c` modulo `trinomial t` for every `c : ℕ`**. -/
theorem mk_polyOfCode_reduceTrinomialCode (t c : ℕ) :
    AdjoinRoot.mk (trinomial t) (polyOfCode (reduceTrinomialCode t c)) =
      AdjoinRoot.mk (trinomial t) (polyOfCode c) := by
  set r := 3 ^ t
  set c3 := c >>> (3 * r)
  set c2 := (c >>> (2 * r)) &&& (2 ^ r - 1)
  set cLow := c &&& (2 ^ (2 * r) - 1)
  have hsplit1 : polyOfCode c = polyOfCode cLow + X ^ (2 * r) * polyOfCode (c >>> (2 * r)) :=
    polyOfCode_eq_and_add_shiftRight c (2 * r)
  have hsplit2 : polyOfCode (c >>> (2 * r)) = polyOfCode c2 + X ^ r * polyOfCode c3 := by
    have h := polyOfCode_eq_and_add_shiftRight (c >>> (2 * r)) r
    rwa [← Nat.shiftRight_add, show 2 * r + r = 3 * r by omega] at h
  have hred : polyOfCode (reduceTrinomialCode t c) =
      polyOfCode cLow + polyOfCode c3 + polyOfCode c2 + X ^ r * polyOfCode c2 := by
    change polyOfCode (((cLow ^^^ c3) ^^^ c2) ^^^ (c2 <<< r)) = _
    simp only [polyOfCode_xor, polyOfCode_shiftLeft]
  have hdiff : polyOfCode c =
      polyOfCode (reduceTrinomialCode t c) +
        (polyOfCode c2 + (X ^ r + 1) * polyOfCode c3) * trinomial t := by
    rw [hsplit1, hsplit2, hred]
    have htri : trinomial t = X ^ (2 * r) + X ^ r + 1 := rfl
    have hrr : (X : (ZMod 2)[X]) ^ r * X ^ r = X ^ (2 * r) := by
      rw [← pow_add, two_mul]
    set P0 := polyOfCode cLow
    set P2 := polyOfCode c2
    set P3 := polyOfCode c3
    set Xr : (ZMod 2)[X] := X ^ r
    have halg :
        P0 + P3 + P2 + Xr * P2 + (P2 + (Xr + 1) * P3) * (Xr * Xr + Xr + 1) =
          P0 + (Xr * Xr) * (P2 + Xr * P3) +
            ((P2 + Xr * P2 + P3 + Xr * P3 + Xr * Xr * P3) +
              (P2 + Xr * P2 + P3 + Xr * P3 + Xr * Xr * P3)) := by
      ring
    rw [htri, ← hrr, halg, zmod2_poly_add_self, add_zero]
  rw [hdiff, map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero]

/-! ## The explicit trinomial field `TrinomialField t` -/

/-- **The explicit binary field of degree `2 * 3 ^ t`**: binary polynomials modulo `trinomial t`. -/
abbrev TrinomialField (t : ℕ) : Type := AdjoinRoot (trinomial t)

namespace TrinomialField

/-- Degree `2 * 3 ^ t` is always positive. -/
theorem deg_ne_zero (t : ℕ) : 2 * 3 ^ t ≠ 0 := by positivity

/-- The modulus `trinomial t` is irreducible, so the quotient is a field. -/
instance (t : ℕ) : Fact (Irreducible (trinomial t)) :=
  ⟨irreducible_trinomial t⟩

/-- `TrinomialField t` is a field. -/
noncomputable instance (t : ℕ) : Field (TrinomialField t) := AdjoinRoot.instField

/-- `TrinomialField t` is finite, through its coordinates in the power basis. -/
noncomputable instance (t : ℕ) : Fintype (TrinomialField t) :=
  Fintype.ofEquiv _
    (AdjoinRoot.powerBasisAux' (monic_trinomial t)).equivFun.toEquiv.symm

/-- Equality in `TrinomialField t`, decided classically. -/
noncomputable instance (t : ℕ) : DecidableEq (TrinomialField t) := Classical.decEq _

/-- `TrinomialField t` has characteristic two. -/
instance (t : ℕ) : CharP (TrinomialField t) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (TrinomialField t)).injective 2

/-- **The power basis** `1, α, …, α ^ (2 * 3 ^ t - 1)` at the root `α` of `trinomial t`. -/
noncomputable def basis (t : ℕ) : Module.Basis (Fin (2 * 3 ^ t)) (ZMod 2) (TrinomialField t) :=
  (AdjoinRoot.powerBasisAux' (monic_trinomial t)).reindex
    (finCongr (natDegree_trinomial t))

/-- Basis vector `i` is the power `α ^ i` of the root. -/
theorem basis_apply (t : ℕ) (i : Fin (2 * 3 ^ t)) :
    basis t i = AdjoinRoot.root (trinomial t) ^ (i : ℕ) := by
  rw [basis, Module.Basis.reindex_apply]
  exact (AdjoinRoot.powerBasis' (monic_trinomial t)).basis_eq_pow
    ((finCongr (natDegree_trinomial t)).symm i)

/-- **The encoding by bits**: the `2 * 3 ^ t` coordinates in the power basis as an additive
equivalence `TrinomialField t ≃+ BitString (2 * 3 ^ t)`. -/
noncomputable def equivBits (t : ℕ) : TrinomialField t ≃+ BitString (2 * 3 ^ t) :=
  (basis t).equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => bitEquiv.toAddEquiv)

/-- Bit `j` of an element is its coordinate `j` in the power basis. -/
theorem equivBits_apply (t : ℕ) (x : TrinomialField t) (j : Fin (2 * 3 ^ t)) :
    equivBits t x j = bitEquiv ((basis t).repr x j) := by
  rfl

/-- The element with given bits is the combination of the basis vectors selected by the bits. -/
theorem equivBits_symm_apply (t : ℕ) (v : BitString (2 * 3 ^ t)) :
    (equivBits t).symm v = ∑ j, bitEquiv.symm (v j) • basis t j := by
  simp [equivBits, Module.Basis.equivFun_symm_apply]

/-- **`TrinomialField t` has `2 ^ (2 * 3 ^ t)` elements.** -/
theorem card (t : ℕ) : Fintype.card (TrinomialField t) = 2 ^ (2 * 3 ^ t) := by
  rw [Fintype.card_congr (equivBits t).toEquiv, BitString.card]

/-- The encoding of the class of a binary polynomial of degree less than `2 * 3 ^ t` is its list
of coefficients. -/
theorem equivBits_mk (t : ℕ) {p : (ZMod 2)[X]} (hp : p.degree < (2 * 3 ^ t : ℕ))
    (j : Fin (2 * 3 ^ t)) :
    equivBits t (AdjoinRoot.mk (trinomial t) p) j = bitEquiv (p.coeff j) := by
  have hdeg : p.degree < (trinomial t).degree := by
    rw [degree_eq_natDegree (irreducible_trinomial t).ne_zero, natDegree_trinomial]
    exact hp
  rw [equivBits_apply, basis, Module.Basis.repr_reindex_apply,
    AdjoinRoot.powerBasisAux'_repr_apply_to_fun, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (monic_trinomial t)).2 hdeg]
  rfl

/-- **Numbering of `TrinomialField t` by `Fin (2 ^ (2 * 3 ^ t))`** via its power-basis bits. -/
@[expose] noncomputable def equivFin (t : ℕ) : TrinomialField t ≃ Fin (2 ^ (2 * 3 ^ t)) :=
  (equivBits t).toEquiv.trans (BitString.equivFin (2 * 3 ^ t))

/-- For `c < 2 ^ (2 * 3 ^ t)`, the `equivFin t` coordinate of
`AdjoinRoot.mk (trinomial t) (polyOfCode c)` is `c`. -/
theorem val_equivFin_mk_polyOfCode (t : ℕ) {c : ℕ} (hc : c < 2 ^ (2 * 3 ^ t)) :
    (equivFin t (AdjoinRoot.mk (trinomial t) (polyOfCode c))).val = c := by
  have hbits : equivBits t (AdjoinRoot.mk (trinomial t) (polyOfCode c)) =
      (BitString.equivFin (2 * 3 ^ t)).symm ⟨c, hc⟩ := by
    ext j
    rw [equivBits_mk t (degree_polyOfCode_lt hc) j, coeff_polyOfCode, RingEquiv.apply_symm_apply,
      BitString.equivFin_symm_apply]
  change (BitString.equivFin (2 * 3 ^ t)
    (equivBits t (AdjoinRoot.mk (trinomial t) (polyOfCode c)))).val = c
  rw [hbits, Equiv.apply_symm_apply]

/-- The inverse of `equivFin t` sends `m : Fin (2 ^ (2 * 3 ^ t))` to
`AdjoinRoot.mk (trinomial t) (polyOfCode m.val)`. -/
theorem equivFin_symm_eq_mk_polyOfCode (t : ℕ) (m : Fin (2 ^ (2 * 3 ^ t))) :
    (equivFin t).symm m = AdjoinRoot.mk (trinomial t) (polyOfCode m.val) := by
  apply (equivFin t).injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (val_equivFin_mk_polyOfCode t m.isLt).symm

/-- Every `x : TrinomialField t` is the class of `polyOfCode (equivFin t x).val`. -/
theorem mk_polyOfCode_val_equivFin (t : ℕ) (x : TrinomialField t) :
    AdjoinRoot.mk (trinomial t) (polyOfCode (equivFin t x).val) = x := by
  rw [← equivFin_symm_eq_mk_polyOfCode, Equiv.symm_apply_apply]

/-- Addition in `TrinomialField t` corresponds to bitwise exclusive-or (`^^^`) on `equivFin t`
coordinates. -/
theorem val_equivFin_add (t : ℕ) (x y : TrinomialField t) :
    (equivFin t (x + y)).val = (equivFin t x).val ^^^ (equivFin t y).val := by
  have hxy : (equivFin t x).val ^^^ (equivFin t y).val < 2 ^ (2 * 3 ^ t) :=
    Nat.xor_lt_two_pow (equivFin t x).isLt (equivFin t y).isLt
  conv_lhs => rw [← mk_polyOfCode_val_equivFin t x, ← mk_polyOfCode_val_equivFin t y]
  rw [← map_add, ← polyOfCode_xor, val_equivFin_mk_polyOfCode t hxy]

/-- Multiplication in `TrinomialField t` corresponds to carryless multiplication `clmul` followed
by 4-limb reduction `reduceTrinomialCode` on `equivFin t` coordinates. -/
theorem val_equivFin_mul (t : ℕ) (x y : TrinomialField t) :
    (equivFin t (x * y)).val =
      reduceTrinomialCode t (clmul (equivFin t x).val (equivFin t y).val) := by
  have hcl : clmul (equivFin t x).val (equivFin t y).val < 2 ^ (4 * 3 ^ t) := by
    rw [show 4 * 3 ^ t = 2 * (2 * 3 ^ t) by ring]
    exact clmul_lt_two_pow_two_mul (equivFin t x).isLt (equivFin t y).isLt
  have hred : reduceTrinomialCode t (clmul (equivFin t x).val (equivFin t y).val) <
      2 ^ (2 * 3 ^ t) :=
    reduceTrinomialCode_lt t hcl
  conv_lhs => rw [← mk_polyOfCode_val_equivFin t x, ← mk_polyOfCode_val_equivFin t y]
  rw [← map_mul, ← polyOfCode_clmul, ← mk_polyOfCode_reduceTrinomialCode,
    val_equivFin_mk_polyOfCode t hred]

/-- **The embedding of bit strings of length `b ≤ 2 * 3 ^ t`** into `TrinomialField t`. -/
@[expose] noncomputable def embed {t b : ℕ} (hb : b ≤ 2 * 3 ^ t) :
    BitString b ↪ TrinomialField t where
  toFun a := (equivBits t).symm (BitString.zeroExtend a)
  inj' _ _ h := BitString.zeroExtend_injective hb ((equivBits t).symm.injective h)

/-- **The embedding of keys `Fin U` (`U ≤ 2 ^ (2 * 3 ^ t)`)** into `TrinomialField t`. -/
@[expose] noncomputable def embedFin {t U : ℕ} (hU : U ≤ 2 ^ (2 * 3 ^ t)) :
    Fin U ↪ TrinomialField t where
  toFun u := (equivFin t).symm (Fin.castLE hU u)
  inj' := (equivFin t).symm.injective.comp (Fin.castLE_injective hU)

/-- Applying `embedFin hU` to `u : Fin U` gives `AdjoinRoot.mk (trinomial t) (polyOfCode u.val)`. -/
theorem embedFin_apply {t U : ℕ} (hU : U ≤ 2 ^ (2 * 3 ^ t)) (u : Fin U) :
    embedFin hU u = AdjoinRoot.mk (trinomial t) (polyOfCode u.val) :=
  equivFin_symm_eq_mk_polyOfCode t (Fin.castLE hU u)

end TrinomialField

end Cslib
