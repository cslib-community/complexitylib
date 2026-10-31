/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.NumberTheory.AKS.Criterion

/-!
# Coefficient arithmetic modulo `X^r - 1` and `n`

An element of `(ℤ / n)[X] / (X^r - 1)` is represented by the `r` coefficients of its reduced
polynomial, as natural numbers below `n`. This file gives the coefficient formulas that a program
evaluates and identifies them with the ring operations: `Cslib.AKS.toQuot n r c` is the class of
`∑_{i < r} c i X^i`, products of classes have the coefficients `Cslib.AKS.mulCoeff`
(`Cslib.AKS.toQuot_mulCoeff`), the classes of `X^e + a` have the coefficients
`Cslib.AKS.powAddCoeff` (`Cslib.AKS.toQuot_powAddCoeff`), and reduced coefficient vectors
determine their classes (`Cslib.AKS.toQuot_eq_toQuot_iff`). In particular the AKS congruence
holds exactly when the `n`-th power of the class of `X + a` has the coefficients of `X^n + a`
(`Cslib.AKS.congruence_iff_toQuot`).

## Main definitions

* `Cslib.AKS.coeffPoly`, `Cslib.AKS.toQuot`: the polynomial with given coefficients and its class.
* `Cslib.AKS.mulCoeff`: the coefficients of a product.
* `Cslib.AKS.powAddCoeff`: the coefficients of `X^e + a`.

## Main results

* `Cslib.AKS.toQuot_mulCoeff`: coefficients of products.
* `Cslib.AKS.toQuot_powAddCoeff`: coefficients of `X^e + a`.
* `Cslib.AKS.toQuot_eq_toQuot_iff`: reduced coefficients determine their class.
* `Cslib.AKS.congruence_iff_toQuot`: the AKS congruence in coefficients.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.AKS

open Polynomial Finset

variable {n r : ℕ}

/-- The polynomial `∑_{i < r} c i X^i` over `ℤ / n`. -/
noncomputable def coeffPoly (n r : ℕ) (c : ℕ → ℕ) : (ZMod n)[X] :=
  ∑ i ∈ range r, C (c i : ZMod n) * X ^ i

/-- The class of `∑_{i < r} c i X^i` in `(ℤ / n)[X] / (X^r - 1)`. -/
noncomputable def toQuot (n r : ℕ) (c : ℕ → ℕ) : AdjoinRoot (X ^ r - 1 : (ZMod n)[X]) :=
  AdjoinRoot.mk _ (coeffPoly n r c)

/-- The coefficients of the product of the classes of `p` and `q`, reduced modulo `n`:
`∑_{(i + j) mod r = k} p i q j mod n`. -/
def mulCoeff (n r : ℕ) (p q : ℕ → ℕ) (k : ℕ) : ℕ :=
  (∑ i ∈ range r, ∑ j ∈ range r, if (i + j) % r = k then p i * q j else 0) % n

/-- The coefficients of `X^e + a`, reduced modulo `X^r - 1` and `n`. -/
def powAddCoeff (n r e a : ℕ) (k : ℕ) : ℕ :=
  ((if k = e % r then 1 else 0) + (if k = 0 then a else 0)) % n

/-- The root of `X^r - 1` is an `r`-th root of unity. -/
theorem root_pow_self (n r : ℕ) : AdjoinRoot.root (X ^ r - 1 : (ZMod n)[X]) ^ r = 1 := by
  have h := AdjoinRoot.mk_self (f := (X ^ r - 1 : (ZMod n)[X]))
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h
  exact h

/-- Powers of the root depend only on the exponent modulo `r`. -/
theorem root_pow_mod (n r m : ℕ) :
    AdjoinRoot.root (X ^ r - 1 : (ZMod n)[X]) ^ (m % r) =
      AdjoinRoot.root (X ^ r - 1 : (ZMod n)[X]) ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m r, pow_add, pow_mul, root_pow_self, one_pow, mul_one]

/-- Natural numbers in `(ℤ / n)[X] / (X^r - 1)` depend only on their residue modulo `n`. -/
theorem natCast_mod (n r m : ℕ) :
    (((m % n : ℕ)) : AdjoinRoot (X ^ r - 1 : (ZMod n)[X])) = m := by
  have h : ((n : ℕ) : AdjoinRoot (X ^ r - 1 : (ZMod n)[X])) = 0 := by
    rw [← map_natCast (AdjoinRoot.of (X ^ r - 1 : (ZMod n)[X])), ZMod.natCast_self, map_zero]
  conv_rhs => rw [← Nat.mod_add_div m n]
  rw [Nat.cast_add, Nat.cast_mul, h, zero_mul, add_zero]

/-- The class of `∑_{i < r} c i X^i` as a sum of powers of the root. -/
theorem toQuot_eq_sum (n r : ℕ) (c : ℕ → ℕ) :
    toQuot n r c = ∑ i ∈ range r,
      (c i : AdjoinRoot (X ^ r - 1 : (ZMod n)[X])) * AdjoinRoot.root _ ^ i := by
  simp only [toQuot, coeffPoly, map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rfl

/-- **Coefficients of products.** -/
theorem toQuot_mulCoeff (n r : ℕ) (p q : ℕ → ℕ) :
    toQuot n r (mulCoeff n r p q) = toQuot n r p * toQuot n r q := by
  set ξ := AdjoinRoot.root (X ^ r - 1 : (ZMod n)[X])
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [toQuot_eq_sum]
  rw [toQuot_eq_sum, toQuot_eq_sum, toQuot_eq_sum, sum_mul_sum]
  simp only [mulCoeff, natCast_mod, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero,
    sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_ite_eq (range r) ((i + j) % r)]
  simp only [mem_range, Nat.mod_lt _ hr, ↓reduceIte]
  rw [root_pow_mod, pow_add]
  ring

/-- **Coefficients of `X^e + a`.** -/
theorem toQuot_powAddCoeff (hr : 0 < r) (e a : ℕ) :
    toQuot n r (powAddCoeff n r e a) =
      AdjoinRoot.mk (X ^ r - 1 : (ZMod n)[X]) (X ^ e + C (a : ZMod n)) := by
  rw [toQuot_eq_sum]
  simp only [powAddCoeff, natCast_mod, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib]
  rw [sum_ite_eq' (range r) (e % r), sum_ite_eq' (range r) 0]
  simp only [mem_range, Nat.mod_lt _ hr, hr, ↓reduceIte]
  rw [pow_zero, mul_one, root_pow_mod, map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rfl

/-- The coefficients of `∑_{i < r} c i X^i`. -/
theorem coeff_coeffPoly (c : ℕ → ℕ) (k : ℕ) :
    (coeffPoly n r c).coeff k = if k < r then (c k : ZMod n) else 0 := by
  simp only [coeffPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_ite_eq (range r) k]
  simp only [mem_range]

/-- **Reduced coefficients determine their class**: for `n ≥ 1` and `r ≥ 1`, coefficient vectors
with entries below `n` have equal classes exactly when they agree below `r`. -/
theorem toQuot_eq_toQuot_iff (hn : 0 < n) (hr : 0 < r) {c d : ℕ → ℕ}
    (hc : ∀ i < r, c i < n) (hd : ∀ i < r, d i < n) :
    toQuot n r c = toQuot n r d ↔ ∀ i < r, c i = d i := by
  constructor
  · intro h
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · intro i hi; have := hc i hi; have := hd i hi; omega
    have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
    rw [toQuot, toQuot, AdjoinRoot.mk_eq_mk] at h
    have hzero : coeffPoly n r c - coeffPoly n r d = 0 := by
      by_contra h0
      refine (monic_X_pow_sub_one (R := ZMod n) hr.ne').not_dvd_of_degree_lt h0 ?_ h
      rw [← C_1, degree_X_pow_sub_C hr]
      refine (degree_lt_iff_coeff_zero _ _).mpr fun k hk => ?_
      have hk' : ¬k < r := not_lt.mpr hk
      rw [coeff_sub, coeff_coeffPoly, coeff_coeffPoly]
      simp only [hk', ↓reduceIte, sub_zero]
    intro i hi
    have hcoeff := congrArg (fun f => f.coeff i) hzero
    simp only [coeff_sub, coeff_coeffPoly, hi, ↓reduceIte, coeff_zero, sub_eq_zero] at hcoeff
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hc i hi), Nat.mod_eq_of_lt (hd i hi)]
      at hcoeff
    exact hcoeff
  · intro h
    rw [toQuot_eq_sum, toQuot_eq_sum]
    exact sum_congr rfl fun i hi => by rw [h i (mem_range.mp hi)]

/-- **The AKS congruence in coefficients**: `(X + a)^n ≡ X^n + a (mod X^r - 1, n)` exactly when
the `n`-th power of the class with the coefficients of `X + a` is the class with the coefficients
of `X^n + a`. -/
theorem congruence_iff_toQuot (hr : 0 < r) (a : ℕ) :
    Congruence n r a ↔ toQuot n r (powAddCoeff n r 1 a) ^ n = toQuot n r (powAddCoeff n r n a) := by
  rw [toQuot_powAddCoeff hr, toQuot_powAddCoeff hr, pow_one, ← map_pow, Congruence]

/-- Coefficients of `X^e + a` are reduced modulo `n`. -/
theorem powAddCoeff_lt (hn : 0 < n) (e a k : ℕ) : powAddCoeff n r e a k < n :=
  Nat.mod_lt _ hn

/-- Coefficients of products are reduced modulo `n`. -/
theorem mulCoeff_lt (hn : 0 < n) (p q : ℕ → ℕ) (k : ℕ) : mulCoeff n r p q k < n :=
  Nat.mod_lt _ hn

end Cslib.AKS
