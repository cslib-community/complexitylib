/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean)

public import Complexity.Init
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Principal roots of unity

An element `ω` of a commutative ring is a *principal* `n`-th root of unity when `ω ^ n = 1` and
`∑ i < n, (ω ^ l) ^ i = 0` for every `0 < l < n`. This geometric-sum condition is what the
inversion formula of the discrete Fourier transform needs (the summation lemma, [CLRS2009],
Lemma 30.6). In an integral domain every primitive `n`-th root of unity is principal
(`IsPrimitiveRoot.isPrincipalRoot`). Conversely, a principal root is primitive whenever
`(n : R) ≠ 0` (`IsPrincipalRoot.isPrimitiveRoot`), in any commutative ring. Neither notion
implies the other in general. `ω = 4` is a primitive square root of unity in `ZMod 15`, yet
`1 + 4 = 5 ≠ 0`, so it is not principal. `ω = 1` is a principal square root of unity in `ZMod 2`,
since `1 + 1 = 0`, but it is not primitive.

The radix-2 fast Fourier transform needs `ω ^ (2 ^ k) = -1`. This condition alone makes `ω` a
principal `2 ^ (k + 1)`-th root of unity in every commutative ring
(`IsPrincipalRoot.of_pow_two_pow_eq_neg_one`); no unit or domain hypothesis is required.

## Main definitions

* `IsPrincipalRoot ω n`: `ω ^ n = 1` and the geometric sums of `ω ^ l` vanish for `0 < l < n`.

## Main results

* `IsPrincipalRoot.geom_sum_pow`: `∑ i < n, (ω ^ l) ^ i` is `n` if `n ∣ l` and `0` otherwise.
* `IsPrimitiveRoot.isPrincipalRoot`: in a domain, primitive roots are principal.
* `IsPrincipalRoot.isPrimitiveRoot`: principal roots are primitive when `(n : R) ≠ 0`.
* `IsPrincipalRoot.of_pow_two_pow_eq_neg_one`: `ω ^ (2 ^ k) = -1` makes `ω` a principal
  `2 ^ (k + 1)`-th root of unity.
* `IsPrimitiveRoot.pow_two_pow_eq_neg_one`: in a domain, a primitive `2 ^ (k + 1)`-th root of
  unity satisfies `ω ^ (2 ^ k) = -1`.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 30.2.
-/

public section

open Finset

variable {R : Type*} [CommRing R]

/-- `ω` is a *principal* `n`-th root of unity: `ω ^ n = 1`, and for `0 < l < n` the geometric
sum `∑ i < n, (ω ^ l) ^ i` vanishes. This is the hypothesis of the DFT inversion formula
([CLRS2009], Lemma 30.6). -/
structure IsPrincipalRoot (ω : R) (n : ℕ) : Prop where
  /-- `ω` is an `n`-th root of unity. -/
  pow_eq_one : ω ^ n = 1
  /-- The geometric sums of the nontrivial powers `ω ^ l`, `0 < l < n`, vanish. -/
  geom_sum_eq_zero : ∀ l, 0 < l → l < n → ∑ i ∈ range n, (ω ^ l) ^ i = 0

namespace IsPrincipalRoot

variable {ω : R} {n : ℕ}

/-- The geometric sum of any power of a principal `n`-th root of unity: it is `n` when `n ∣ l`
and `0` otherwise. -/
theorem geom_sum_pow (h : IsPrincipalRoot ω n) (l : ℕ) :
    ∑ i ∈ range n, (ω ^ l) ^ i = if n ∣ l then (n : R) else 0 := by
  split_ifs with hl
  · obtain ⟨c, rfl⟩ := hl
    simp [pow_mul, h.pow_eq_one]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hmod : 0 < l % n := Nat.pos_of_ne_zero fun h0 => hl (Nat.dvd_of_mod_eq_zero h0)
    rw [← Nat.mod_add_div l n, pow_add, pow_mul, h.pow_eq_one, one_pow, mul_one]
    exact h.geom_sum_eq_zero _ hmod (Nat.mod_lt _ hn)

/-- A principal `n`-th root of unity is primitive when `(n : R) ≠ 0`: if `ω ^ l = 1` with
`0 < l < n`, the vanishing geometric sum of `ω ^ l` would be `n`. Without this hypothesis the
implication fails: `1` is a principal, non-primitive square root of unity in `ZMod 2`. -/
theorem isPrimitiveRoot (h : IsPrincipalRoot ω n) (hn : (n : R) ≠ 0) : IsPrimitiveRoot ω n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero fun h0 => hn (by rw [h0, Nat.cast_zero])
  refine IsPrimitiveRoot.mk_of_lt ω hpos h.pow_eq_one fun l hl hln h1 => hn ?_
  have hsum := h.geom_sum_eq_zero l hl hln
  rwa [h1, one_geom_sum] at hsum

/-- Doubling a geometric sum of length `2 ^ k`. -/
private theorem geom_sum_two_pow_succ (x : R) (k : ℕ) :
    ∑ i ∈ range (2 ^ (k + 1)), x ^ i = (1 + x ^ 2 ^ k) * ∑ i ∈ range (2 ^ k), x ^ i := by
  rw [pow_succ, mul_two, sum_range_add, add_mul, one_mul, mul_sum]
  simp_rw [pow_add]

/-- If `x ^ (2 ^ j) = -1` for some `j ≤ k`, the geometric sum of length `2 ^ (k + 1)` of `x`
vanishes. -/
private theorem geom_sum_two_pow_eq_zero {x : R} {j k : ℕ} (hj : j ≤ k) (hx : x ^ 2 ^ j = -1) :
    ∑ i ∈ range (2 ^ (k + 1)), x ^ i = 0 := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := by omega
    rw [geom_sum_two_pow_succ, hx, add_neg_cancel, zero_mul]
  | succ k ih =>
    rw [geom_sum_two_pow_succ]
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · rw [ih (by omega), mul_zero]
    · obtain rfl : j = k + 1 := by omega
      rw [hx, add_neg_cancel, zero_mul]

/-- An element with `ω ^ (2 ^ k) = -1` is a principal `2 ^ (k + 1)`-th root of unity, in any
commutative ring. Write `0 < l < 2 ^ (k + 1)` as `2 ^ v * u` with `u` odd; then `v ≤ k` and
`(ω ^ l) ^ (2 ^ (k - v)) = (-1) ^ u = -1`, so the geometric sum of `ω ^ l` telescopes to zero. -/
theorem of_pow_two_pow_eq_neg_one {k : ℕ} (h : ω ^ 2 ^ k = -1) :
    IsPrincipalRoot ω (2 ^ (k + 1)) where
  pow_eq_one := by rw [pow_succ, pow_mul, h, neg_one_sq]
  geom_sum_eq_zero l hl hlt := by
    obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := l) hl.ne'
    have hv : v ≤ k := by
      by_contra hv
      have : 2 ^ (k + 1) ≤ 2 ^ v * u :=
        le_trans (Nat.pow_le_pow_right two_pos (by omega)) (Nat.le_mul_of_pos_right _ hu.pos)
      omega
    refine geom_sum_two_pow_eq_zero (j := k - v) (by omega) ?_
    rw [← pow_mul, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hv, pow_mul, h,
      hu.neg_one_pow]

end IsPrincipalRoot

namespace IsPrimitiveRoot

variable [IsDomain R] {ω : R} {n : ℕ}

/-- In an integral domain, a primitive `n`-th root of unity is principal. -/
theorem isPrincipalRoot (h : IsPrimitiveRoot ω n) : IsPrincipalRoot ω n where
  pow_eq_one := h.pow_eq_one
  geom_sum_eq_zero l hl hln := by
    have hne : ω ^ l ≠ 1 := fun h1 =>
      absurd (Nat.le_of_dvd hl (h.dvd_of_pow_eq_one l h1)) (by omega)
    refine eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne hne) ?_
    rw [mul_geom_sum, ← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow, sub_self]

/-- In an integral domain, a primitive `2 ^ (k + 1)`-th root of unity `ω` satisfies
`ω ^ (2 ^ k) = -1`, the hypothesis of the radix-2 fast Fourier transform. -/
theorem pow_two_pow_eq_neg_one {k : ℕ} (h : IsPrimitiveRoot ω (2 ^ (k + 1))) :
    ω ^ 2 ^ k = -1 := by
  have h2 := h.pow_of_dvd (p := 2 ^ k) (pow_ne_zero _ two_ne_zero) (pow_dvd_pow 2 k.le_succ)
  rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos two_pos k)] at h2
  exact h2.eq_neg_one_of_two_right

end IsPrimitiveRoot
