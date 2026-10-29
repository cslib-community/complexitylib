/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Integer polynomials modulo `X^p - 1`

## Main definitions

* `CyclicIntRing`: the integer polynomial quotient.
* `CyclicIntRing.coeff`: coefficients in the unique representative of degree less than `p`.

## Main results

* `CyclicIntRing.coeff_x_pow`: powers have a single coefficient at the residue of their
  exponent.

## References

Adapted from [Anthropic's
Hashing.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem17/Hashing.lean#L57-L101).
-/

@[expose] public section

namespace Cslib

open Polynomial in
/-- The quotient ring `ℤ[X]/(X^p - 1)`. -/
abbrev CyclicIntRing (p : ℕ) : Type := AdjoinRoot ((X : ℤ[X]) ^ p - C 1)

namespace CyclicIntRing

open Polynomial

variable {p : ℕ}

/-- The element `x` of `ℤ[x]/(x^p − 1)`. -/
noncomputable def x (p : ℕ) : CyclicIntRing p := AdjoinRoot.root _

/-- The coefficient of degree `r` in an element `z` of the quotient, as a linear map. It is the
coefficient of `x^r` in the unique polynomial of degree less than `p` that represents `z`
(Mathlib's `AdjoinRoot.modByMonicHom` gives that polynomial; it asks for the fact that `x^p − 1`
is monic, which holds as `p ≠ 0`).
-/
noncomputable def coeff (hp : p ≠ 0) (r : ℕ) : CyclicIntRing p →ₗ[ℤ] ℤ :=
  lcoeff ℤ r ∘ₗ AdjoinRoot.modByMonicHom (monic_X_pow_sub_C (1 : ℤ) hp)

/-- The coefficient, in terms of the representing polynomial. -/
theorem coeff_apply (hp : p ≠ 0) (r : ℕ) (z : CyclicIntRing p) :
    coeff hp r z = (AdjoinRoot.modByMonicHom (monic_X_pow_sub_C (1 : ℤ) hp) z).coeff r :=
  rfl

/-- In `ℤ[x]/(x^p − 1)` we have `x^p = 1`. -/
private theorem x_pow_self (p : ℕ) : x p ^ p = 1 := by
  have h : AdjoinRoot.mk ((X : ℤ[X]) ^ p - C 1) ((X : ℤ[X]) ^ p - C 1) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, C_1, map_one] at h
  exact sub_eq_zero.1 h

/-- The coefficient of `x^r` in the power `x^k` of `ℤ[x]/(x^p − 1)` is 1 if `r = k mod p` and 0
otherwise.
-/
theorem coeff_x_pow (hp : p ≠ 0) (k r : ℕ) :
    coeff hp r (x p ^ k) = if r = k % p then 1 else 0 := by
  have hred : x p ^ k = x p ^ (k % p) := by
    conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul, x_pow_self, one_pow, one_mul]
  have hdeg : ((X : ℤ[X]) ^ (k % p)).degree < ((X : ℤ[X]) ^ p - C 1).degree := by
    rw [degree_X_pow, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
    exact_mod_cast Nat.mod_lt k (Nat.pos_of_ne_zero hp)
  rw [coeff_apply, hred, x, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (monic_X_pow_sub_C (1 : ℤ) hp)).2 hdeg, coeff_X_pow]

end CyclicIntRing

end Cslib
