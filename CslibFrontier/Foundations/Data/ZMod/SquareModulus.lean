/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/ZMod/Units.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement
import CslibFrontier.Foundations.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Basic

/-!
# Residues modulo a square

In `ZMod (N ^ 2)` the residue `N` squares to zero. So `1 + N` behaves like `1 + ε` with
`ε ^ 2 = 0`: `(1 + N) ^ a = 1 + a * N`, and `1 + N` has order exactly `N` for positive `N`. An
`N`-th power modulo `N ^ 2` depends only on its base modulo `N`, and the units satisfy Euler's
theorem with exponent `φ(N ^ 2) = N * φ(N)`. These facts underlie Paillier encryption
([KatzLindell2020], Claim 15.8 and the proof of Claim 15.9).

## Main results

* `ZMod.natCast_mul_self_eq_zero`: `N * N = 0` in `ZMod (N ^ 2)`.
* `ZMod.one_add_natCast_pow`, `ZMod.one_add_natCast_pow_self`, `ZMod.orderOf_one_add_natCast`:
  `(1 + N) ^ a = 1 + a * N`, so `(1 + N) ^ N = 1`, and `1 + N` has order `N` when `0 < N`.
* `ZMod.add_natCast_mul_pow_self`, `ZMod.natCast_pow_self_mod`: an `N`-th power modulo `N ^ 2`
  only depends on the base modulo `N`.
* `ZMod.natCast_pow_mul_totient`: `r ^ (N * φ(N)) = 1` modulo `N ^ 2` for `r` coprime to `N`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Chapter 15,
  Claims 15.8 and 15.9.
-/

public section

namespace ZMod

/-- `N * N` vanishes modulo `N ^ 2`. -/
theorem natCast_mul_self_eq_zero (N : ℕ) : (N : ZMod (N ^ 2)) * N = 0 := by
  rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]

/-- `(1 + N) ^ a = 1 + a * N` in `ZMod (N ^ 2)` ([KatzLindell2020], Claim 15.8). -/
theorem one_add_natCast_pow (N a : ℕ) :
    (1 + (N : ZMod (N ^ 2))) ^ a = 1 + (a : ZMod (N ^ 2)) * N := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ (1 + (N : ZMod (N ^ 2))) a, ih]
    push_cast
    linear_combination (a : ZMod (N ^ 2)) * natCast_mul_self_eq_zero N

/-- `(1 + N) ^ N = 1` in `ZMod (N ^ 2)` ([KatzLindell2020], Claim 15.8). -/
theorem one_add_natCast_pow_self (N : ℕ) : (1 + (N : ZMod (N ^ 2))) ^ N = 1 := by
  rw [one_add_natCast_pow, natCast_mul_self_eq_zero, add_zero]

/-- For positive `N`, the residue `1 + N` has order exactly `N` in `ZMod (N ^ 2)`
([KatzLindell2020], Claim 15.8). -/
theorem orderOf_one_add_natCast {N : ℕ} (hN : 0 < N) :
    orderOf (1 + (N : ZMod (N ^ 2))) = N := by
  rw [orderOf_eq_iff hN]
  refine ⟨one_add_natCast_pow_self N, fun a ha ha0 h => ?_⟩
  rw [one_add_natCast_pow, add_eq_left, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, pow_two] at h
  have := Nat.le_of_dvd ha0 (Nat.dvd_of_mul_dvd_mul_right hN h)
  lia

/-- Adding a multiple of `N` does not change an `N`-th power in `ZMod (N ^ 2)`. -/
theorem add_natCast_mul_pow_self (N : ℕ) (v k : ZMod (N ^ 2)) :
    (v + (N : ZMod (N ^ 2)) * k) ^ N = v ^ N := by
  have h := dvd_sub_pow_of_dvd_sub (p := N) (a := v + N * k) (b := v) ⟨k, by ring⟩ 1
  rwa [pow_one, one_add_one_eq_two, pow_two (N : ZMod (N ^ 2)), natCast_mul_self_eq_zero,
    zero_dvd_iff, sub_eq_zero] at h

/-- The `N`-th power of a natural number in `ZMod (N ^ 2)` depends only on its residue
modulo `N`. -/
theorem natCast_pow_self_mod (N m : ℕ) :
    (m : ZMod (N ^ 2)) ^ N = ((m % N : ℕ) : ZMod (N ^ 2)) ^ N := by
  conv_lhs => rw [← Nat.mod_add_div m N]
  rw [Nat.cast_add, Nat.cast_mul, add_natCast_mul_pow_self]

/-- A natural number coprime to `N` has `N * φ(N)`-th power `1` modulo `N ^ 2`. -/
theorem natCast_pow_mul_totient {N r : ℕ} (hr : r.Coprime N) :
    (r : ZMod (N ^ 2)) ^ (N * N.totient) = 1 := by
  have hunit := ZMod.pow_totient (ZMod.unitOfCoprime r (Nat.Coprime.pow_right 2 hr))
  rw [Nat.totient_sq] at hunit
  simpa only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] using
    congrArg Units.val hunit

end ZMod
