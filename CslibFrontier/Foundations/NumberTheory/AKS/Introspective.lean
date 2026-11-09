/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.AKS.Criterion
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic

/-!
# Introspective numbers

Fix a prime `p`, a number `r`, and a field `K` that is an algebra over `ℤ / p`. A number `m` is
*introspective* for a polynomial `f` over `ℤ / p` if `f(η)^m = f(η^m)` for every `r`-th root of
unity `η` of `K` (`Cslib.AKS.Introspective`). This is the form of Agrawal, Kayal and Saxena's
introspection `f(X)^m ≡ f(X^m) (mod X^r - 1, p)` that their proof uses, evaluated at roots of unity
as in Lenstra's exposition [Agrawal, Kayal, Saxena, Section 4][AKS2004].

* `p` is introspective for every `f`, by the Frobenius map (`introspective_prime`).
* Introspective numbers are closed under products, and introspective polynomials under products
  (`Introspective.mul`, `Introspective.mul_poly`).
* If `p ∣ n` and the AKS congruence `(X + a)^n ≡ X^n + a (mod X^r - 1, n)` holds, then `n` is
  introspective for `X + a` (`introspective_of_congruence`).
* If `n` is introspective for `f` and `p ∣ n`, so is `n / p`, because the Frobenius map of a field
  of characteristic `p` is injective (`Introspective.div_prime`).

## Main definitions

* `Cslib.AKS.Introspective`: `f(η)^m = f(η^m)` at every `r`-th root of unity `η`.

## Main results

* `Cslib.AKS.introspective_prime`, `Cslib.AKS.introspective_of_congruence`,
  `Cslib.AKS.Introspective.div_prime`: the basic introspective numbers.
* `Cslib.AKS.Introspective.mul`, `Cslib.AKS.Introspective.mul_poly`,
  `Cslib.AKS.Introspective.multiset_prod`: closure properties.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.AKS

open Polynomial

variable {p : ℕ} {K : Type*} [Field K] [Algebra (ZMod p) K]

variable (K) in
/-- `m` is **introspective** for `f` (with respect to `r`): `f(η)^m = f(η^m)` for every `r`-th root
of unity `η` of `K`. -/
def Introspective (r m : ℕ) (f : (ZMod p)[X]) : Prop :=
  ∀ η : K, η ^ r = 1 → aeval η f ^ m = aeval (η ^ m) f

variable {r m m' : ℕ} {f g : (ZMod p)[X]}

/-- **The prime is introspective** for every polynomial: `f(η)^p = f(η^p)` by the Frobenius map,
since the coefficients of `f` lie in `ℤ / p`. -/
theorem introspective_prime [Fact p.Prime] (r : ℕ) (f : (ZMod p)[X]) :
    Introspective K r p f := fun η _ => by
  rw [← map_pow, ← ZMod.expand_card, expand_aeval]

/-- **Introspective numbers are closed under products.** -/
theorem Introspective.mul (hm : Introspective K r m f) (hm' : Introspective K r m' f) :
    Introspective K r (m * m') f := fun η hη => by
  have hηm : (η ^ m) ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hη, one_pow]
  rw [pow_mul, hm η hη, hm' _ hηm, ← pow_mul]

/-- **Introspective polynomials are closed under products.** -/
theorem Introspective.mul_poly (hf : Introspective K r m f) (hg : Introspective K r m g) :
    Introspective K r m (f * g) := fun η hη => by
  rw [map_mul, map_mul, mul_pow, hf η hη, hg η hη]

/-- Every number is introspective for the constant `1`. -/
theorem introspective_one (r m : ℕ) : Introspective K r m (1 : (ZMod p)[X]) := fun η _ => by
  simp

/-- Every number is introspective for `X`. -/
theorem introspective_X (r m : ℕ) : Introspective K r m (X : (ZMod p)[X]) := fun η _ => by
  simp

/-- Products of introspective polynomials are introspective. -/
theorem Introspective.multiset_prod {s : Multiset (ZMod p)[X]}
    (hs : ∀ f ∈ s, Introspective K r m f) : Introspective K r m s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using introspective_one r m
  | cons f s ih =>
    rw [Multiset.prod_cons]
    exact (hs f (Multiset.mem_cons_self f s)).mul_poly
      (ih fun g hg => hs g (Multiset.mem_cons_of_mem hg))

/-- Every power of `m` is introspective when `m` is. -/
theorem Introspective.pow (hm : Introspective K r m f) (k : ℕ) : Introspective K r (m ^ k) f := by
  induction k with
  | zero => exact fun η _ => by simp
  | succ k ih => rw [pow_succ]; exact ih.mul hm

/-- **The AKS congruence gives introspection.** If `p ∣ n` and
`(X + a)^n ≡ X^n + a (mod X^r - 1, n)`, then `n` is introspective for `X + a`. -/
theorem introspective_of_congruence {n a : ℕ} (hpn : p ∣ n) (h : Congruence n r a) :
    Introspective K r n (X + C (a : ZMod p)) := fun η hη => by
  let ψ : ZMod n →+* K := (algebraMap (ZMod p) K).comp (ZMod.castHom hpn (ZMod p))
  have hroot : eval₂ ψ η (X ^ r - 1 : (ZMod n)[X]) = 0 := by simp [hη]
  have h' := congrArg (AdjoinRoot.lift ψ η hroot) h
  simp only [AdjoinRoot.lift_mk, eval₂_pow, eval₂_add, eval₂_X, ψ, map_natCast] at h'
  simpa using h'

/-- **`n / p` is introspective when `n` is**, for `p ∣ n`: both `(f(η)^{n/p})^p` and `f(η^{n/p})^p`
equal `f(η^n)`, and the Frobenius map of `K` is injective. -/
theorem Introspective.div_prime [Fact p.Prime] {n : ℕ} (hpn : p ∣ n) (hn : Introspective K r n f) :
    Introspective K r (n / p) f := fun η hη => by
  have hchar : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hexp : ExpChar K p := ExpChar.prime (Fact.out : p.Prime)
  have hηk : (η ^ (n / p)) ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hη, one_pow]
  apply frobenius_inj K p
  simp only [frobenius_def]
  rw [introspective_prime (K := K) r f _ hηk, ← pow_mul, ← pow_mul, Nat.div_mul_cancel hpn,
    hn η hη]

end Cslib.AKS
