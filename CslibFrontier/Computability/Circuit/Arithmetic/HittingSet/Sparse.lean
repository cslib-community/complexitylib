/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.LinearAlgebra.Vandermonde

/-!
# A hitting set for sparse polynomials

A polynomial is `s`-sparse if it has at most `s` monomials. Let `x : σ → F` be a point of a
domain whose monomials are pairwise distinct: `m ↦ ∏ᵢ x i ^ m i` is injective on exponent
vectors. Then the `s` points `(x i ^ j)ᵢ`, `j < s`, form a hitting set for the `s`-sparse
polynomials (`isHittingSet_powerHittingSet`). Indeed the value of `f = ∑ₘ cₘ X ^ m` at the `j`-th
point is `∑ₘ cₘ βₘ ^ j` with `βₘ = ∏ᵢ x i ^ m i`, and for distinct nodes `βₘ` these sums cannot
vanish for all `j` below the number of monomials: the Vandermonde matrix is invertible.

In characteristic zero the point of the first `n` primes has distinct monomials, by unique
factorisation (`isHittingSet_primePowers`). This is the zero test of the sparse interpolation
algorithm of Ben-Or and Tiwari [BenOrTiwari1988]. The hitting set has `s` points whatever the
degree; its points are large integers, and the statement says nothing about their bit length.

## Main definitions

* `powerHittingSet`: the points `(x i ^ j)ᵢ` for `j < s`.

## Main results

* `isHittingSet_powerHittingSet`: these points hit the `s`-sparse polynomials when the monomials
  of `x` are distinct.
* `injective_prod_prime_pow`: distinct primes have distinct monomials in characteristic zero.
* `isHittingSet_primePowers`: the hitting set of prime powers.

## References

* [M. Ben-Or, P. Tiwari, *A deterministic algorithm for sparse multivariate polynomial
  interpolation*][BenOrTiwari1988]
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable {F σ : Type*} [CommRing F]

open scoped Classical in
/-- The points `(x i ^ j)ᵢ` for `j < s`. -/
noncomputable def powerHittingSet (x : σ → F) (s : ℕ) : Finset (σ → F) :=
  (range s).image fun (j : ℕ) (i : σ) => x i ^ j

theorem card_powerHittingSet_le (x : σ → F) (s : ℕ) : (powerHittingSet x s).card ≤ s := by
  classical
  exact card_image_le.trans_eq (card_range s)

/-- The value of a polynomial at the point `(x i ^ j)ᵢ` is a combination of `j`-th powers of the
monomials of `x`. -/
private theorem eval_pow_point (x : σ → F) (j : ℕ) (f : MvPolynomial σ F) :
    eval (fun i => x i ^ j) f =
      ∑ m ∈ f.support, f.coeff m * (m.prod fun i k => x i ^ k) ^ j := by
  rw [eval_eq]
  refine sum_congr rfl fun m _ => ?_
  rw [Finsupp.prod, ← prod_pow]
  exact congrArg _ (prod_congr rfl fun i _ => by rw [← pow_mul, ← pow_mul, mul_comm])

/-- If the monomials of the point `x` are pairwise distinct, the points `(x i ^ j)ᵢ`, `j < s`,
are a hitting set for the polynomials with at most `s` monomials. -/
theorem isHittingSet_powerHittingSet [IsDomain F] {x : σ → F}
    (hx : Function.Injective fun m : σ →₀ ℕ => m.prod fun i k => x i ^ k) (s : ℕ) :
    IsHittingSet (powerHittingSet x s) {f | f.support.card ≤ s} := by
  classical
  intro f hf hf0
  by_contra hall
  have hzero (j : ℕ) (hj : j < s) :
      ∑ m ∈ f.support, f.coeff m * (m.prod fun i k => x i ^ k) ^ j = 0 := by
    rw [← eval_pow_point]
    exact not_not.1 fun h => hall ⟨_, mem_image.2 ⟨j, mem_range.2 hj, rfl⟩, h⟩
  set e := f.support.equivFin with he
  have hv : (fun t : Fin f.support.card => f.coeff (e.symm t : σ →₀ ℕ)) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := fun t => (e.symm t : σ →₀ ℕ).prod fun i k => x i ^ k)
      (hx.comp (Subtype.val_injective.comp e.symm.injective)) fun i => by
        rw [← hzero i (i.2.trans_le hf), ← sum_coe_sort f.support]
        exact Equiv.sum_comp e.symm fun m : f.support =>
          f.coeff (m : σ →₀ ℕ) * ((m : σ →₀ ℕ).prod fun i k => x i ^ k) ^ (i : ℕ)
  obtain ⟨m, hm⟩ : f.support.Nonempty := by
    rwa [nonempty_iff_ne_empty, Ne, support_eq_empty]
  have h := congrFun hv (e ⟨m, hm⟩)
  rw [Equiv.symm_apply_apply] at h
  exact mem_support_iff.1 hm h

/-- In characteristic zero, distinct primes have pairwise distinct monomials. -/
theorem injective_prod_prime_pow [CharZero F] {p : σ → ℕ} (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    Function.Injective fun m : σ →₀ ℕ => m.prod fun i k => (p i : F) ^ k := by
  classical
  intro m m' h
  have hcast (m : σ →₀ ℕ) : (m.prod fun i k => (p i : F) ^ k) =
      (((m.mapDomain p).prod (· ^ ·) : ℕ) : F) := by
    rw [Finsupp.prod_mapDomain_index_inj hp, Finsupp.prod, Finsupp.prod, Nat.cast_prod]
    exact prod_congr rfl fun i _ => (Nat.cast_pow _ _).symm
  have hfact (m : σ →₀ ℕ) : ((m.mapDomain p).prod (· ^ ·)).factorization = m.mapDomain p :=
    Nat.factorization_prod_pow_eq_self fun q hq => by
      obtain ⟨i, -, rfl⟩ := mem_image.1 (Finsupp.mapDomain_support hq)
      exact hprime i
  simp only [hcast] at h
  refine Finsupp.mapDomain_injective hp ?_
  rw [← hfact m, ← hfact m', Nat.cast_injective h]

/-- The powers `(p₀ ^ j, …, pₙ₋₁ ^ j)`, `j < s`, of the first `n` primes are a hitting set for
the `n`-variate polynomials with at most `s` monomials, over a domain of characteristic zero. -/
theorem isHittingSet_primePowers [IsDomain F] [CharZero F] (n s : ℕ) :
    IsHittingSet (powerHittingSet (fun i : Fin n => (Nat.nth Nat.Prime i : F)) s)
      {f | f.support.card ≤ s} :=
  isHittingSet_powerHittingSet
    (injective_prod_prime_pow
      ((Nat.nth_injective Nat.infinite_setOfPred_prime).comp Fin.val_injective)
      fun i => Nat.prime_nth_prime i) s

end Cslib.Circuits.Arithmetic
