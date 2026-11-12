/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.IsolatedBasis
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Finsupp.Weight

/-!
# Substituting powers of one variable

A weight `c : σ → ℕ` on the variables gives the substitution `x i ↦ t ^ c i` of a multivariate
polynomial `f` into a univariate one. The monomial with exponent vector `m` becomes
`t ^ Finsupp.weight c m`, so the coefficient of `t ^ e` is the sum of the coefficients of `f` at
the exponent vectors of weight `e`.

If the coefficients of `f` are the values `ℓ (D m)` of a linear form `ℓ` on a family of vectors
`D`, and the weight isolates a set of exponent vectors for `D` (`Cslib.Isolates`), then the
substitution keeps a nonzero `f` nonzero: among the isolated exponent vectors `m` with
`ℓ (D m) ≠ 0`, the one of least weight is the only exponent vector of its weight at which `f` has
a nonzero coefficient. Linear independence of the isolated vectors is not used.

## Main results

* `MvPolynomial.coeff_aeval_X_pow`: the coefficients of `f (t ^ c i)`.
* `MvPolynomial.aeval_X_pow_ne_zero_of_isolates`: a weight isolating a set of exponent vectors
  keeps a nonzero polynomial nonzero ([AgrawalGurjarKorwarSaxena2015], Lemma 6).

## References

* [AgrawalGurjarKorwarSaxena2015], Lemma 6.
-/

public section

namespace MvPolynomial

open Polynomial

variable {σ R F A : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The coefficient of `t ^ e` in `f (t ^ c i)` is the sum of the coefficients of `f` at the
exponent vectors of weight `e`. -/
theorem coeff_aeval_X_pow (c : σ → ℕ) (f : MvPolynomial σ R) (e : ℕ) :
    (aeval (fun i => (Polynomial.X : R[X]) ^ c i) f).coeff e =
      ∑ m ∈ f.support with Finsupp.weight c m = e, f.coeff m := by
  classical
  rw [aeval_def, eval₂_eq, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : ∏ i ∈ m.support, ((Polynomial.X : R[X]) ^ c i) ^ m i =
      Polynomial.X ^ Finsupp.weight c m := by
    rw [Finsupp.weight_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [h, ← Polynomial.C_eq_algebraMap, Polynomial.coeff_C_mul_X_pow]
  simp only [eq_comm]

end CommSemiring

variable [Field F] [AddCommGroup A] [Module F A]

/-- Let the coefficients of a nonzero polynomial `f` be the values `ℓ (D m)` of a linear form
`ℓ` on a family of vectors `D`. If the weight of `c : σ → ℕ` isolates a set `S` of exponent
vectors for `D`, then `f (t ^ c i)` is nonzero: its coefficient at the least weight of an
`m ∈ S` with `ℓ (D m) ≠ 0` is `ℓ (D m)`. -/
theorem aeval_X_pow_ne_zero_of_isolates {c : σ → ℕ} {D : (σ →₀ ℕ) → A}
    {T S : Finset (σ →₀ ℕ)} (h : Cslib.Isolates F (Finsupp.weight c) D T S) (ℓ : A →ₗ[F] F)
    {f : MvPolynomial σ F} (hT : f.support ⊆ T) (hf : ∀ m ∈ T, f.coeff m = ℓ (D m))
    (hf0 : f ≠ 0) : aeval (fun i => (Polynomial.X : F[X]) ^ c i) f ≠ 0 := by
  classical
  have key : ∀ m ∈ T, m ∉ S →
      (∀ m' ∈ S, Finsupp.weight c m' < Finsupp.weight c m → ℓ (D m') = 0) → ℓ (D m) = 0 := by
    intro m hm hmS hz
    refine (Submodule.span_le (p := LinearMap.ker ℓ)).2 ?_ (h.2.2 m hm hmS)
    rintro _ ⟨m', hm', rfl⟩
    exact hz m' hm'.1 hm'.2
  obtain ⟨m₀, hm₀⟩ := ne_zero_iff.1 hf0
  have hm₀T : m₀ ∈ T := hT (mem_support_iff.2 hm₀)
  have hex : ({m ∈ S | ℓ (D m) ≠ 0}).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    have hz : ∀ m ∈ S, ℓ (D m) = 0 := fun m hm => not_not.1 (hne hm)
    refine hm₀ ((hf m₀ hm₀T).trans ?_)
    by_cases hS : m₀ ∈ S
    · exact hz m₀ hS
    · exact key m₀ hm₀T hS fun m' hm' _ => hz m' hm'
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image _ (Finsupp.weight c) hex
  rw [Finset.mem_filter] at hm
  have hmT : m ∈ T := h.1 hm.1
  have hcoeff : (aeval (fun i => (Polynomial.X : F[X]) ^ c i) f).coeff (Finsupp.weight c m) =
      f.coeff m := by
    rw [coeff_aeval_X_pow]
    refine Finset.sum_eq_single_of_mem m
      (Finset.mem_filter.2 ⟨mem_support_iff.2 (hf m hmT ▸ hm.2), rfl⟩) fun m' hm' hne => ?_
    rw [Finset.mem_filter] at hm'
    have hm'T : m' ∈ T := hT hm'.1
    rw [hf m' hm'T]
    refine key m' hm'T (fun hS => hne (h.2.1 hS hm.1 hm'.2)) fun m'' hm'' hlt => ?_
    by_contra hnz
    exact (hmin m'' (Finset.mem_filter.2 ⟨hm'', hnz⟩)).not_gt (hm'.2 ▸ hlt)
  exact fun h0 => hm.2 (by rw [← hf m hmT, ← hcoeff, h0, Polynomial.coeff_zero])

end MvPolynomial
