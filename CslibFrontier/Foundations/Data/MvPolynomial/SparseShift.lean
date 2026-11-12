/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, partial derivatives of translated sparse polynomials)

public import CslibFrontier.Foundations.Data.MvPolynomial.IteratedPDerivSpan
public import CslibFrontier.Foundations.Data.MvPolynomial.LowestComponent
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The initial form of a translated sparse polynomial

Let `p` be a polynomial with `s` monomials over a field and `u` a point with all coordinates
nonzero. Let `m` be such that the translate `g = p (X + u)` has no homogeneous component of degree
less than `m`, and let `h` be the component of `g` of degree `m`; when `h ≠ 0` this is the *initial
form* of `g`. Then the space of all partial derivatives of `h` has dimension at most `s`
(`MvPolynomial.finrank_iteratedPDerivSpan_homogeneousComponent_shift_le`). This is Lemma 3.2 of
[Bhargava and Sengupta][BhargavaSengupta2026].

The proof uses the *correlated shifted partials* `(X + u) ^ β * ∂ ^ β g`, where the multiplier and
the derivative are indexed by the same tuple `β` of variables. For a monomial `q`, the polynomial
`X ^ β * ∂ ^ β q` is a scalar multiple of `q`, so all correlated shifted partials of `g` lie in the
image under the translation of the span of the monomials of `p`
(`MvPolynomial.restrictSupport`), a space of dimension at most `s`
(Lemma 3.1 of the source, there quoted from Forbes).

## Departures from the source

The source works with Hasse derivatives over any field; here the derivatives are the ordinary
partial derivatives, also over any field: the argument only uses that `X ^ β * ∂ ^ β q` is a
multiple of the monomial `q`. Derivatives are indexed by tuples of variables rather than by
exponent vectors. The source derives a contradiction from more than `s` derivatives of `h` chosen
as bases of the spaces of derivatives of each order; here a linearly independent family of
derivatives spanning the space is lifted to correlated shifted partials, which are linearly
independent because their lowest homogeneous components are
(`MvPolynomial.linearIndependent_of_homogeneousComponent`), so the family has at most `s`
members.

## Main results

* `MvPolynomial.prod_X_mul_iteratedPDeriv_mem_restrictSupport`,
  `MvPolynomial.prod_X_add_C_mul_iteratedPDeriv_shift_mem`: Lemma 3.1 of the source.
* `MvPolynomial.finrank_iteratedPDerivSpan_homogeneousComponent_shift_le`: Lemma 3.2 of the
  source.

## References

* [V. Bhargava, A. K. Sengupta, *Polynomial identity testing and lower bounds for sparse affine
  orbits*][BhargavaSengupta2026], Lemmas 3.1 and 3.2
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- An iterated partial derivative of a monomial is a monomial which is either zero or gives back
the exponent of the original monomial when multiplied by the variables of the derivative. -/
private theorem exists_iteratedPDeriv_monomial {k : ℕ} (α : Fin k → σ) (μ : σ →₀ ℕ) (c : R) :
    ∃ (ν : σ →₀ ℕ) (c' : R), iteratedPDeriv α (monomial μ c) = monomial ν c' ∧
      (c' = 0 ∨ ∀ a : R, (∏ i, X (α i)) * monomial ν a = monomial μ a) := by
  classical
  induction k with
  | zero => exact ⟨μ, c, rfl, Or.inr fun a => by simp⟩
  | succ k ih =>
    obtain ⟨ν, c', h, hν⟩ := ih (Fin.tail α)
    refine ⟨ν - Finsupp.single (α 0) 1, c' * ν (α 0), by
      rw [iteratedPDeriv_succ_apply, h, pderiv_monomial], ?_⟩
    rcases hν with rfl | hν
    · exact Or.inl (zero_mul _)
    by_cases h0 : ν (α 0) = 0
    · exact Or.inl (by rw [h0, Nat.cast_zero, mul_zero])
    refine Or.inr fun a => ?_
    have he : Finsupp.single (α 0) 1 + (ν - Finsupp.single (α 0) 1) = ν :=
      Finsupp.ext fun j => by
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hj
        · subst hj; omega
        · omega
    rw [Fin.prod_univ_succ, mul_comm (X (α 0)), mul_assoc, X, monomial_mul_monomial, one_mul, he]
    exact hν a

/-- **Lemma 3.1 of the source**, before translation. Multiplying an iterated partial derivative
of `p` by the variables of the derivative gives a polynomial in the span of the monomials of
`p`. -/
theorem prod_X_mul_iteratedPDeriv_mem_restrictSupport {k : ℕ} (α : Fin k → σ)
    (p : MvPolynomial σ R) :
    (∏ i, X (α i)) * iteratedPDeriv α p ∈ restrictSupport R (p.support : Set (σ →₀ ℕ)) := by
  rw [restrictSupport_eq_span]
  have hp : iteratedPDeriv α p =
      ∑ μ ∈ p.support, iteratedPDeriv α (monomial μ (p.coeff μ)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [hp, Finset.mul_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  obtain ⟨ν, c', h, hν⟩ := exists_iteratedPDeriv_monomial α μ (p.coeff μ)
  rw [h]
  rcases hν with rfl | hν
  · rw [monomial_zero, mul_zero]
    exact zero_mem _
  · rw [hν, ← mul_one c', ← smul_eq_mul, ← smul_monomial]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, rfl⟩)

/-- **Lemma 3.1 of the source.** The correlated shifted partials
`(X + u) ^ β * ∂ ^ β (p (X + u))` of a translate of `p` lie in the image under the translation of
the span of the monomials of `p`. -/
theorem prod_X_add_C_mul_iteratedPDeriv_shift_mem (u : σ → R) {k : ℕ} (α : Fin k → σ)
    (p : MvPolynomial σ R) :
    (∏ i, (X (α i) + C (u (α i)))) * iteratedPDeriv α (shift u p) ∈
      (restrictSupport R (p.support : Set (σ →₀ ℕ))).map
        (shift u : MvPolynomial σ R →ₐ[R] MvPolynomial σ R).toLinearMap := by
  refine ⟨_, prod_X_mul_iteratedPDeriv_mem_restrictSupport α p, ?_⟩
  rw [AlgHom.toLinearMap_apply, map_mul, map_prod, iteratedPDeriv_shift]
  simp only [shift_X]

section Field

variable {K : Type*} [Field K]

/-- **Lemma 3.2 of the source.** Let `p` be a polynomial over a field and `u` a point with all
coordinates nonzero, and suppose that the translate `p (X + u)` has no homogeneous component of
degree less than `m`. Then the space of all partial derivatives of its component of degree `m` is
finite-dimensional, of dimension at most the number of monomials of `p`. -/
theorem finrank_iteratedPDerivSpan_homogeneousComponent_shift_le {p : MvPolynomial σ K}
    {u : σ → K} (hu : ∀ i, u i ≠ 0) {m : ℕ}
    (hm : ∀ j < m, homogeneousComponent j (shift u p) = 0) :
    Module.Finite K (iteratedPDerivSpan (homogeneousComponent m (shift u p))) ∧
      Module.finrank K (iteratedPDerivSpan (homogeneousComponent m (shift u p))) ≤
        p.support.card := by
  classical
  set g : MvPolynomial σ K := shift u p with hg
  set h := homogeneousComponent m g with hh
  set V := (restrictSupport K (p.support : Set (σ →₀ ℕ))).map
    (shift u : MvPolynomial σ K →ₐ[K] MvPolynomial σ K).toLinearMap with hV
  have : Module.Finite K (restrictSupport K (p.support : Set (σ →₀ ℕ))) :=
    Module.Finite.of_basis (basisRestrictSupport K _)
  have hVrank : Module.finrank K V ≤ p.support.card :=
    (Submodule.finrank_map_le _ _).trans
      ((Module.finrank_eq_card_basis (basisRestrictSupport K _)).trans (Fintype.card_coe _)).le
  -- a linearly independent family of derivatives of `h` spanning all of them
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K
    (Set.range fun x : Σ k, Fin k → σ => iteratedPDeriv x.2 h)
  have hbsub' (x : b) : ∃ y : Σ k, Fin k → σ, iteratedPDeriv y.2 h = x := hbsub x.2
  choose idx hidx using hbsub'
  have hk (x : b) : (idx x).1 ≤ m := not_lt.1 fun hlt => hbli.ne_zero x (by
    rw [← hidx x]
    exact iteratedPDeriv_homogeneousComponent_eq_zero hlt _ _)
  -- the lifts of the derivatives to correlated shifted partials of `g`
  let Fam : b → MvPolynomial σ K := fun x =>
    (∏ i, (X ((idx x).2 i) + C (u ((idx x).2 i)))) * iteratedPDeriv (idx x).2 g
  have hstart (x : b) : ∀ j < m - (idx x).1,
      homogeneousComponent j (iteratedPDeriv (idx x).2 g) = 0 := fun j hj => by
    rw [homogeneousComponent_iteratedPDeriv, hm _ (by omega), map_zero]
  let w : b → Kˣ := fun x =>
    Units.mk0 (∏ i, u ((idx x).2 i)) (Finset.prod_ne_zero_iff.2 fun i _ => hu _)
  have hlead : (fun x : b => homogeneousComponent (m - (idx x).1) (Fam x)) =
      w • ((↑) : b → MvPolynomial σ K) := funext fun x => by
    have hc : (∏ i, (X ((idx x).2 i) + C (u ((idx x).2 i)) : MvPolynomial σ K)).coeff 0 =
        ∏ i, u ((idx x).2 i) := by
      rw [← constantCoeff_eq, map_prod]
      simp
    rw [homogeneousComponent_mul (hstart x), homogeneousComponent_iteratedPDeriv,
      Nat.sub_add_cancel (hk x), hidx x, hc]
    rfl
  have hFam : LinearIndependent K Fam :=
    linearIndependent_of_homogeneousComponent (e := fun x => m - (idx x).1)
      (fun x _ hj => homogeneousComponent_mul_eq_zero (hstart x) _ hj)
      (hlead ▸ hbli.units_smul w)
  have hFam' : LinearIndependent K fun x : b =>
      (⟨Fam x, prod_X_add_C_mul_iteratedPDeriv_shift_mem u _ p⟩ : V) :=
    LinearIndependent.of_comp V.subtype hFam
  have : Finite b := hFam'.finite
  have := Fintype.ofFinite b
  rw [iteratedPDerivSpan, ← hbspan]
  refine ⟨Module.Finite.span_of_finite K (Set.toFinite b), (finrank_span_le_card b).trans ?_⟩
  rw [Set.toFinset_card]
  exact hFam'.fintype_card_le_finrank.trans hVrank

end Field

end MvPolynomial
