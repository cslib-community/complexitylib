/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareSimplexMilestone

/-!
# Homogenization with the total-mass polynomial

The total-mass linear form is the `tauPoly` already used by simplex
dehomogenization.  Homogeneous components are raised to a common total degree
by multiplying by powers of this form.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareTauHomogenization.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace SquarePolynomial

section Generic

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

lemma tauPoly_eq_sum_X (star : σ) :
    tauPoly (R := R) star = ∑ i : σ, MvPolynomial.X i := by
  apply (toNested (R := R) star).injective
  rw [toNested_tauPoly, toNested_sum_X]

@[simp] lemma dehomSimplex_tauPoly (star : σ) :
    dehomSimplex (R := R) star (tauPoly (R := R) star) = 1 := by
  have h := dehomSimplex_tau_sub_one (R := R) star
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

lemma tauPoly_isHomogeneous (star : σ) :
    (tauPoly (R := R) star).IsHomogeneous 1 := by
  rw [tauPoly_eq_sum_X]
  apply MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i => MvPolynomial.X i) 1
  intro i hi
  exact MvPolynomial.isHomogeneous_X R i

/-- Homogenize every homogeneous component of `P` to `P.totalDegree` using
powers of the total-mass linear form. -/
@[expose] def tauHomogenize (star : σ) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ k ∈ Finset.range (P.totalDegree + 1),
    tauPoly (R := R) star ^ (P.totalDegree - k) *
      MvPolynomial.homogeneousComponent k P

theorem tauHomogenize_isHomogeneous (star : σ) (P : MvPolynomial σ R) :
    (tauHomogenize (R := R) star P).IsHomogeneous P.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
    (Finset.range (P.totalDegree + 1))
    (fun k => tauPoly (R := R) star ^ (P.totalDegree - k) *
      MvPolynomial.homogeneousComponent k P)
    P.totalDegree
  intro k hk
  have hkle : k ≤ P.totalDegree := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow := (tauPoly_isHomogeneous (R := R) star).pow (P.totalDegree - k)
  have hcomp := MvPolynomial.homogeneousComponent_isHomogeneous k P
  simpa [Nat.sub_add_cancel hkle] using hpow.mul hcomp

theorem eval_tauHomogenize_of_eval_tau_eq_one
    (star : σ) (P : MvPolynomial σ R) (x : σ → R)
    (htau : MvPolynomial.eval x (tauPoly (R := R) star) = 1) :
    MvPolynomial.eval x (tauHomogenize (R := R) star P) =
      MvPolynomial.eval x P := by
  rw [tauHomogenize, map_sum]
  simp only [map_mul, map_pow, htau, one_pow, one_mul]
  rw [← map_sum, MvPolynomial.sum_homogeneousComponent]

@[simp] theorem dehomSimplex_tauHomogenize
    (star : σ) (P : MvPolynomial σ R) :
    dehomSimplex (R := R) star (tauHomogenize (R := R) star P) =
      dehomSimplex (R := R) star P := by
  rw [tauHomogenize, map_sum]
  simp only [map_mul, map_pow, dehomSimplex_tauPoly, one_pow, one_mul]
  rw [← map_sum, MvPolynomial.sum_homogeneousComponent]

theorem tauHomogenize_sub_mem_simplex_kernel
    (star : σ) (P : MvPolynomial σ R) :
    ∃ K : MvPolynomial σ R,
      tauHomogenize (R := R) star P - P =
        (tauPoly (R := R) star - 1) * K := by
  apply (kernel_dehomSimplex (R := R) star
    (tauHomogenize (R := R) star P - P)).mp
  simp

/-- The final algebraic recombination: a determinant-square factorization of
the homogenization immediately gives the requested identity modulo `tau-1`. -/
theorem square_identity_of_tauHomogenize_factor
    (star : σ) (P D Q : MvPolynomial σ R)
    (hfactor : tauHomogenize (R := R) star P = D ^ 2 * Q) :
    ∃ K : MvPolynomial σ R,
      P = D ^ 2 * Q + (tauPoly (R := R) star - 1) * K := by
  obtain ⟨K, hK⟩ := tauHomogenize_sub_mem_simplex_kernel (R := R) star P
  refine ⟨-K, ?_⟩
  rw [hfactor] at hK
  calc
    P = D ^ 2 * Q - (D ^ 2 * Q - P) := by ring
    _ = D ^ 2 * Q - (tauPoly (R := R) star - 1) * K := by rw [hK]
    _ = D ^ 2 * Q + (tauPoly (R := R) star - 1) * (-K) := by ring

end Generic

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
