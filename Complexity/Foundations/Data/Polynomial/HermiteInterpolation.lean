/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, confluent Hermite interpolation)

public import Complexity.Init
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Confluent Hermite interpolation from Taylor jets

A polynomial of degree less than `Q * J` is determined by its first `J` Taylor coefficients at each
of `Q` nodes, provided the nodes differ by units. Over a commutative ring `R`, the order-`J` Taylor
jet of `p` at nodes `t : Fin Q → R` is the family of coefficients
`(Polynomial.taylor (t i) p).coeff j = [z ^ j] p (t i + z)`, for `i < Q` and `j < J`
(`Polynomial.taylorJet`). This file proves

* uniqueness: a polynomial of degree less than `Q * J` whose jet vanishes is zero, over any
  commutative ring whose nodes have unit differences (`Polynomial.eq_zero_of_taylorJet_eq_zero`);
* reconstruction: for integer nodes, the integer confluent Vandermonde matrix
  `Polynomial.hermiteMatrix` maps the coefficient vector to the jet, it is nonsingular when the
  nodes are distinct, and Cramer's rule expresses each coefficient through two determinants
  (`Polynomial.det_hermiteMatrix_mul_coeff`). Over a `ℚ`-algebra this recovers every coefficient,
  and in particular the value at `0`, as a rational combination of the jet
  (`Polynomial.eval_zero_eq_of_taylorJet`).

The coefficient of `X ^ u` is indexed by `c : Fin Q × Fin J` with `u = finProdFinEquiv c`, so the
Hermite matrix is square over `Fin Q × Fin J`. Its entry in row `(i, j)` and column `c` is
`(u choose j) * t i ^ (u - j)`, the coefficient of `z ^ j` in `(t i + z) ^ u`; it vanishes for
`u < j` because the binomial does.

This is the interpolation step of the subexponential counting algorithm of [OpenAI2026ETH]
(§3.4 and Appendix B.3): the count is the value at `0` of a polynomial `H` of degree less than
`Q * J`, and only Taylor coefficients of `H` at the nodes `1, …, Q` are computed. Ordinary
Lagrange interpolation (`Lagrange.interpolate`) is the case `J = 1`.

## Main definitions

* `Polynomial.taylorJet`: the order-`J` Taylor jet at `Q` nodes, as a linear map.
* `Polynomial.hermiteMatrix`: the integer confluent Vandermonde matrix of integer nodes.

## Main results

* `Polynomial.eq_zero_of_taylorJet_eq_zero`, `Polynomial.eq_of_taylorJet_eq`: uniqueness.
* `Polynomial.hermiteMatrix_mulVec`: the Hermite matrix maps coefficients to the jet.
* `Polynomial.det_hermiteMatrix_ne_zero`: it is nonsingular at distinct integer nodes.
* `Polynomial.det_hermiteMatrix_mul_coeff`: Cramer's rule for the coefficients, over any
  commutative ring.
* `Polynomial.coeff_eq_of_taylorJet`, `Polynomial.eval_zero_eq_of_taylorJet`: reconstruction over
  a `ℚ`-algebra.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Polynomial

open Finset Matrix

variable {R : Type*} [CommRing R] {Q J : ℕ}

/-! ### Taylor jets and uniqueness -/

/-- The order-`J` Taylor jet of a polynomial at the nodes `t`: the coefficient of `z ^ j` in
`p (t i + z)`, for `i < Q` and `j < J`. -/
noncomputable def taylorJet (t : Fin Q → R) (J : ℕ) : R[X] →ₗ[R] Fin Q × Fin J → R :=
  LinearMap.pi fun r => lcoeff R r.2 ∘ₗ taylor (t r.1)

@[simp]
theorem taylorJet_apply (t : Fin Q → R) (J : ℕ) (p : R[X]) (r : Fin Q × Fin J) :
    taylorJet t J p r = (taylor (t r.1) p).coeff r.2 :=
  rfl

/-- **Uniqueness of confluent Hermite interpolation.** A polynomial of degree less than `Q * J`
whose order-`J` Taylor jet vanishes at `Q` nodes with unit differences is zero. -/
theorem eq_zero_of_taylorJet_eq_zero {t : Fin Q → R} (ht : Pairwise fun i j => IsUnit (t i - t j))
    {p : R[X]} (hp : p.degree < ↑(Q * J)) (h : taylorJet t J p = 0) : p = 0 := by
  nontriviality R
  by_contra h0
  have hdvd : ∀ i ∈ (univ : Finset (Fin Q)), (X - C (t i)) ^ J ∣ p := fun i _ => by
    rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
    exact fun d hd => congrFun h (i, ⟨d, hd⟩)
  have hcop : ((univ : Finset (Fin Q)) : Set (Fin Q)).Pairwise
      (Function.onFun IsCoprime fun i => (X - C (t i)) ^ J) := fun i _ j _ hij =>
    (isCoprime_X_sub_C_of_isUnit_sub (ht hij)).pow
  have hmon : ∀ i ∈ (univ : Finset (Fin Q)), ((X - C (t i)) ^ J).Monic := fun i _ =>
    (monic_X_sub_C _).pow J
  refine (monic_prod_of_monic _ _ hmon).not_dvd_of_natDegree_lt h0 ?_
    (Finset.prod_dvd_of_coprime hcop hdvd)
  rw [natDegree_prod_of_monic _ _ hmon]
  simpa only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul] using (natDegree_lt_iff_degree_lt h0).mpr hp

/-- Two polynomials of degree less than `Q * J` with the same order-`J` Taylor jet at `Q` nodes
with unit differences are equal. -/
theorem eq_of_taylorJet_eq {t : Fin Q → R} (ht : Pairwise fun i j => IsUnit (t i - t j))
    {p q : R[X]} (hp : p.degree < ↑(Q * J)) (hq : q.degree < ↑(Q * J))
    (h : taylorJet t J p = taylorJet t J q) : p = q :=
  sub_eq_zero.mp <| eq_zero_of_taylorJet_eq_zero ht ((degree_sub_le p q).trans_lt (max_lt hp hq))
    (by rw [map_sub, h, sub_self])

/-! ### The Hermite matrix and reconstruction -/

/-- The integer confluent Vandermonde (Hermite) matrix of the nodes `t`: the entry in row `(i, j)`
and column `c` is `(u choose j) * t i ^ (u - j)` with `u = finProdFinEquiv c`, the coefficient of
`z ^ j` in `(t i + z) ^ u`. -/
def hermiteMatrix (t : Fin Q → ℤ) (J : ℕ) : Matrix (Fin Q × Fin J) (Fin Q × Fin J) ℤ :=
  of fun r c => ((finProdFinEquiv c : ℕ).choose r.2 : ℤ) * t r.1 ^ ((finProdFinEquiv c : ℕ) - r.2)

theorem hermiteMatrix_apply (t : Fin Q → ℤ) (r c : Fin Q × Fin J) :
    hermiteMatrix t J r c =
      ((finProdFinEquiv c : ℕ).choose r.2 : ℤ) * t r.1 ^ ((finProdFinEquiv c : ℕ) - r.2) :=
  rfl

/-- **The Hermite matrix maps coefficients to the jet.** For `p` of degree less than `Q * J`, the
Hermite matrix applied to the vector of coefficients of `X ^ (finProdFinEquiv c)` is the order-`J`
Taylor jet of `p` at the nodes, over any commutative ring. -/
theorem hermiteMatrix_mulVec (t : Fin Q → ℤ) {p : R[X]} (hp : p.degree < ↑(Q * J)) :
    (hermiteMatrix t J).map (Int.cast : ℤ → R) *ᵥ (fun c => p.coeff (finProdFinEquiv c)) =
      taylorJet (fun i => (t i : R)) J p := by
  funext r
  rw [taylorJet_apply, taylor_coeff, hasseDeriv_apply, ← sum_fin _ (fun a => by simp) hp,
    eval_finsetSum, mulVec, dotProduct, ← finProdFinEquiv.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [map_apply, hermiteMatrix_apply, eval_monomial]
  push_cast
  ring

/-- **The Hermite matrix is nonsingular** at distinct integer nodes. -/
theorem det_hermiteMatrix_ne_zero {t : Fin Q → ℤ} (ht : Function.Injective t) :
    (hermiteMatrix t J).det ≠ 0 := by
  intro h0
  have h0' : ((hermiteMatrix t J).map (Int.cast : ℤ → ℚ)).det = 0 := by
    rw [← Int.cast_det, h0, Int.cast_zero]
  obtain ⟨v, hv, hV⟩ := exists_mulVec_eq_zero_iff.mpr h0'
  -- the polynomial whose coefficient of `X ^ (finProdFinEquiv c)` is `v c`
  set p : ℚ[X] := ((degreeLTEquiv ℚ (Q * J)).symm (v ∘ finProdFinEquiv.symm) : ℚ[X])
  have hcoeff : (fun c => p.coeff (finProdFinEquiv c)) = v := _root_.funext fun c => by
    have := congrFun ((degreeLTEquiv ℚ (Q * J)).apply_symm_apply (v ∘ finProdFinEquiv.symm))
      (finProdFinEquiv c)
    rwa [Function.comp_apply, Equiv.symm_apply_apply] at this
  have hp : p.degree < ↑(Q * J) :=
    mem_degreeLT.mp ((degreeLTEquiv ℚ (Q * J)).symm (v ∘ finProdFinEquiv.symm)).2
  have hunit : Pairwise fun i j => IsUnit ((t i : ℚ) - t j) := fun i j hij =>
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast ht.ne hij))
  have hjet := hermiteMatrix_mulVec t hp
  rw [hcoeff, hV] at hjet
  refine hv ?_
  rw [← hcoeff, eq_zero_of_taylorJet_eq_zero hunit hp hjet.symm]
  rfl

/-- **Cramer's rule for confluent Hermite interpolation**, over any commutative ring: for `p` of
degree less than `Q * J`, the determinant of the Hermite matrix times the coefficient of
`X ^ (finProdFinEquiv c)` is the determinant of the Hermite matrix with column `c` replaced by the
order-`J` Taylor jet of `p`. -/
theorem det_hermiteMatrix_mul_coeff (t : Fin Q → ℤ) {p : R[X]} (hp : p.degree < ↑(Q * J))
    (c : Fin Q × Fin J) :
    ((hermiteMatrix t J).det : R) * p.coeff (finProdFinEquiv c) =
      (((hermiteMatrix t J).map (Int.cast : ℤ → R)).updateCol c
        (taylorJet (fun i => (t i : R)) J p)).det := by
  rw [← cramer_apply, ← hermiteMatrix_mulVec t hp, cramer_eq_adjugate_mulVec, mulVec_mulVec,
    adjugate_mul, Int.cast_det, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul]

/-- **Reconstruction over a `ℚ`-algebra.** At distinct integer nodes, each coefficient of a
polynomial of degree less than `Q * J` is a rational multiple of a determinant formed from the
Hermite matrix and the order-`J` Taylor jet. -/
theorem coeff_eq_of_taylorJet (A : Type*) [CommRing A] [Algebra ℚ A] {t : Fin Q → ℤ}
    (ht : Function.Injective t) {p : A[X]} (hp : p.degree < ↑(Q * J)) (c : Fin Q × Fin J) :
    p.coeff (finProdFinEquiv c) = ((hermiteMatrix t J).det : ℚ)⁻¹ •
      (((hermiteMatrix t J).map (Int.cast : ℤ → A)).updateCol c
        (taylorJet (fun i => (t i : A)) J p)).det := by
  have hd : ((hermiteMatrix t J).det : ℚ) ≠ 0 := by exact_mod_cast det_hermiteMatrix_ne_zero ht
  rw [← det_hermiteMatrix_mul_coeff t hp c, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
    inv_mul_cancel₀ hd, one_smul]

/-- **The value at `0` from the jet (B.1).** At distinct integer nodes, the value at `0` of a
polynomial of degree less than `Q * J`, over a `ℚ`-algebra, is the determinant of the Hermite
matrix with its column for `X ^ 0` replaced by the order-`J` Taylor jet, divided by the determinant
of the Hermite matrix. -/
theorem eval_zero_eq_of_taylorJet (A : Type*) [CommRing A] [Algebra ℚ A] {t : Fin Q → ℤ}
    (ht : Function.Injective t) (hQ : 0 < Q) (hJ : 0 < J) {p : A[X]}
    (hp : p.degree < ↑(Q * J)) :
    p.eval 0 = ((hermiteMatrix t J).det : ℚ)⁻¹ •
      (((hermiteMatrix t J).map (Int.cast : ℤ → A)).updateCol (⟨0, hQ⟩, ⟨0, hJ⟩)
        (taylorJet (fun i => (t i : A)) J p)).det := by
  rw [← coeff_eq_of_taylorJet A ht hp, ← coeff_zero_eq_eval_zero]
  congr 1

end Polynomial
