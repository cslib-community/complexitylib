/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquarePolynomialCoordinates

/-!
# One-variable double contact

This file isolates the elementary algebraic part of the square argument.  A
polynomial whose value and formal derivative vanish at a point has the square
of the corresponding linear factor as a divisor.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareDeterminantDoubleContact.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

namespace SquarePolynomial

open Polynomial

section AffineDeterminant

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-- A column whose entries are affine polynomials in one common variable. -/
@[expose] def affineColumn (u v : ι → A) : ι → Polynomial A :=
  fun i => Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X

/-- Multilinearity in a single column makes the determinant affine in the
common variable.  This is the algebraic core of the determinant-chart
calculation; the two coefficients are explicit determinants over `A`. -/
theorem det_updateCol_affine (M : Matrix ι ι A) (j : ι) (u v : ι → A) :
    Matrix.det ((M.map Polynomial.C).updateCol j (affineColumn u v)) =
      Polynomial.C (Matrix.det (M.updateCol j u)) +
        Polynomial.C (Matrix.det (M.updateCol j v)) * Polynomial.X := by
  have hcol : affineColumn u v =
      ((fun i => Polynomial.C (u i)) : ι → Polynomial A) +
        (Polynomial.X : Polynomial A) •
          ((fun i => Polynomial.C (v i)) : ι → Polynomial A) := by
    funext i
    change Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X =
      Polynomial.C (u i) + Polynomial.X * Polynomial.C (v i)
    rw [mul_comm]
  rw [hcol, Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
  have hu :
      ((M.map Polynomial.C).updateCol j (fun i => Polynomial.C (u i))) =
        (M.updateCol j u).map Polynomial.C := by
    ext i k
    by_cases hk : k = j <;> simp [hk]
  have hv :
      ((M.map Polynomial.C).updateCol j (fun i => Polynomial.C (v i))) =
        (M.updateCol j v).map Polynomial.C := by
    ext i k
    by_cases hk : k = j <;> simp [hk]
  have hdetu : Matrix.det ((M.updateCol j u).map Polynomial.C) =
      Polynomial.C (Matrix.det (M.updateCol j u)) := by
    symm
    exact (Polynomial.C : A →+* Polynomial A).map_det (M.updateCol j u)
  have hdetv : Matrix.det ((M.updateCol j v).map Polynomial.C) =
      Polynomial.C (Matrix.det (M.updateCol j v)) := by
    symm
    exact (Polynomial.C : A →+* Polynomial A).map_det (M.updateCol j v)
  rw [hu, hv, hdetu, hdetv]
  ring

end AffineDeterminant

/-- Value and first-derivative vanishing are exactly the input needed for a
square linear factor.  The statement works over an arbitrary commutative
ring; no fraction field is needed at this stage. -/
theorem X_sub_C_sq_dvd_of_eval_derivative_eq_zero
    {R : Type*} [CommRing R] (p : Polynomial R) (r : R)
    (hvalue : p.eval r = 0) (hderiv : p.derivative.eval r = 0) :
    (Polynomial.X - Polynomial.C r) ^ 2 ∣ p := by
  have hfirst : Polynomial.X - Polynomial.C r ∣ p := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hvalue
  obtain ⟨q, hq⟩ := hfirst
  have hqvalue : q.eval r = 0 := by
    have h := hderiv
    rw [hq, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      one_mul, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero] at h
    exact h
  have hsecond : Polynomial.X - Polynomial.C r ∣ q := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hqvalue
  obtain ⟨s, hs⟩ := hsecond
  refine ⟨s, ?_⟩
  rw [hq, hs, pow_two, mul_assoc]

/-- The affine-linear version over a field.  Multiplying by a nonzero scalar
does not change the root, and hence the square of `aX+b` divides `p`. -/
theorem affine_linear_sq_dvd_of_eval_derivative_eq_zero
    {K : Type*} [Field K] (a b : K) (ha : a ≠ 0)
    (p : Polynomial K)
    (hvalue : p.eval (-b / a) = 0)
    (hderiv : p.derivative.eval (-b / a) = 0) :
    (Polynomial.C a * Polynomial.X + Polynomial.C b) ^ 2 ∣ p := by
  let r : K := -b / a
  have har : a * r = -b := by
    dsimp [r]
    field_simp
  have hfactor : Polynomial.C a * (Polynomial.X - Polynomial.C r) =
      Polynomial.C a * Polynomial.X + Polynomial.C b := by
    rw [mul_sub, ← Polynomial.C_mul, har, map_neg, sub_neg_eq_add]
  obtain ⟨q, hq⟩ := X_sub_C_sq_dvd_of_eval_derivative_eq_zero p r hvalue hderiv
  refine ⟨Polynomial.C (a⁻¹ ^ 2) * q, ?_⟩
  rw [← hfactor, hq, mul_pow]
  have hcancel : (Polynomial.C a : Polynomial K) ^ 2 *
      Polynomial.C (a⁻¹ ^ 2) = 1 := by
    rw [← map_pow, ← map_mul]
    simp [ha]
  calc
    (Polynomial.X - Polynomial.C r) ^ 2 * q =
        ((Polynomial.C a) ^ 2 * Polynomial.C (a⁻¹ ^ 2)) *
          ((Polynomial.X - Polynomial.C r) ^ 2 * q) := by rw [hcancel, one_mul]
    _ = (Polynomial.C a) ^ 2 * (Polynomial.X - Polynomial.C r) ^ 2 *
          (Polynomial.C (a⁻¹ ^ 2) * q) := by ring

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
