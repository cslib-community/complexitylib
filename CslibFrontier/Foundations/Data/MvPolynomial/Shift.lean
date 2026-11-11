/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Shifting the variables of a multivariate polynomial

`MvPolynomial.shift a` is the substitution `X i ↦ X i + C (a i)`. The point `a` may have
coordinates in an algebra `A` over the coefficient ring `R`, so that a polynomial over a field can
be shifted by a point with polynomial coordinates; the result is a polynomial over `A`.

## Main definitions

* `MvPolynomial.shift`: the algebra homomorphism `f ↦ f (X + a)`.

## Main results

* `MvPolynomial.degreeOf_shift_le`: shifting does not increase the degree in a variable.
* `MvPolynomial.shift_injective`: shifting is injective when `R → A` is.
* `MvPolynomial.aeval_X_eq_map`: substituting the variables over an algebra is a base change.
* `MvPolynomial.map_shift`: shifting commutes with a change of the ring of the point.
-/

@[expose] public section

namespace MvPolynomial

variable {σ R A B : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The shift `f ↦ f (X + a)` by a point `a` with coordinates in an `R`-algebra. -/
noncomputable def shift (a : σ → A) : MvPolynomial σ R →ₐ[R] MvPolynomial σ A :=
  aeval fun i => X i + C (a i)

theorem shift_X (a : σ → A) (i : σ) : shift a (X i : MvPolynomial σ R) = X i + C (a i) :=
  aeval_X _ i

/-- Shifting commutes with a homomorphism applied to the coordinates of the point. -/
theorem map_shift [CommSemiring B] [Algebra R B] (φ : A →ₐ[R] B) (a : σ → A)
    (f : MvPolynomial σ R) : map (φ : A →+* B) (shift a f) = shift (fun i => φ (a i)) f := by
  have h := comp_aeval (R := R) (f := fun i => (X i + C (a i) : MvPolynomial σ A)) (mapAlgHom φ)
  simpa [shift] using DFunLike.congr_fun h f

/-- Substituting the variables of the polynomial ring over an algebra is a base change. -/
theorem aeval_X_eq_map (p : MvPolynomial σ R) :
    aeval (fun i => (X i : MvPolynomial σ A)) p = map (algebraMap R A) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Shifting does not increase the degree in a variable. -/
theorem degreeOf_shift_le (a : σ → A) (f : MvPolynomial σ R) (i : σ) :
    (shift a f).degreeOf i ≤ f.degreeOf i := by
  classical
  rw [shift, aeval_def, eval₂_eq]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [algebraMap_apply, degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  have hle : ∀ j ∈ m.support,
      degreeOf i ((X j + C (a j) : MvPolynomial σ A) ^ m j) ≤ if j = i then m j else 0 := by
    intro j _
    refine (degreeOf_pow_le _ _ _).trans ?_
    have h1 : degreeOf i (X j + C (a j) : MvPolynomial σ A) ≤ degreeOf i (X j : MvPolynomial σ A) :=
      (degreeOf_add_le _ _ _).trans (by rw [degreeOf_C, max_eq_left (Nat.zero_le _)])
    split_ifs with h
    · have hX : degreeOf i (X j : MvPolynomial σ A) ≤ 1 := degreeOf_le_iff.2 fun d hd => by
        rw [Finset.mem_singleton.1 (support_monomial_subset hd), Finsupp.single_apply]
        split_ifs
        exact le_rfl
      exact (Nat.mul_le_mul_left _ (h1.trans hX)).trans_eq (mul_one _)
    · rw [Nat.le_zero.1 (h1.trans_eq (degreeOf_X_of_ne (Ne.symm h))), mul_zero]
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_ite_eq' m.support i]
  split_ifs
  · exact monomial_le_degreeOf i hm
  · exact Nat.zero_le _

end CommSemiring

section CommRing

variable [CommRing R] [CommRing A] [Algebra R A]

/-- Shifting is injective when the coefficient ring embeds into the ring of the point. -/
theorem shift_injective (hRA : Function.Injective (algebraMap R A)) (a : σ → A) :
    Function.Injective (shift a : MvPolynomial σ R → MvPolynomial σ A) := by
  have h : ((aeval fun i => X i - C (a i) : MvPolynomial σ A →ₐ[A] MvPolynomial σ A).restrictScalars
      R).comp (shift a) = aeval (fun i => (X i : MvPolynomial σ A)) := by
    rw [shift, comp_aeval]
    congr 1
    funext i
    simp
  have hinj : Function.Injective (aeval (fun i => (X i : MvPolynomial σ A)) :
      MvPolynomial σ R → MvPolynomial σ A) := by
    rw [show (aeval (fun i => (X i : MvPolynomial σ A)) : MvPolynomial σ R → MvPolynomial σ A) =
      map (algebraMap R A) from funext aeval_X_eq_map]
    exact map_injective _ hRA
  exact Function.Injective.of_comp (f := (aeval fun i => X i - C (a i) :
    MvPolynomial σ A →ₐ[A] MvPolynomial σ A)) (by rw [← h] at hinj; exact hinj)

end CommRing

end MvPolynomial
