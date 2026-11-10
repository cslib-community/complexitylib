/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Multilinear extensions of functions on the cube

Every function `g : (ι → Bool) → R` on a finite cube is the restriction of a multilinear
polynomial: the sum over the points `a` of the cube of `g a` times the indicator polynomial of `a`,
the product of `X i` over the coordinates where `a i` is true and of `1 - X i` over the others.
Its total degree is at most the dimension.

## Main definitions

* `Cslib.BitString.indicatorPoly`: the multilinear polynomial that is `1` at a point of the cube
  and `0` at every other point.
* `Cslib.BitString.multilinearExtension`: the multilinear extension of a function on the cube.

## Main results

* `Cslib.BitString.eval_multilinearExtension`: the extension agrees with the function on the cube.
* `Cslib.BitString.eval_multilinearExtension_eq_sum`: the extension at any point, in the indicator
  basis.
* `Cslib.BitString.totalDegree_multilinearExtension_le`: its total degree is at most the
  dimension.
* `Cslib.BitString.rename_multilinearExtension`: renaming the coordinates along an equivalence
  gives the multilinear extension of the function read through the equivalence.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 1.2 for the indicator
  polynomials.
-/

@[expose] public section

open MvPolynomial

namespace Cslib.BitString

variable {ι κ R : Type*} [CommRing R]

/-- The indicator polynomial of a point `a` of the cube: the product of `X i` where `a i` is true
and of `1 - X i` where it is false. -/
noncomputable def indicatorPoly [Fintype ι] (a : ι → Bool) : MvPolynomial ι R :=
  ∏ i, if a i then X i else 1 - X i

/-- The multilinear extension of a function on the cube. -/
noncomputable def multilinearExtension [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → R) :
    MvPolynomial ι R :=
  ∑ a, C (g a) * indicatorPoly a

/-- The value of an indicator polynomial at any point. -/
theorem eval_indicatorPoly_apply [Fintype ι] (a : ι → Bool) (z : ι → R) :
    eval z (indicatorPoly a : MvPolynomial ι R) = ∏ i, if a i then z i else 1 - z i := by
  simp [indicatorPoly, map_prod, apply_ite]

/-- On the cube, the indicator polynomial of `a` is `1` at `a` and `0` elsewhere. -/
theorem eval_indicatorPoly [Fintype ι] (a x : ι → Bool) :
    eval (fun i => bitVal R (x i)) (indicatorPoly a : MvPolynomial ι R) =
      if a = x then 1 else 0 := by
  rw [eval_indicatorPoly_apply]
  split_ifs with h
  · subst h
    exact Finset.prod_eq_one fun i _ => by cases a i <;> simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by cases ha : a i <;> cases hx : x i <;> simp_all)

/-- The point of `R^ι` with the coordinates of the bit string `x`. -/
abbrev bitPoint (x : ι → Bool) : ι → R := fun i => bitVal R (x i)

/-- The multilinear extension at any point is the sum of the values of the function weighted by the
indicator polynomials. -/
theorem eval_multilinearExtension_eq_sum [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → R)
    (z : ι → R) : eval z (multilinearExtension g) = ∑ a, g a * eval z (indicatorPoly a) := by
  simp [multilinearExtension]

/-- The multilinear extension agrees with the function on the cube. -/
theorem eval_multilinearExtension [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → R)
    (x : ι → Bool) : eval (fun i => bitVal R (x i)) (multilinearExtension g) = g x := by
  simp only [multilinearExtension, map_sum, map_mul, eval_C, eval_indicatorPoly, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- An indicator polynomial has total degree at most the dimension. -/
theorem totalDegree_indicatorPoly_le [Fintype ι] (a : ι → Bool) :
    (indicatorPoly a : MvPolynomial ι R).totalDegree ≤ Fintype.card ι := by
  have hX (i : ι) : (X i : MvPolynomial ι R).totalDegree ≤ 1 :=
    (totalDegree_monomial_le _ _).trans (by simp)
  refine (totalDegree_finsetProd _ _).trans <|
    (Finset.sum_le_card_nsmul _ _ 1 fun i _ => ?_).trans (by simp)
  split_ifs
  · exact hX i
  · exact (totalDegree_sub _ _).trans (max_le (by simp) (hX i))

/-- The multilinear extension has total degree at most the dimension. -/
theorem totalDegree_multilinearExtension_le [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → R) :
    (multilinearExtension g).totalDegree ≤ Fintype.card ι := by
  refine (totalDegree_finsetSum _ _).trans <| Finset.sup_le fun a _ => ?_
  exact (totalDegree_mul _ _).trans <| by
    simpa using totalDegree_indicatorPoly_le (R := R) a

/-- Renaming the coordinates along an equivalence `e` turns the multilinear extension of `g` into
the multilinear extension of `g` read through `e`. -/
theorem rename_multilinearExtension [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (g : (ι → Bool) → R) :
    rename e (multilinearExtension g) = multilinearExtension fun z => g (z ∘ e) := by
  simp only [multilinearExtension, indicatorPoly, map_sum, map_mul, rename_C, map_prod,
    apply_ite (rename e), rename_X, map_sub, map_one]
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl Bool)) _ _ fun a => ?_
  congr 1
  · simp [Equiv.arrowCongr, Function.comp_assoc]
  · exact Fintype.prod_equiv e _ _ fun i => by simp [Equiv.arrowCongr]

end Cslib.BitString
