/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.AnyOrder

/-!
# Hitting sets for multilinear any-order ROABPs

The product `X 0 * X 1` of two rational variables is computed by branching programs of width
one in every order, so it is nonzero at a point of the hitting set for width one.
-/

public section

namespace CslibFrontierTests.AnyOrderHittingSet

open Cslib.Circuits.Arithmetic MvPolynomial

/-- `X 0 * X 1` is computed in every order by the width-one program with matrices `(X)`. -/
theorem isAnyOrderROABP_X_mul_X :
    IsAnyOrderROABP 1 (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) := by
  intro l hl hmem
  refine ⟨fun _ => Matrix.of fun _ _ => Polynomial.X, 0, 0, ?_⟩
  have hprod : ∀ l' : List (Fin 2), roabpProd (F := ℚ)
      (fun _ => Matrix.of fun _ _ : Fin 1 => Polynomial.X) l' 0 0 = (l'.map X).prod := by
    intro l'
    induction l' with
    | nil => simp [roabpProd]
    | cons i l' ih =>
      rw [roabpProd, List.map_cons, List.prod_cons, Matrix.mul_apply] at *
      simp [ih]
  rw [hprod]
  have hperm : l.Perm [0, 1] := by
    refine (List.perm_ext_iff_of_nodup hl (by decide)).2 fun i => ?_
    simp only [hmem i, true_iff]
    fin_cases i <;> simp
  rw [(hperm.map X).prod_eq]
  simp

/-- The hitting set for width one contains a point where `X 0 * X 1` is nonzero. -/
theorem exists_eval_X_mul_X_ne_zero :
    ∃ a ∈ anyOrderHittingSet ℚ 2 1, eval a (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) ≠ 0 :=
  isHittingSet_anyOrderHittingSet_roabp _
    ⟨fun i => by
      refine (degreeOf_mul_le _ _ _).trans ?_
      rw [degreeOf_X, degreeOf_X]
      fin_cases i <;> simp, isAnyOrderROABP_X_mul_X⟩
    (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1))

end CslibFrontierTests.AnyOrderHittingSet
