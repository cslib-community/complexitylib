/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.FieldTheory.Finite.UnitSum
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Unmasking low-degree polynomials over a finite field

The degree hypothesis of `FiniteField.sum_units_eval_mul_add` is satisfiable: the product of two
variables over `ZMod 7` has total degree `2 < 6`. This is the shape used by Tree Evaluation, where
a gate's multilinear extension is evaluated at masked copies of its children's values.
-/

namespace ComplexityTests.FiniteFieldUnitSum

open MvPolynomial

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The product of two masked inputs, summed over the units of `ZMod 7`, unmasks to the product
of the inputs. -/
example (τ x : Fin 2 → ZMod 7) :
    ∑ u : (ZMod 7)ˣ, (u * τ 0 + x 0) * (u * τ 1 + x 1) = -(x 0 * x 1) := by
  have hdeg :
      (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree < Fintype.card (ZMod 7) - 1 :=
    calc (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree
        ≤ (X 0 : MvPolynomial (Fin 2) (ZMod 7)).totalDegree + (X 1).totalDegree :=
          totalDegree_mul _ _
      _ < Fintype.card (ZMod 7) - 1 := by simp [totalDegree_X]
  simpa using FiniteField.sum_units_eval_mul_add hdeg τ x

/-- The univariate form: a degree-five polynomial over `ZMod 7` sums over the units to minus its
constant term. -/
example (a b : ZMod 7) :
    ∑ u : (ZMod 7)ˣ, Polynomial.eval (u : ZMod 7) (Polynomial.C a * Polynomial.X ^ 5 +
      Polynomial.C b) = -b := by
  have hdeg : (Polynomial.C a * Polynomial.X ^ 5 + Polynomial.C b).natDegree <
      Fintype.card (ZMod 7) - 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans_lt ?_
    simp only [Polynomial.natDegree_C, ZMod.card]
    exact (max_le (Polynomial.natDegree_C_mul_X_pow_le a 5) (Nat.zero_le _)).trans_lt (by decide)
  simpa using FiniteField.sum_units_eval hdeg

end ComplexityTests.FiniteFieldUnitSum
