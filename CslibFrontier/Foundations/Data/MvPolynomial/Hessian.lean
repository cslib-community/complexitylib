/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, point-evaluated polynomial Hessians)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Matrix.Mul

/-!
# Point-evaluated gradients and Hessians

Formal derivatives define gradients and Hessians over any commutative semiring. The product
rule expresses a product's Hessian as a linear combination of the two Hessians and two outer
products of gradients. No assumption on the characteristic is needed.

## Main definitions

* `MvPolynomial.gradient`: the gradient at a point.
* `MvPolynomial.hessian`: the Hessian matrix at a point.

## Main results

* `MvPolynomial.hessian_add`, `MvPolynomial.hessian_C`, `MvPolynomial.hessian_X`.
* `MvPolynomial.hessian_mul`: the product rule for Hessians.
* `MvPolynomial.hessian_sum_X_mul_X`: the pairing polynomial has a block-swap Hessian.

## References

* Ported from LowerBound/Fusion/Arithmetic/Interaction/Hessian.lean and its `Pairing.lean`
  application in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace MvPolynomial

variable {ι R : Type*} [CommSemiring R]

/-- The gradient of a formal polynomial, evaluated at a point. -/
noncomputable def gradient (x : ι → R) (p : MvPolynomial ι R) : ι → R :=
  fun i => eval x (pderiv i p)

/-- The Hessian of a formal polynomial, evaluated at a point. -/
noncomputable def hessian (x : ι → R) (p : MvPolynomial ι R) : Matrix ι ι R :=
  fun i j => eval x (pderiv i (pderiv j p))

/-- The Hessian of a sum is the sum of the Hessians. -/
@[simp] theorem hessian_add (x : ι → R) (p q : MvPolynomial ι R) :
    hessian x (p + q) = hessian x p + hessian x q := by
  ext i j
  simp [hessian]

/-- A constant polynomial has zero Hessian. -/
@[simp] theorem hessian_C (x : ι → R) (c : R) : hessian x (C c) = 0 := by
  ext i j
  simp [hessian]

/-- A variable has zero Hessian. -/
@[simp] theorem hessian_X (x : ι → R) (i : ι) : hessian x (X i) = 0 := by
  classical
  ext j k
  by_cases h : i = k <;> simp [hessian, h]

/-- A product's Hessian has two additional outer products of gradients. -/
theorem hessian_mul (x : ι → R) (p q : MvPolynomial ι R) :
    hessian x (p * q) = eval x q • hessian x p + eval x p • hessian x q +
      (Matrix.vecMulVec (gradient x p) (gradient x q) +
        Matrix.vecMulVec (gradient x q) (gradient x p)) := by
  ext i j
  simp only [hessian, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, gradient,
    pderiv_mul, map_add, eval_mul, smul_eq_mul]
  ring

/-- The Hessian of the pairing polynomial swaps the two coordinate blocks. This identity
holds over any commutative semiring, including characteristic two. -/
theorem hessian_sum_X_mul_X [Fintype ι] [DecidableEq ι] (point : (ι ⊕ ι) → R) :
    hessian point (∑ i : ι, X (Sum.inl i) * X (Sum.inr i)) =
      (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).submatrix (Equiv.sumComm ι ι) (Equiv.refl _) := by
  ext i j
  cases i <;> cases j <;>
    simp [hessian, Matrix.submatrix_apply, Matrix.one_apply, Pi.single_apply, eq_comm]

end MvPolynomial
