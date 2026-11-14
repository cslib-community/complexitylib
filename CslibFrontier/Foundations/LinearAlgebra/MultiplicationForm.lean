/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Multiplication forms of field extensions

A linear functional on a commutative algebra turns multiplication into a bilinear form.  For a
field extension, every nonzero functional gives a nondegenerate form.  Its Gram matrix therefore
symmetrizes every matrix in the regular representation.

This is the field-extension case of the symmetrizer construction in §3.2, Theorem 1, of
[QRUOV2026], printed p. 13.  The cited theorem treats more general polynomial quotients; the result
here deliberately uses inverses in the extension field and does not cover reducible quotients.

## Main definitions

* `Algebra.mulForm`: the bilinear form `(x, y) ↦ λ (x * y)`.

## Main results

* `Algebra.mulForm_nondegenerate`: a nonzero functional gives a nondegenerate multiplication form.
* `Algebra.mulForm_toMatrix_nondegenerate`: its Gram matrix is nondegenerate in any finite basis.
* `Algebra.isUnit_mulForm_toMatrix`: its Gram matrix is invertible in any finite basis.
* `Algebra.mulForm_toMatrix_mul_leftMulMatrix_isSymm`: the Gram matrix symmetrizes the regular
  representation.
* `Algebra.transpose_leftMulMatrix_mul_mulForm_toMatrix`: the corresponding transpose
  intertwining identity.

## References

* [QRUOV2026]
-/

public section

namespace Algebra

open LinearMap (BilinForm)
open Matrix

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

/-- The multiplication form associated to a linear functional `φ`, sending `(x, y)` to
`φ (x * y)`.

This is the form whose Gram matrix is the symmetrizer in the field-extension construction of
[QRUOV2026, §3.2, Theorem 1, printed p. 13]. -/
noncomputable def mulForm (φ : E →ₗ[K] K) : BilinForm K E :=
  LinearMap.compr₂ (Algebra.lmul K E).toLinearMap φ

@[simp]
theorem mulForm_apply (φ : E →ₗ[K] K) (x y : E) : mulForm φ x y = φ (x * y) :=
  rfl

/-- Multiplication forms on commutative algebras are symmetric. -/
theorem mulForm_isSymm (φ : E →ₗ[K] K) : (mulForm φ).IsSymm :=
  ⟨fun x y ↦ congrArg φ (mul_comm x y)⟩

/-- The entries of the multiplication Gram matrix in a basis `b`. -/
theorem mulForm_toMatrix_apply [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K E)
    (φ : E →ₗ[K] K) (i j : ι) : (mulForm φ).toMatrix b i j = φ (b i * b j) := by
  rw [LinearMap.BilinForm.toMatrix_apply, mulForm_apply]

/-- A nonzero functional on a field extension gives a left-separating multiplication form. -/
theorem mulForm_separatingLeft {φ : E →ₗ[K] K} (hφ : φ ≠ 0) :
    (mulForm φ).SeparatingLeft := by
  intro x hx
  by_contra hx0
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hφ
  have hzero := hx (x⁻¹ * z)
  rw [mulForm_apply, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at hzero
  exact hz hzero

/-- A nonzero functional on a field extension gives a nondegenerate multiplication form. -/
theorem mulForm_nondegenerate {φ : E →ₗ[K] K} (hφ : φ ≠ 0) :
    (mulForm φ).Nondegenerate :=
  (mulForm_isSymm φ).isRefl.nondegenerate_iff_separatingLeft.mpr
    (mulForm_separatingLeft hφ)

/-- The multiplication Gram matrix of a nonzero functional on a field extension is nondegenerate. -/
theorem mulForm_toMatrix_nondegenerate [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K E) {φ : E →ₗ[K] K} (hφ : φ ≠ 0) :
    ((mulForm φ).toMatrix b).Nondegenerate :=
  (mulForm_nondegenerate hφ).toMatrix b

/-- The multiplication Gram matrix of a nonzero functional on a field extension is invertible. -/
theorem isUnit_mulForm_toMatrix [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K E)
    {φ : E →ₗ[K] K} (hφ : φ ≠ 0) : IsUnit ((mulForm φ).toMatrix b) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  exact (mulForm_toMatrix_nondegenerate b hφ).det_ne_zero

/-- Multiplication by the Gram matrix makes every regular-representation matrix symmetric. -/
theorem mulForm_toMatrix_mul_leftMulMatrix_isSymm [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K E) (φ : E →ₗ[K] K) (g : E) :
    ((mulForm φ).toMatrix b * Algebra.leftMulMatrix b g).IsSymm := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.BilinForm.toMatrix_mul,
    Matrix.toLin_toMatrix, LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm]
  refine ⟨fun x y ↦ ?_⟩
  simp only [LinearMap.BilinForm.compRight_apply, mulForm_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  congr 1
  ac_rfl

/-- The transpose of each regular-representation matrix intertwines with the multiplication Gram
matrix. -/
theorem transpose_leftMulMatrix_mul_mulForm_toMatrix [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K E) (φ : E →ₗ[K] K) (g : E) :
    (Algebra.leftMulMatrix b g)ᵀ * (mulForm φ).toMatrix b =
      (mulForm φ).toMatrix b * Algebra.leftMulMatrix b g := by
  have hW : ((mulForm φ).toMatrix b).IsSymm :=
    ((mulForm φ).isSymm_toMatrix_iff_isSymm b).mpr (mulForm_isSymm φ)
  have hWL := mulForm_toMatrix_mul_leftMulMatrix_isSymm b φ g
  simpa only [Matrix.IsSymm, Matrix.transpose_mul, hW.eq] using hWL

end Algebra
