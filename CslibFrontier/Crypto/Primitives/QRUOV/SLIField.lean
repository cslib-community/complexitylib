/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.MultiplicationForm
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases

/-!
# QR-UOV security-level-I coefficient field

The balanced QR-UOV security-level-I parameter row uses the base field `ZMod 127` and the degree-3
extension defined by `x³ - x - 1`.  Table 3 of [QRUOV2026], printed p. 22, gives the symmetrizer
`diag(J₁, J₂)`, where `Jᵢ` is the size-`i` anti-identity matrix.  In the power basis this is
```
!![1, 0, 0;
   0, 0, 1;
   0, 1, 0].
```

This module checks the irreducibility premise, constructs the coefficient-zero functional used by
§3.2, and proves the stated matrix exactly.  It also computes the regular-representation matrix of
the quotient generator, fixing the column and transpose conventions used by the generic
multiplication-form API.

The module contains only coefficient-field algebra.  It does not define QR-UOV dimensions,
distributions, keys, signing, verification, rank-failure events, games, or security reductions.

## Main definitions

* `Cslib.Crypto.QRUOV.SLI.modulus`: the polynomial `x³ - x - 1` over `ZMod 127`.
* `Cslib.Crypto.QRUOV.SLI.Extension`: its degree-3 quotient field.
* `Cslib.Crypto.QRUOV.SLI.basis`: the power basis `1, x, x²`.
* `Cslib.Crypto.QRUOV.SLI.coeffZero`: the coefficient-zero functional.
* `Cslib.Crypto.QRUOV.SLI.symmetrizer`: its multiplication Gram matrix.

## Main results

* `Cslib.Crypto.QRUOV.SLI.modulus_irreducible`: the stated cubic is irreducible over `ZMod 127`.
* `Cslib.Crypto.QRUOV.SLI.symmetrizer_eq`: the Gram matrix is exactly `diag(J₁, J₂)`.
* `Cslib.Crypto.QRUOV.SLI.leftMulMatrix_root_eq`: the generator's regular-representation matrix.
* `Cslib.Crypto.QRUOV.SLI.symmetrizer_mul_generator`: the explicitly evaluated symmetric product.

## References

* [QRUOV2026]
-/

public section

namespace Cslib.Crypto.QRUOV.SLI

open Matrix Module Polynomial

/-- The primality premise for the QR-UOV base field of order 127. -/
instance : Fact (Nat.Prime 127) := ⟨by decide⟩

/-- The base field used by the balanced security-level-I parameters in [QRUOV2026, Table 1,
printed p. 22]. -/
abbrev BaseField := ZMod 127

/-- The degree-3 modulus `x³ - x - 1` from [QRUOV2026, Table 3, printed p. 22]. -/
noncomputable def modulus : BaseField[X] := X ^ 3 - X - 1

/-- The QR-UOV cubic is monic. -/
theorem modulus_monic : modulus.Monic := by
  rw [show modulus = X ^ 3 - (X + 1) by unfold modulus; ring]
  apply monic_X_pow_sub
  compute_degree!

/-- The QR-UOV modulus has degree 3. -/
theorem modulus_natDegree : modulus.natDegree = 3 := by
  unfold modulus
  compute_degree!

/-- The QR-UOV cubic has no roots in `ZMod 127`, and hence is irreducible. -/
theorem modulus_irreducible : Irreducible modulus := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (p := modulus) ?_ ?_
  · simp [modulus_natDegree]
  · intro x hx
    rw [IsRoot.def] at hx
    simp only [modulus, eval_sub, eval_pow, eval_X, eval_one] at hx
    fin_cases x <;> revert hx <;> decide

/-- The field instance for the quotient by the QR-UOV modulus. -/
instance : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩

/-- The degree-3 coefficient extension used by the QR-UOV security-level-I parameters. -/
abbrev Extension := AdjoinRoot modulus

/-- The power basis `1, x, x²` of the QR-UOV coefficient extension. -/
noncomputable def basis : Basis (Fin 3) BaseField Extension :=
  (AdjoinRoot.powerBasis' modulus_monic).basis.reindex (finCongr modulus_natDegree)

/-- The coefficient-zero functional in the power basis. -/
noncomputable def coeffZero : Extension →ₗ[BaseField] BaseField :=
  basis.coord 0

/-- The multiplication Gram matrix obtained from the coefficient-zero functional. -/
noncomputable def symmetrizer : Matrix (Fin 3) (Fin 3) BaseField :=
  (Algebra.mulForm coeffZero).toMatrix basis

/-- The coefficient-zero functional is nonzero. -/
theorem coeffZero_ne_zero : coeffZero ≠ 0 := by
  intro h
  have h0 := LinearMap.congr_fun h (basis 0)
  simp [coeffZero] at h0

/-- The first power-basis vector is `1`. -/
theorem basis_zero : basis 0 = 1 := by
  simp only [basis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change AdjoinRoot.root modulus ^
      (((finCongr modulus_natDegree).symm 0 : Fin modulus.natDegree) : ℕ) = 1
  rw [finCongr_symm_apply_coe]
  simp

/-- The second power-basis vector is the quotient generator. -/
theorem basis_one : basis 1 = AdjoinRoot.root modulus := by
  simp only [basis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change AdjoinRoot.root modulus ^
      (((finCongr modulus_natDegree).symm 1 : Fin modulus.natDegree) : ℕ) =
    AdjoinRoot.root modulus
  rw [finCongr_symm_apply_coe]
  simp

/-- The third power-basis vector is the square of the quotient generator. -/
theorem basis_two : basis 2 = AdjoinRoot.root modulus ^ 2 := by
  simp only [basis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  change AdjoinRoot.root modulus ^
      (((finCongr modulus_natDegree).symm 2 : Fin modulus.natDegree) : ℕ) =
    AdjoinRoot.root modulus ^ 2
  rw [finCongr_symm_apply_coe]
  norm_num

/-- The defining quotient relation is `x³ = x + 1`. -/
theorem root_cubic :
    AdjoinRoot.root modulus ^ 3 = AdjoinRoot.root modulus + 1 := by
  have h : AdjoinRoot.mk modulus (X ^ 3 - X - 1) = 0 := by
    simpa [modulus] using AdjoinRoot.mk_self (f := modulus)
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  linear_combination h

/-- The fourth power reduces to `x² + x`. -/
private theorem root_quartic :
    AdjoinRoot.root modulus ^ 4 = AdjoinRoot.root modulus ^ 2 + AdjoinRoot.root modulus := by
  calc
    AdjoinRoot.root modulus ^ 4 =
        AdjoinRoot.root modulus * AdjoinRoot.root modulus ^ 3 := by ring
    _ = AdjoinRoot.root modulus * (AdjoinRoot.root modulus + 1) := by rw [root_cubic]
    _ = AdjoinRoot.root modulus ^ 2 + AdjoinRoot.root modulus := by ring

@[simp]
private theorem coeffZero_one : coeffZero 1 = 1 := by
  rw [← basis_zero]
  change basis.repr (basis 0) 0 = 1
  simp

@[simp]
private theorem coeffZero_root : coeffZero (AdjoinRoot.root modulus) = 0 := by
  rw [← basis_one]
  change basis.repr (basis 1) 0 = 0
  simp

@[simp]
private theorem coeffZero_root_sq : coeffZero (AdjoinRoot.root modulus ^ 2) = 0 := by
  rw [← basis_two]
  change basis.repr (basis 2) 0 = 0
  simp

@[simp]
private theorem coeffZero_root_cubic : coeffZero (AdjoinRoot.root modulus ^ 3) = 1 := by
  rw [root_cubic]
  simp

@[simp]
private theorem coeffZero_root_quartic : coeffZero (AdjoinRoot.root modulus ^ 4) = 0 := by
  rw [root_quartic]
  simp

@[simp]
private theorem root_mul_root :
    AdjoinRoot.root modulus * AdjoinRoot.root modulus = AdjoinRoot.root modulus ^ 2 := by
  ring

@[simp]
private theorem root_mul_root_sq :
    AdjoinRoot.root modulus * AdjoinRoot.root modulus ^ 2 = AdjoinRoot.root modulus ^ 3 := by
  ring

@[simp]
private theorem root_sq_mul_root :
    AdjoinRoot.root modulus ^ 2 * AdjoinRoot.root modulus = AdjoinRoot.root modulus ^ 3 := by
  ring

@[simp]
private theorem root_sq_mul_root_sq :
    AdjoinRoot.root modulus ^ 2 * AdjoinRoot.root modulus ^ 2 = AdjoinRoot.root modulus ^ 4 := by
  ring

/-- The multiplication Gram matrix is the source's `diag(J₁, J₂)` from Table 3, printed p. 22. -/
theorem symmetrizer_eq : symmetrizer = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetrizer, basis_zero, basis_one, basis_two]

/-- The source's symmetrizer is invertible. -/
theorem isUnit_symmetrizer : IsUnit symmetrizer :=
  Algebra.isUnit_mulForm_toMatrix basis coeffZero_ne_zero

/-- The source's symmetrizer makes every regular-representation matrix symmetric. -/
theorem symmetrizer_mul_leftMulMatrix_isSymm (g : Extension) :
    (symmetrizer * Algebra.leftMulMatrix basis g).IsSymm :=
  Algebra.mulForm_toMatrix_mul_leftMulMatrix_isSymm basis coeffZero g

/-- The specialized transpose-intertwining identity. -/
theorem transpose_leftMulMatrix_mul_symmetrizer (g : Extension) :
    (Algebra.leftMulMatrix basis g)ᵀ * symmetrizer =
      symmetrizer * Algebra.leftMulMatrix basis g :=
  Algebra.transpose_leftMulMatrix_mul_mulForm_toMatrix basis coeffZero g

@[simp]
private theorem basis_one_mul_basis_zero : basis 1 * basis 0 = basis 1 := by
  rw [basis_zero, mul_one]

@[simp]
private theorem basis_one_mul_basis_one : basis 1 * basis 1 = basis 2 := by
  rw [basis_one, basis_two]
  ring

@[simp]
private theorem basis_one_mul_basis_two : basis 1 * basis 2 = basis 0 + basis 1 := by
  rw [basis_one, basis_two, basis_zero, root_mul_root_sq, root_cubic]
  ring

/-- Multiplication by the quotient generator has the expected column-oriented regular
representation matrix: column `j` contains the coordinates of `x * basis j`. -/
theorem leftMulMatrix_root_eq :
    Algebra.leftMulMatrix basis (AdjoinRoot.root modulus) =
      !![0, 0, 1; 1, 0, 1; 0, 1, 0] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  rw [← basis_one]
  fin_cases i <;> fin_cases j <;>
    simp

/-- Explicitly multiplying the source's `W` by the generator representation produces this
symmetric matrix.  This calculation fixes the multiplication, column, and transpose conventions. -/
theorem symmetrizer_mul_generator :
    symmetrizer * Algebra.leftMulMatrix basis (AdjoinRoot.root modulus) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 1] := by
  rw [symmetrizer_eq, leftMulMatrix_root_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

end Cslib.Crypto.QRUOV.SLI
