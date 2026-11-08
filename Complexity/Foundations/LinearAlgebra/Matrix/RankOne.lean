/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Constructive inverses and signed rank-one changes

Field-polymorphic determinant/adjugate inverse and Cramer solve, followed by a
signed Sherman–Morrison kernel. The arithmetic definitions execute over `ℚ`.
Correctness uses nonsingularity of the original and changed matrices; neither
symmetry nor a positivity condition on the signed change is required.
No cubic arithmetic-operation bound is claimed for determinant evaluation.

## Main definitions

* `inverse`: constructive adjugate inverse.
* `solve`: Cramer's rule without constructing a full inverse.
* `change`: signed rank-one change of a cached inverse.

## Main results

* `inverse_eq`, `solve_eq`: agreement with semantic matrix inversion.
* `change_den_ne_zero`, `change_eq`: well-definedness and correctness of signed updates.
-/

public section

namespace Matrix.RankOne

open Matrix

variable {K d : Type*} [Field K] [Fintype d] [DecidableEq d]

/-- A constructive adjugate inverse. This uses determinant arithmetic, not a
choice of an inverse from an existence proof. -/
@[expose] def inverse (G : Matrix d d K) : Matrix d d K :=
  G.det⁻¹ • G.adjugate

/-- Solve one normal equation by Cramer's rule, without constructing an inverse. -/
@[expose] def solve (G : Matrix d d K) (g : d → K) : d → K :=
  G.det⁻¹ • G.cramer g

/-- Signed rank-one change of a cached inverse. The row on the right is retained
explicitly, so the algebraic API does not require symmetry. -/
@[expose] def change (H : Matrix d d K) (x : d → K) (a : K) : Matrix d d K :=
  H - (a / (1 + a * (x ⬝ᵥ (H *ᵥ x)))) • vecMulVec (H *ᵥ x) (x ᵥ* H)

/-- The constructive inverse agrees with Mathlib's semantic inverse, including
its zero convention on singular matrices over a field. -/
theorem inverse_eq (G : Matrix d d K) : inverse G = G⁻¹ := by
  rw [inverse, Matrix.inv_def, Ring.inverse_eq_inv]

/-- Cramer's rule computes the actual inverse-matrix solution. -/
theorem solve_eq (G : Matrix d d K) (g : d → K) : solve G g = G⁻¹ *ᵥ g := by
  rw [solve, cramer_eq_adjugate_mulVec, ← smul_mulVec, ← inverse, inverse_eq]

/-- A rank-one change between two nonsingular matrices cannot have a zero
Sherman–Morrison denominator. This also covers negative downdates. -/
theorem change_den_ne_zero (G : Matrix d d K) (x : d → K) (a : K)
    (hG : IsUnit G) (hnew : IsUnit (G + a • vecMulVec x x)) :
    1 + a * (x ⬝ᵥ (G⁻¹ *ᵥ x)) ≠ 0 := by
  have hi : G *ᵥ (G⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det G).mp hG), one_mulVec]
  intro hz
  have hv : (G + a • vecMulVec x x) *ᵥ (G⁻¹ *ᵥ x) = 0 := by
    rw [add_mulVec, hi, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have := congrArg (fun t : K => t * x i) hz
    simp only [zero_mul] at this
    linear_combination this
  have hx : G⁻¹ *ᵥ x = 0 :=
    (mulVec_injective_iff_isUnit.mpr hnew) (hv.trans (mulVec_zero _).symm)
  simp [hx] at hz

/-- The signed update computes the inverse of the changed matrix. No updated
inverse or desired rounding result is supplied as a hypothesis. -/
theorem change_eq (G : Matrix d d K) (x : d → K) (a : K)
    (hG : IsUnit G) (hnew : IsUnit (G + a • vecMulVec x x)) :
    change G⁻¹ x a = (G + a • vecMulVec x x)⁻¹ := by
  have hd := change_den_ne_zero G x a hG hnew
  have hdet := (isUnit_iff_isUnit_det G).mp hG
  have hi : G *ᵥ (G⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  apply Eq.symm
  apply inv_eq_right_inv
  simp only [change, mul_sub, add_mul, mul_nonsing_inv _ hdet,
    smul_mul_assoc, vecMulVec_mul, mul_smul_comm, mul_vecMulVec,
    hi, vecMulVec_mulVec, op_smul_eq_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply, Pi.smul_apply]
  field_simp
  ring

end Matrix.RankOne
