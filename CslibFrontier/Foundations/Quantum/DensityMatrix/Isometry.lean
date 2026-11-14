/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.Linear
public import CslibFrontier.Foundations.Quantum.Bipartite
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Density-matrix evolution through isometries

Rectangular matrices describe an isometry into a larger register, including initialization of
ancillas. `densityConj V` is the linear operation `ρ ↦ V * ρ * Vᴴ`, built from Mathlib's matrix
multiplication maps. It is not a new notion of channel: preservation of density matrices requires
the explicit isometry equation. The matrix of a linear isometry satisfies that equation.

The same operation on one factor of a joint state preserves the other factor's reduced density
matrix. No product-state assumption is made, so correlations with an inaccessible reference
remain in the joint output. These are original bridges between existing representations.

## Main definitions

* `Cslib.Quantum.densityConj`: linear conjugation by a rectangular matrix.

## Main results

* `Cslib.Quantum.matrix_isometry`: the matrix of a linear isometry has orthonormal columns.
* `Cslib.Quantum.densityConj_pureState`: conjugation agrees with pure-state evolution.
* `Cslib.Quantum.partialTraceLeft_densityConj_kronecker`: a local isometry preserves the reference.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped Kronecker

variable {ι ι' κ : Type*} [Fintype ι]

/-- Conjugation `ρ ↦ V * ρ * Vᴴ` as a linear map, allowing different input and output dimensions.
Density matrices are preserved when `Vᴴ * V = 1`. -/
noncomputable def densityConj (V : Matrix ι' ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι' ι' ℂ :=
  (mulRightLinearMap ι' ℂ Vᴴ).comp (mulLeftLinearMap ι ℂ V)

/-- The operation uses the usual matrix conjugation. -/
theorem densityConj_apply (V : Matrix ι' ι ℂ) (ρ : Matrix ι ι ℂ) :
    densityConj V ρ = V * ρ * Vᴴ := by
  unfold densityConj
  rfl

/-- Matrix multiplication composes the corresponding state evolutions, including rectangular
maps between registers of different dimensions. -/
theorem densityConj_mul {ι'' : Type*} [Fintype ι'] (U : Matrix ι'' ι' ℂ)
    (V : Matrix ι' ι ℂ) (ρ : Matrix ι ι ℂ) :
    densityConj (U * V) ρ = densityConj U (densityConj V ρ) := by
  simp only [densityConj_apply, conjTranspose_mul, Matrix.mul_assoc]

/-- The identity matrix leaves an arbitrary state operator unchanged. -/
@[simp] theorem densityConj_one [DecidableEq ι] (ρ : Matrix ι ι ℂ) :
    densityConj (1 : Matrix ι ι ℂ) ρ = ρ := by
  simp [densityConj_apply]

/-- A rectangular isometry carries every density matrix to a density matrix. -/
theorem IsDensityMatrix.densityConj [Fintype ι'] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) {V : Matrix ι' ι ℂ} (hV : Vᴴ * V = 1) :
    IsDensityMatrix (densityConj V ρ) := by
  rw [densityConj_apply]
  exact hρ.conj_isometry hV

/-- A local isometry preserves a joint density matrix and retains the full reference. -/
theorem IsDensityMatrix.densityConj_kronecker [Fintype ι'] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : IsDensityMatrix ρ) {V : Matrix ι' ι ℂ} (hV : Vᴴ * V = 1) :
    IsDensityMatrix (Cslib.Quantum.densityConj (V ⊗ₖ (1 : Matrix κ κ ℂ)) ρ) := by
  apply hρ.densityConj
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    hV, one_mul, one_kronecker_one]

/-- The matrix of a linear isometry has orthonormal columns, even when it is rectangular. -/
theorem matrix_isometry [Fintype ι'] [DecidableEq ι]
    (V : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') :
    (Matrix.toEuclideanLin.symm V.toLinearMap)ᴴ *
      Matrix.toEuclideanLin.symm V.toLinearMap = 1 := by
  classical
  apply Matrix.toEuclideanLin.injective
  rw [show Matrix.toEuclideanLin = Matrix.toLpLin 2 2 from rfl,
    Matrix.toLpLin_mul_same]
  change (Matrix.toEuclideanLin _).comp (Matrix.toEuclideanLin _) = _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearEquiv.apply_symm_apply,
    LinearIsometry.adjoint_comp_self']
  exact (Matrix.toLpLin_one 2).symm

/-- Conjugating a rank-one state is exactly the corresponding linear evolution of its vector. -/
theorem densityConj_pureState [DecidableEq ι] (V : Matrix ι' ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    densityConj V (pureState ψ) = pureState (V.toEuclideanLin ψ) := by
  ext i j
  simp only [densityConj_apply, Matrix.mul_apply, pureState_apply, conjTranspose_apply,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, mulVec, dotProduct,
    star_sum, star_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- On a product pure state, local conjugation evolves the active vector and retains the
reference vector. Correlated inputs still use the unrestricted joint-matrix operation. -/
theorem densityConj_kronecker_pureState [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι' ι ℂ) (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) :
    densityConj (V ⊗ₖ (1 : Matrix κ κ ℂ)) (pureState (prodState ψ φ)) =
      pureState (prodState (V.toEuclideanLin ψ) φ) := by
  rw [densityConj_pureState]
  congr 1
  ext p
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, prodState_apply]
  rw [show (prodState ψ φ).ofLp = (fun q => ψ.ofLp q.1 * φ.ofLp q.2) from
    funext (prodState_apply ψ φ)]
  simpa only [Matrix.one_mulVec] using
    congrFun (kronecker_mulVec_mul V (1 : Matrix κ κ ℂ) ψ.ofLp φ.ofLp) p

/-- Applying a rectangular isometry to the first system leaves the reference marginal unchanged.
The input may be mixed or entangled, and need not even be normalized for this identity. -/
theorem partialTraceLeft_densityConj_kronecker [Fintype ι'] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {V : Matrix ι' ι ℂ} (hV : Vᴴ * V = 1) (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeft (densityConj (V ⊗ₖ (1 : Matrix κ κ ℂ)) ρ) = partialTraceLeft ρ := by
  rw [densityConj_apply]
  simpa only [Finset.sum_singleton] using
    partialTraceLeft_kraus {()} (fun _ => V) (by simpa only [Finset.sum_singleton] using hV) ρ

end Cslib.Quantum
