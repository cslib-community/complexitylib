/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Measurement.Restrict
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Isometry
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Normalize
public import CslibFrontier.Foundations.Quantum.POVM.Density

/-!
# Classical readout with retained quantum memory

A function `f : ι → A` declares which classical value is read from a computational basis index.
Outcome `y` applies the existing projection onto the fiber `f ⁻¹' {y}`. Conjugation by its matrix
retains the entire active register, including coherence within each fiber. Its trace is the
outcome probability, agreeing with the existing basis-density PMF mapped by `f`.

This is the projective update rule of [de Wolf][deWolf2019], §15.1, p. 128, restricted to diagonal
projectors. The PMF and reference-register bridges are original formalization infrastructure.
Conditional reference states can change; only the sum of all branches preserves the reference.

## Main definitions

* `Cslib.Quantum.outcomeProjection`: the matrix of `projOutcomes (f · = y)`.
* `Cslib.Quantum.classicalDensityBranch`: the subnormalized state for one classical outcome.

## Main results

* `Cslib.Quantum.classicalDensityBranch_posSemidef`: each branch is positive.
* `Cslib.Quantum.sum_trace_classicalDensityBranch`: total trace is preserved.
* `Cslib.Quantum.classicalDensityBranch_pureState`: agreement with vector projection.
* `Cslib.Quantum.map_measureDensity_basis_apply`: the mapped basis PMF gives each branch mass.
* `Cslib.Quantum.isDensityMatrix_normalize_classicalDensityBranch`: supported branches normalize.
* `Cslib.Quantum.bindOnSupport_classicalDensityBranch_apply`: supported continuation is the
  readout of the linearly evolved subnormalized branches.
* `Cslib.Quantum.partialTraceLeft_sum_classicalDensityBranch`: the summed reference is preserved.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker ComplexOrder

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]

/-- The matrix of projection onto the computational basis indices reporting `y`. -/
noncomputable def outcomeProjection (f : ι → A) (y : A) : Matrix ι ι ℂ :=
  Matrix.toEuclideanLin.symm (projOutcomes (fun i => f i = y))

/-- The projector is diagonal, with ones exactly on the reported fiber. -/
theorem outcomeProjection_eq_diagonal (f : ι → A) (y : A) :
    outcomeProjection f y = diagonal (fun i => if f i = y then 1 else 0) := by
  apply Matrix.toEuclideanLin.injective
  ext ψ i
  simp [outcomeProjection, Matrix.toEuclideanLin, Matrix.toLpLin_apply, mulVec_diagonal,
    projOutcomes_apply]

/-- As a linear map, the matrix acts by the existing amplitude projection. -/
@[simp] theorem outcomeProjection_toEuclideanLin (f : ι → A) (y : A) :
    (outcomeProjection f y).toEuclideanLin = projOutcomes (fun i => f i = y) :=
  LinearEquiv.apply_symm_apply _ _

/-- Every outcome projector is self-adjoint. -/
@[simp] theorem outcomeProjection_conjTranspose (f : ι → A) (y : A) :
    (outcomeProjection f y)ᴴ = outcomeProjection f y := by
  simp [outcomeProjection_eq_diagonal, diagonal_conjTranspose]

/-- Projecting onto one classical fiber twice is the same as projecting once. -/
@[simp] theorem outcomeProjection_mul_self (f : ι → A) (y : A) :
    outcomeProjection f y * outcomeProjection f y = outcomeProjection f y := by
  simp only [outcomeProjection_eq_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- The outcome projectors form a complete family. -/
theorem sum_outcomeProjection [Fintype A] (f : ι → A) : ∑ y, outcomeProjection f y = 1 := by
  ext i j
  simp [Matrix.sum_apply, outcomeProjection_eq_diagonal, diagonal_apply, Matrix.one_apply]

/-- The subnormalized branch retains the full register and the coherence inside the fiber. -/
noncomputable def classicalDensityBranch (f : ι → A) (y : A) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  densityConj (outcomeProjection f y)

/-- A branch masks both matrix indices by the declared readout, not by the whole basis index. -/
theorem classicalDensityBranch_apply (f : ι → A) (y : A) (ρ : Matrix ι ι ℂ) (i j : ι) :
    classicalDensityBranch f y ρ i j = if f i = y ∧ f j = y then ρ i j else 0 := by
  change densityConj (outcomeProjection f y) ρ i j = _
  rw [densityConj_apply, outcomeProjection_conjTranspose, outcomeProjection_eq_diagonal]
  by_cases hi : f i = y <;> by_cases hj : f j = y <;>
    simp [diagonal_mul, mul_diagonal, hi, hj]

/-- Conjugation by an outcome projector preserves positivity. -/
theorem classicalDensityBranch_posSemidef (f : ι → A) (y : A) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) : (classicalDensityBranch f y ρ).PosSemidef := by
  change (densityConj (outcomeProjection f y) ρ).PosSemidef
  rw [densityConj_apply]
  exact hρ.mul_mul_conjTranspose_same _

/-- Branch mass is the sum of the diagonal entries in its fiber. -/
theorem trace_classicalDensityBranch (f : ι → A) (y : A) (ρ : Matrix ι ι ℂ) :
    (classicalDensityBranch f y ρ).trace = ∑ i, if f i = y then ρ i i else 0 := by
  simp [Matrix.trace, classicalDensityBranch_apply]

/-- All branch masses sum to the original trace, without a normalization assumption. -/
theorem sum_trace_classicalDensityBranch [Fintype A] (f : ι → A) (ρ : Matrix ι ι ℂ) :
    ∑ y, (classicalDensityBranch f y ρ).trace = ρ.trace := by
  simp only [trace_classicalDensityBranch]
  rw [sum_comm]
  simp [Matrix.trace]

/-- Branch traces give the existing basis measurement followed by classical postprocessing. -/
theorem map_measureDensity_basis_apply (f : ι → A) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) (y : A) :
    ((POVM.basis.measureDensity ρ hρ).map f) y =
      ENNReal.ofReal (classicalDensityBranch f y ρ).trace.re := by
  rw [PMF.map_apply, tsum_fintype, trace_classicalDensityBranch, Complex.re_sum]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply sum_congr rfl
    intro i _
    by_cases h : f i = y
    · simp [h, POVM.measureDensity_apply, POVM.densityProb_basis]
    · simp [h, Ne.symm h]
  · intro i _
    split_ifs
    · exact (Complex.nonneg_iff.mp hρ.posSemidef.diag_nonneg).1
    · simp

/-- A supported outcome has strictly positive branch trace, so its state can be normalized. -/
theorem trace_classicalDensityBranch_pos_of_mem_support (f : ι → A) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) (y : A)
    (hy : y ∈ ((POVM.basis.measureDensity ρ hρ).map f).support) :
    0 < (classicalDensityBranch f y ρ).trace.re := by
  rw [PMF.mem_support_iff, map_measureDensity_basis_apply] at hy
  exact lt_of_not_ge (fun h => hy (ENNReal.ofReal_eq_zero.mpr h))

/-- Supported classical branches normalize to density matrices. -/
theorem isDensityMatrix_normalize_classicalDensityBranch (f : ι → A) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) (y : A)
    (hy : y ∈ ((POVM.basis.measureDensity ρ hρ).map f).support) :
    IsDensityMatrix (normalizeDensity (classicalDensityBranch f y ρ)) :=
  isDensityMatrix_normalizeDensity (classicalDensityBranch_posSemidef f y hρ.posSemidef)
    (trace_classicalDensityBranch_pos_of_mem_support f ρ hρ y hy)

/-- Weighting a normalized branch by its outcome probability recovers the subnormalized branch.
This identity also covers impossible outcomes without supplying a default density matrix. -/
theorem measureDensity_smul_normalize_classicalDensityBranch (f : ι → A) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) (y : A) :
    (((POVM.basis.measureDensity ρ hρ).map f) y).toReal •
      normalizeDensity (classicalDensityBranch f y ρ) = classicalDensityBranch f y ρ := by
  rw [map_measureDensity_basis_apply, ENNReal.toReal_ofReal
    (Complex.nonneg_iff.mp (classicalDensityBranch_posSemidef f y hρ.posSemidef).trace_nonneg).1]
  exact trace_smul_normalizeDensity (classicalDensityBranch_posSemidef f y hρ.posSemidef)

/-- An impossible classical outcome has the zero matrix as its subnormalized branch. -/
theorem classicalDensityBranch_eq_zero_of_not_mem_support (f : ι → A) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) (y : A)
    (hy : y ∉ ((POVM.basis.measureDensity ρ hρ).map f).support) :
    classicalDensityBranch f y ρ = 0 := by
  have h := measureDensity_smul_normalize_classicalDensityBranch f ρ hρ y
  rw [PMF.mem_support_iff, not_not] at hy
  simpa only [hy, ENNReal.toReal_zero, zero_smul] using h.symm

/-- Supported normalized continuation agrees with the sum of subnormalized branches after
linear state evolution and POVM readout. No continuation is evaluated at a null branch. -/
theorem bindOnSupport_classicalDensityBranch_apply [Fintype A] [Fintype κ] [DecidableEq κ]
    {B : Type*} [Fintype B] (f : ι → A) (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ)
    (L : A → Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hL : ∀ y σ, IsDensityMatrix σ → IsDensityMatrix (L y σ)) (M : A → POVM B κ) (b : B) :
    (((POVM.basis.measureDensity ρ hρ).map f).bindOnSupport fun y hy =>
      (M y).measureDensity (L y (normalizeDensity (classicalDensityBranch f y ρ)))
        (hL y _ (isDensityMatrix_normalize_classicalDensityBranch f ρ hρ y hy))) b =
      ∑ y, ENNReal.ofReal ((M y).densityProb (L y (classicalDensityBranch f y ρ)) b) := by
  rw [PMF.bindOnSupport_apply, tsum_fintype]
  apply sum_congr rfl
  intro y _
  by_cases hy : ((POVM.basis.measureDensity ρ hρ).map f) y = 0
  · have hz := classicalDensityBranch_eq_zero_of_not_mem_support f ρ hρ y
      (by simpa only [PMF.mem_support_iff, not_not] using hy)
    simp [hy, hz, POVM.densityProb]
  · rw [dite_eq_right hy, POVM.measureDensity_apply]
    have hw : (((POVM.basis.measureDensity ρ hρ).map f) y).toReal •
        L y (normalizeDensity (classicalDensityBranch f y ρ)) =
          L y (classicalDensityBranch f y ρ) := by
      rw [← LinearMap.map_smul_of_tower,
        measureDensity_smul_normalize_classicalDensityBranch f ρ hρ y]
    rw [← hw, POVM.densityProb_smul, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- On pure states, each density branch is exactly the projected vector's rank-one matrix. -/
theorem classicalDensityBranch_pureState (f : ι → A) (y : A) (ψ : EuclideanSpace ℂ ι) :
    classicalDensityBranch f y (pureState ψ) =
      pureState (projOutcomes (fun i => f i = y) ψ) := by
  rw [classicalDensityBranch, densityConj_pureState, outcomeProjection_toEuclideanLin]

/-- Reading only the active factor acts as the identity on the reference factor. -/
theorem outcomeProjection_comp_fst [Fintype κ] [DecidableEq κ] (f : ι → A) (y : A) :
    outcomeProjection (f ∘ Prod.fst : ι × κ → A) y =
      outcomeProjection f y ⊗ₖ (1 : Matrix κ κ ℂ) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [outcomeProjection_eq_diagonal, diagonal_apply, kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq, Function.comp_apply]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl]

/-- Discarding the classical outcome preserves the reference marginal, even for entangled inputs.
Individual conditional reference states need not agree with the original marginal. -/
theorem partialTraceLeft_sum_classicalDensityBranch [Fintype A] [Fintype κ] [DecidableEq κ]
    (f : ι → A) (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeft (∑ y, classicalDensityBranch (f ∘ Prod.fst) y ρ) =
      partialTraceLeft ρ := by
  simp only [classicalDensityBranch, outcomeProjection_comp_fst, densityConj_apply]
  apply partialTraceLeft_kraus
  simpa only [outcomeProjection_conjTranspose, outcomeProjection_mul_self] using
    sum_outcomeProjection f

end Cslib.Quantum
