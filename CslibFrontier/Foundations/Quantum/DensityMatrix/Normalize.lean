/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix
import Mathlib.Analysis.Matrix.PosDef

/-!
# Normalizing positive density operators

A positive matrix with positive trace can be normalized to a density matrix. The same formula
sends the zero matrix to zero; it does not assign a state to an impossible measurement branch.
Multiplying the normalized matrix by its original trace recovers every positive matrix, including
the zero matrix. These are original bridges for supported probabilistic continuations.

## Main definitions

* `Cslib.Quantum.normalizeDensity`: divide a matrix by the real part of its trace.

## Main results

* `Cslib.Quantum.isDensityMatrix_normalizeDensity`: positive nonzero mass gives a density matrix.
* `Cslib.Quantum.trace_smul_normalizeDensity`: recover a positive matrix from its weight and
  normalized value, including the null case.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- Divide by the real trace. A zero-trace input maps to zero, not to a chosen default state. -/
noncomputable def normalizeDensity (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ρ.trace.re⁻¹ • ρ

/-- Normalization scales by the inverse real trace. -/
theorem normalizeDensity_apply (ρ : Matrix ι ι ℂ) :
    normalizeDensity ρ = ρ.trace.re⁻¹ • ρ := by rfl

/-- A positive matrix with positive mass normalizes to a density matrix. -/
theorem isDensityMatrix_normalizeDensity {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    (h : 0 < ρ.trace.re) : IsDensityMatrix (normalizeDensity ρ) := by
  refine ⟨hρ.smul (inv_nonneg.mpr h.le), ?_⟩
  rw [normalizeDensity, Matrix.trace_smul]
  have him := (Complex.nonneg_iff.mp hρ.trace_nonneg).2.symm
  apply Complex.ext <;> simp [him, ne_of_gt h]

/-- A positive matrix is its mass times its normalized value, even when its mass is zero. -/
theorem trace_smul_normalizeDensity {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    ρ.trace.re • normalizeDensity ρ = ρ := by
  by_cases h : ρ.trace.re = 0
  · have hzero : ρ = 0 := hρ.trace_eq_zero_iff.mp <|
      Complex.ext h (Complex.nonneg_iff.mp hρ.trace_nonneg).2.symm
    simp [hzero, normalizeDensity]
  · rw [normalizeDensity, smul_smul, mul_inv_cancel₀ h, one_smul]

end Cslib.Quantum
