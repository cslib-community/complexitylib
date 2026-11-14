/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, traces of products of positive semidefinite matrices)

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.Order

/-!
# Traces of products of positive semidefinite matrices

The product of positive semidefinite matrices need not be positive semidefinite, but its trace
is nonnegative. Factor one matrix as `Cᴴ C` and rotate the trace to the positive sandwich `C A Cᴴ`.
For complex matrices, nonnegativity in `ComplexOrder` also asserts that the imaginary part is zero.

## Main results

* `Matrix.PosSemidef.trace_mul_nonneg`: the trace of a product of positive semidefinite matrices
  is nonnegative, over either the real or the complex numbers.
-/

public section

namespace Matrix.PosSemidef

open scoped MatrixOrder ComplexOrder

/-- The trace of the product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]
    {A B : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.star_eq_conjTranspose]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

end Matrix.PosSemidef
