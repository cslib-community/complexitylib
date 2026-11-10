/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# Topology of the inner-product dual lattice

## Main results

* `ZLattice.discreteTopology_dualSubmodule`: the existing inner-product dual of a full-rank
  discrete lattice is discrete. This lets lattice convergence results apply to Fourier samples.
* `ZLattice.isZLattice_dualSubmodule`: the same dual spans the ambient real space.

## References

The proof uses Mathlib's `dualSubmodule_span_of_basis`: the dual is the integer span of the
real dual basis. No new notion of a dual lattice is introduced.
-/

public section

open Module
open scoped RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The inner-product dual of a full-rank discrete lattice is discrete. -/
theorem discreteTopology_dualSubmodule :
    DiscreteTopology (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) := by
  classical
  let b := Free.chooseBasis ℤ L
  have hB : (innerₗ E).Nondegenerate := by
    constructor <;> intro x hx <;> exact inner_self_eq_zero.mp (hx x)
  rw [← b.ofZLatticeBasis_span ℝ,
    LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ E) hB]
  infer_instance

/-- The inner-product dual of a full-rank discrete lattice spans the ambient real space. -/
theorem isZLattice_dualSubmodule
    [DiscreteTopology (LinearMap.BilinForm.dualSubmodule (innerₗ E) L)] :
    IsZLattice ℝ (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) := by
  classical
  let b := Free.chooseBasis ℤ L
  have hB : (innerₗ E).Nondegenerate := by
    constructor <;> intro x hx <;> exact inner_self_eq_zero.mp (hx x)
  constructor
  rw [← b.ofZLatticeBasis_span ℝ,
    LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ E) hB]
  exact ZSpan.span_top _

end ZLattice
