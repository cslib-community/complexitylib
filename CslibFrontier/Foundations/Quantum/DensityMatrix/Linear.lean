/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix

/-!
# Linear partial trace

Bundle the existing partial trace as a complex-linear map, using its existing addition and
scalar laws. This lets linear measurement continuations observe a reference register and lets
the generic linear-map API handle sums and real scalar towers.

## Main definitions

* `Cslib.Quantum.partialTraceLeftLinearMap`: the existing partial trace as a linear map.
-/

public section

namespace Cslib.Quantum

/-- The existing partial trace over the first factor, bundled with its established linearity. -/
noncomputable def partialTraceLeftLinearMap (ι κ : Type*) [Fintype ι] :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun := partialTraceLeft
  map_add' := partialTraceLeft_add
  map_smul' := partialTraceLeft_smul

/-- Bundling changes no partial-trace entries. -/
@[simp] theorem partialTraceLeftLinearMap_apply (ι κ : Type*) [Fintype ι]
    (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeftLinearMap ι κ ρ = partialTraceLeft ρ := by rfl

end Cslib.Quantum
