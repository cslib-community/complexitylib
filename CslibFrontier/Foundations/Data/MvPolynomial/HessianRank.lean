/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, residual Hessian rank)

public import CslibFrontier.Foundations.Data.MvPolynomial.Hessian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ENat.Lattice

/-!
# Minimum residual Hessian rank

Subtracting arbitrary linear combinations of supplied Hessians gives a family of residual
matrices. Their minimum rank is recorded in `ℕ∞`, for comparison with extended circuit costs.
Unlike circuit complexity, this minimum is always finite: zero coefficients are available.
The coefficients are chosen at the given point, not uniformly over all points.

## Main definitions

* `MvPolynomial.hessianResidualRank`: minimum rank after subtracting supplied Hessians.

## Main results

* `MvPolynomial.hessianResidualRank_le`: any choice of coefficients bounds the minimum.
* `MvPolynomial.hessianResidualRank_ne_top`: the minimum is finite.

## References

* Ported from LowerBound/Fusion/Arithmetic/Interaction/Hessian/Relative.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace MvPolynomial

variable {ι κ K : Type*} [Field K] [Fintype ι] [Fintype κ]

/-- The minimum residual Hessian rank at a fixed point after subtracting a linear combination
of the supplied Hessians. The result lies in `ℕ∞` to compare with extended computational costs. -/
noncomputable def hessianResidualRank (point : ι → K) (target : MvPolynomial ι K)
    (sources : κ → MvPolynomial ι K) : ℕ∞ :=
  ⨅ coefficients : κ → K,
    ((hessian point target - ∑ i, coefficients i • hessian point (sources i)).rank : ℕ∞)

/-- The minimum residual Hessian rank is at most the rank of the residual for any choice of
coefficients. -/
theorem hessianResidualRank_le (point : ι → K) (target : MvPolynomial ι K)
    (sources : κ → MvPolynomial ι K) (coefficients : κ → K) :
    hessianResidualRank point target sources ≤
      (hessian point target - ∑ i, coefficients i • hessian point (sources i)).rank :=
  iInf_le _ coefficients

/-- The minimum residual Hessian rank is finite. -/
@[simp] theorem hessianResidualRank_ne_top (point : ι → K) (target : MvPolynomial ι K)
    (sources : κ → MvPolynomial ι K) : hessianResidualRank point target sources ≠ ⊤ :=
  ENat.iInf_natCast_ne_top.mpr ⟨0⟩

end MvPolynomial
