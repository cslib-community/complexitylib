/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Algebra.Module.ZLattice.CoefficientFiber
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Dual lattice pairing modulo an integer

## Main results

* `ZLattice.toAddCircle_coefficientMod_pairing`: the coefficient dot product is the actual
  bilinear pairing divided by the modulus, reduced modulo one.

## References

[Regev2009], Lemma 3.11, equation (12), printed page 24. This algebraic identity applies to
composite moduli and does not assert uniformity or an efficient sampling procedure.
-/

public section

noncomputable section

namespace ZLattice

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- Reducing the integer dual pairing gives the coefficient phase used by the actual sample. -/
theorem toAddCircle_coefficientMod_pairing (B : LinearMap.BilinForm ℝ E)
    (L : Submodule ℤ E) (b : Module.Basis ι ℤ L) (p : ℕ) [NeZero p]
    (w : B.dualSubmodule L) (v : L) :
    ZMod.toAddCircle (∑ i, coefficientMod L b p v i *
      ((B.dualSubmodulePairing w (b i) : ℤ) : ZMod p)) =
        ((B w v / p : ℝ) : UnitAddCircle) := by
  classical
  have hp : B.dualSubmodulePairing w v =
      ∑ i, b.equivFun v i * B.dualSubmodulePairing w (b i) := by
    have h := congrArg (B.dualSubmoduleToDual L w) (b.sum_equivFun v)
    simpa only [map_sum, map_smul, smul_eq_mul,
      LinearMap.BilinForm.dualSubmoduleToDual, LinearMap.coe_mk, AddHom.coe_mk] using h.symm
  have hc : (∑ i, coefficientMod L b p v i *
      ((B.dualSubmodulePairing w (b i) : ℤ) : ZMod p)) =
        ((B.dualSubmodulePairing w v : ℤ) : ZMod p) := by
    rw [hp]
    simp [coefficientMod]
  rw [hc, ZMod.toAddCircle_intCast]
  congr 2
  exact B.dualSubmodulePairing_spec w v

end ZLattice
