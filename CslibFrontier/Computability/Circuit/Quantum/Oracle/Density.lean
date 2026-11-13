/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Isometry

/-!
# Native oracle circuits on mixed states and entangled references

The existing `UniformOracleCircuitFamily.run` isometry acts on density matrices by conjugation.
Its reference extension acts only on the supplied quantum-input subsystem and retains the full
joint output. The reference may be correlated with the input; no product-state assumption or
measurement is inserted. Its marginal remains unchanged.

Register initialization, fixed-oracle semantics and active resource counts are exactly those of
the existing family. The inaccessible reference is not an active circuit register. These are
finite-dimensional execution bridges, not efficient state-preparation certificates, interactive
measurement instruments, or security theorems.

## Main definitions

* `Cslib.Quantum.UniformOracleCircuitFamily.runDensity`: mixed-state execution.
* `Cslib.Quantum.UniformOracleCircuitFamily.runDensityWithReference`: retain a joint reference.

## Main results

* `Cslib.Quantum.UniformOracleCircuitFamily.runDensity_pureState`: agreement with pure execution.
* `Cslib.Quantum.UniformOracleCircuitFamily.isDensityMatrix_runDensityWithReference`:
  joint density matrices remain density matrices.
* `Cslib.Quantum.UniformOracleCircuitFamily.partialTraceLeft_runDensityWithReference`:
  the reference's reduced state is unchanged.
-/

public section

namespace Cslib.Quantum.UniformOracleCircuitFamily

open Matrix
open scoped Kronecker

variable (F : UniformOracleCircuitFamily) (n : ℕ) (x : List Bool)
    (H : (Fin (F.description n x.length).queryWidth → Bool) →
      Fin (F.description n x.length).responseWidth → Bool)

/-- Execute the existing run isometry on a density matrix. Linearity preserves mixtures and
does not require choosing a decomposition into pure states. -/
noncomputable def runDensity :
    Matrix (Fin (F.description n x.length).quantumInputWidth → Bool)
      (Fin (F.description n x.length).quantumInputWidth → Bool) ℂ →ₗ[ℂ]
    Matrix (Fin (F.description n x.length).width → Bool)
      (Fin (F.description n x.length).width → Bool) ℂ :=
  densityConj (Matrix.toEuclideanLin.symm (F.run n x H).toLinearMap)

/-- Mixed execution is conjugation by the matrix of the existing run isometry. -/
theorem runDensity_apply (ρ) : F.runDensity n x H ρ =
    densityConj (Matrix.toEuclideanLin.symm (F.run n x H).toLinearMap) ρ := by
  unfold runDensity
  rfl

/-- Mixed execution agrees with the existing pure-state execution. -/
theorem runDensity_pureState (ψ : Qubits (F.description n x.length).quantumInputWidth) :
    F.runDensity n x H (pureState ψ) = pureState (F.run n x H ψ) := by
  rw [runDensity_apply, densityConj_pureState, LinearEquiv.apply_symm_apply]
  rfl

/-- The initialized and executed state has positive semidefinite density and unit trace. -/
theorem isDensityMatrix_runDensity {ρ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (F.runDensity n x H ρ) := by
  rw [runDensity_apply]
  exact hρ.densityConj (matrix_isometry _)

variable (κ : Type*) [Fintype κ] [DecidableEq κ]

/-- Execute on the input subsystem and retain an inaccessible finite reference. The output
contains the entire joint density matrix, including its correlations. -/
noncomputable def runDensityWithReference :
    Matrix ((Fin (F.description n x.length).quantumInputWidth → Bool) × κ)
      ((Fin (F.description n x.length).quantumInputWidth → Bool) × κ) ℂ →ₗ[ℂ]
    Matrix ((Fin (F.description n x.length).width → Bool) × κ)
      ((Fin (F.description n x.length).width → Bool) × κ) ℂ :=
  densityConj (Matrix.toEuclideanLin.symm (F.run n x H).toLinearMap ⊗ₖ (1 : Matrix κ κ ℂ))

/-- The reference extension applies the run matrix tensored with the identity. -/
theorem runDensityWithReference_apply (ρ) : F.runDensityWithReference n x H κ ρ =
    densityConj (Matrix.toEuclideanLin.symm (F.run n x H).toLinearMap ⊗ₖ
      (1 : Matrix κ κ ℂ)) ρ := by
  unfold runDensityWithReference
  rfl

/-- Local execution preserves density matrices even with an entangled reference. -/
theorem isDensityMatrix_runDensityWithReference {ρ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (F.runDensityWithReference n x H κ ρ) := by
  rw [runDensityWithReference_apply]
  apply hρ.densityConj
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    matrix_isometry, one_mul, one_kronecker_one]

/-- Local execution leaves the reference marginal unchanged, including for correlated inputs. -/
theorem partialTraceLeft_runDensityWithReference (ρ) :
    partialTraceLeft (F.runDensityWithReference n x H κ ρ) = partialTraceLeft ρ := by
  rw [runDensityWithReference_apply]
  exact partialTraceLeft_densityConj_kronecker (matrix_isometry _) ρ

end Cslib.Quantum.UniformOracleCircuitFamily
