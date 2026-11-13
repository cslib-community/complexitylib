/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Isometry
public import CslibFrontier.Foundations.Quantum.POVM.Density

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
* `Cslib.Quantum.UniformOracleCircuitFamily.outputDensity`: terminal prefix readout.
* `Cslib.Quantum.UniformOracleCircuitFamily.runDensityWithReference`: retain a joint reference.

## Main results

* `Cslib.Quantum.UniformOracleCircuitFamily.runDensity_pureState`: agreement with pure execution.
* `Cslib.Quantum.UniformOracleCircuitFamily.outputDensity_pureState`: agreement with pure readout.
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

/-- Terminal basis measurement of the declared output prefix for an arbitrary density matrix. -/
noncomputable def outputDensity
    (ρ : Matrix (Fin (F.description n x.length).quantumInputWidth → Bool)
      (Fin (F.description n x.length).quantumInputWidth → Bool) ℂ)
    (hρ : IsDensityMatrix ρ) : PMF (List Bool) :=
  (POVM.basis.measureDensity (F.runDensity n x H ρ)
    (F.isDensityMatrix_runDensity n x H hρ)).map
    (fun y => List.ofFn fun i => y (Fin.castLEEmb (F.wellFormed n x.length).output_le i))

/-- The mixed output uses basis measurement followed by the same prefix map as pure output. -/
theorem outputDensity_eq (ρ) (hρ : IsDensityMatrix ρ) :
    F.outputDensity n x H ρ hρ =
      (POVM.basis.measureDensity (F.runDensity n x H ρ)
        (F.isDensityMatrix_runDensity n x H hρ)).map
        (fun y => List.ofFn fun i => y (Fin.castLEEmb (F.wellFormed n x.length).output_le i)) := by
  unfold outputDensity
  rfl

/-- Mixed readout agrees with the existing readout on each normalized pure input. -/
@[simp] theorem outputDensity_pureState
    (ψ : Qubits (F.description n x.length).quantumInputWidth) (hψ : ‖ψ‖ = 1) :
    F.outputDensity n x H (pureState ψ) (isDensityMatrix_pureState hψ) =
      F.output n x H ψ hψ := by
  have hrun : ‖F.run n x H ψ‖ = 1 := by rw [LinearIsometry.norm_map, hψ]
  simp only [outputDensity_eq, output_eq, runDensity_pureState,
    POVM.measureDensity_pureState _ _ hrun, POVM.measure_basis]
  rfl

/-- Every supported mixed output has the declared output length. -/
theorem length_of_mem_support_outputDensity (ρ) (hρ : IsDensityMatrix ρ)
    {out : List Bool} (h : out ∈ (F.outputDensity n x H ρ hρ).support) :
    out.length = (F.description n x.length).outputWidth := by
  rw [outputDensity_eq, PMF.mem_support_map_iff] at h
  obtain ⟨y, _, rfl⟩ := h
  exact List.length_ofFn

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
