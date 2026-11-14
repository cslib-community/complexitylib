/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Circuit
public import CslibFrontier.Foundations.Quantum.DensityMatrix.Pure

/-! Shared pure-state fixtures for native controllers and their one-boundary clients. The
device keeps the existing density matrix on the active register and a one-dimensional reference.
No quantum data is encoded into the classical service state. -/

public section

namespace CslibFrontierTests.QuantumControllerFixture

open Cslib Cslib.Quantum Matrix
open scoped Kronecker

variable {m : ℕ}

/-- A normalized pure active state, a trivial reference and a trivial classical service state. -/
noncomputable def pureDevice (ψ : Qubits m) (hψ : ‖ψ‖ = 1) : DeviceState m Unit Unit where
  density := pureState (prodState ψ (ket ()))
  isDensityMatrix := isDensityMatrix_pureState (by rw [norm_prodState, hψ, norm_ket, one_mul])
  serviceState := ()

/-- The fixture is the existing product-state projector. -/
theorem pureDevice_density (ψ : Qubits m) (hψ : ‖ψ‖ = 1) :
    (pureDevice ψ hψ).density = pureState (prodState ψ (ket ())) := by rfl

@[simp] theorem pureDevice_serviceState (ψ : Qubits m) (hψ : ‖ψ‖ = 1) :
    (pureDevice ψ hψ).serviceState = () := by rfl

/-- A global phase does not change the device state. -/
theorem pureDevice_smul_of_norm_eq_one (c : ℂ) (hc : ‖c‖ = 1)
    (ψ : Qubits m) (hψ : ‖ψ‖ = 1) :
    pureDevice (c • ψ) (by rw [norm_smul, hc, hψ, one_mul]) = pureDevice ψ hψ := by
  apply DeviceState.ext
  · rw [pureDevice_density, pureDevice_density, prodState_smul_left,
      pureState_smul_of_norm_eq_one c hc]
  · rfl

/-- Unitary device evolution agrees with the existing pure-vector evolution, including the
trivial reference register. -/
theorem pureDevice_evolve (ψ : Qubits m) (hψ : ‖ψ‖ = 1)
    (U : unitaryGroup (Fin m → Bool) ℂ) :
    (pureDevice ψ hψ).evolve U =
      pureDevice (unitaryEquiv U ψ) (by simpa using hψ) := by
  apply DeviceState.ext
  · rw [DeviceState.evolve_density, pureDevice_density, densityConj_kronecker_pureState,
      pureDevice_density]
    congr 2
  · rfl

/-- The placed-gate specialization used by the controller's elementary instruction clients. -/
theorem pureDevice_evolve_gate (ψ : Qubits m) (hψ : ‖ψ‖ = 1) (g : PlacedGate m) :
    (pureDevice ψ hψ).evolve g.matrix = pureDevice (g.eval ψ) (by simpa using hψ) :=
  pureDevice_evolve ψ hψ g.matrix

/-- A decoded existing instruction executes its placed gate on the pure fixture. -/
theorem pureDevice_instruction {a b : ℕ} (H : (Fin a → Bool) → Fin b → Bool)
    (code : OracleGateCode) (g : PlacedGate m) (hcode : code.toPlacedGate? m H = some g)
    (ψ : Qubits m) (hψ : ‖ψ‖ = 1) :
    (pureDevice ψ hψ).instruction H code = pureDevice (g.eval ψ) (by simpa using hψ) := by
  rw [DeviceState.instruction_apply, hcode]
  exact pureDevice_evolve_gate ψ hψ g

/-- A readout constant on the support of a pure state reports that value and retains the whole
state, including coherence between different basis vectors in the same readout fiber. -/
theorem pureDevice_measure_eq_pure {Outcome : Type} [DecidableEq Outcome]
    (ψ : Qubits m) (hψ : ‖ψ‖ = 1) (read : (Fin m → Bool) → Outcome) (value : Outcome)
    (hsupport : ∀ x, ψ.ofLp x ≠ 0 → read x = value) :
    (pureDevice ψ hψ).measure read = PMF.pure (value, pureDevice ψ hψ) := by
  apply DeviceState.measure_eq_pure_of_branch
  ext p q
  rw [classicalDensityBranch_apply]
  by_cases hp : read p.1 = value
  · by_cases hq : read q.1 = value
    · simp [hp, hq]
    · have hzero : ψ.ofLp q.1 = 0 := by
        by_contra hz
        exact hq (hsupport _ hz)
      simp [hp, hq, pureDevice_density, pureState_apply, prodState_apply,
        hzero]
  · have hzero : ψ.ofLp p.1 = 0 := by
      by_contra hz
      exact hp (hsupport _ hz)
    simp [hp, pureDevice_density, pureState_apply, prodState_apply, hzero]

end CslibFrontierTests.QuantumControllerFixture
