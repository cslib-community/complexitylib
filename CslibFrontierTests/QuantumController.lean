/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Circuit
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Reference
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Resources

/-! Ordinary-module clients: canonical rejection, the zero-qubit boundary, complete circuit
execution, fixed-width classical service replies and reference readout on arbitrary joint states. -/

public section

open Cslib Cslib.Quantum

namespace CslibFrontierTests.QuantumController

/-- A nonempty payload is not the canonical coherent-query request. -/
theorem reject_query_payload (m : ℕ) (Operation : Type) :
    (DeviceRequest.codec m Operation).decodeQuery (.inl .query, [true]) = none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro q h
  have he := ((DeviceRequest.codec m Operation).decodeQuery_eq_some_iff _ q).mp h
  rw [DeviceRequest.codec_encodeQuery] at he
  cases q <;> simp [DeviceRequest.encode] at he

-- A malformed payload cannot make a query or change the service, active or reference state.
example {a b m r : ℕ} {κ State Operation : Type} [Fintype κ] [DecidableEq κ]
    (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (s : DeviceState m κ State) :
    deviceWordHandler H service (.inl .query, [true]) s = PMF.pure ([], s) :=
  deviceWordHandler_of_invalid H service _ (reject_query_payload m Operation) s

private noncomputable def vacuum : DeviceState 0 Unit Unit :=
  ⟨pureState (ket ((fun i => Fin.elim0 i), ())), isDensityMatrix_pureState (norm_ket _), ()⟩

/-- A concrete service with a zero-width reply and unchanged unit state. -/
noncomputable def emptyService : Unit × List Bool → StateT Unit PMF (Fin 0 → Bool) :=
  fun _ s => PMF.pure (Fin.elim0, s)

/-- A real entangled input: one active qubit and one inaccessible reference qubit. -/
noncomputable def entangledDevice : DeviceState 1 (Fin 1 → Bool) Unit :=
  ⟨pureState (maxEntangled (Fin 1 → Bool)), isDensityMatrix_pureState norm_maxEntangled, ()⟩

/-- Intermediate adaptive measurements may change conditional reference states, but the
unconditional reference readout on this entangled device is preserved. -/
theorem entangled_reference (H : (Fin 1 → Bool) → Fin 0 → Bool)
    (program : ProbOracleComp
      (fun _ : (DeviceOperation ⊕ Unit) × List Bool => List Bool) Bool) :
    (ProbOracleComp.runWith (deviceWordHandler H emptyService) program entangledDevice).bind
      (fun p => p.2.referenceMeasure POVM.basis) = entangledDevice.referenceMeasure POVM.basis :=
  runWith_deviceWordHandler_referenceMeasure H emptyService POVM.basis program entangledDevice

-- A query whose registers do not fit is skipped, even on an actually instantiated empty device.
example (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    ProbOracleComp.runWith (deviceWordHandler H emptyService)
      (OracleCircuit.controller 0 [.query]) vacuum = PMF.pure ((), vacuum) := by
  rw [OracleCircuit.runWith_controller]
  simp [OracleCircuit.toCircuit, OracleGateCode.toPlacedGate?, Circuit.matrix_nil]

-- The same concrete empty device can use the classical service without inventing a qubit.
example (H : (Fin 0 → Bool) → Fin 0 → Bool) :
    deviceWordHandler H emptyService (DeviceRequest.service (m := 0) () [true]).encode vacuum =
      PMF.pure ([], vacuum) := by
  rw [deviceWordHandler_encode, deviceHandler_service]
  simp [emptyService, vacuum]

-- The reference law includes arbitrary correlated inputs and adaptive private-coin programs.
example {a b m r : ℕ} {κ State Operation A : Type}
    [Fintype κ] [DecidableEq κ] [Fintype A]
    (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (M : POVM A κ)
    (program : ProbOracleComp
      (fun _ : (DeviceOperation ⊕ Operation) × List Bool => List Bool) Bool)
    (s : DeviceState m κ State) :
    (ProbOracleComp.runWith (deviceWordHandler H service) program s).bind
      (fun p => p.2.referenceMeasure M) = s.referenceMeasure M :=
  runWith_deviceWordHandler_referenceMeasure H service M program s

end CslibFrontierTests.QuantumController
