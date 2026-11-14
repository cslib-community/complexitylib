/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Program
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Handler

/-!
# Native device commands under the quantum handler

Canonical word commands execute their typed operations on the existing joint density matrix.
These original interface equations connect the native certificates in `Controller.Program`
to the stateful quantum semantics in `Controller.Handler`.

## Main results

* `Cslib.Quantum.DeviceProgram.runWith_command`: a canonical command executes its typed request.
* `Cslib.Quantum.DeviceProgram.runWith_gate`: an elementary gate executes its existing decoder.
* `Cslib.Quantum.DeviceProgram.runWith_query`: a coherent query uses the fixed supplied oracle.
* `Cslib.Quantum.DeviceProgram.runWith_measure`: a wire request retains its conditional state.
-/

public section

namespace Cslib.Quantum.DeviceProgram

variable {a b m r : ℕ} {κ State Operation : Type} [Fintype κ] [DecidableEq κ]

/-- A canonical command executes its typed operation and discards the classical reply. -/
theorem runWith_command (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (q : DeviceRequest m Operation) (s : DeviceState m κ State) :
    ProbOracleComp.runWith (deviceWordHandler H service)
      (command q.encode.1 q.encode.2) s =
        (deviceHandler H service q s).map (fun p => ((), p.2)) := by
  simp only [command, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    Prod.mk.eta, deviceWordHandler_encode, PMF.map_comp]
  rfl

/-- An elementary gate executes its existing decoder, including the invalid-placement no-op. -/
theorem runWith_gate (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (code : PhaseGateCode) (s : DeviceState m κ State) :
    ProbOracleComp.runWith (deviceWordHandler H service) (gate code) s =
      PMF.pure ((), s.instruction H (.gate code)) := by
  simpa only [gate, DeviceRequest.encode, deviceHandler_gate, PMF.pure_map] using
    runWith_command H service (.gate code) s

/-- A coherent-query command uses the one supplied oracle throughout the run. -/
theorem runWith_query (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (s : DeviceState m κ State) :
    ProbOracleComp.runWith (deviceWordHandler H service) (command (.inl .query) []) s =
      PMF.pure ((), s.instruction H .query) := by
  simpa only [DeviceRequest.encode, deviceHandler_query, PMF.pure_map] using
    runWith_command H service .query s

/-- Reading a valid wire returns its bit and retains the supported conditional joint state. -/
theorem runWith_measure (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (wire : Fin m) (s : DeviceState m κ State) :
    ProbOracleComp.runWith (deviceWordHandler H service)
      (requestBit (.inl .measure) (Turing.MultiTapeTM.encUnary wire.val)) s =
      s.measure (fun x => x wire) := by
  have h := deviceWordHandler_encode (κ := κ) H service
    (DeviceRequest.measure (Operation := Operation) wire)
  simp only [DeviceRequest.encode] at h
  rw [requestBit, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_query, h, deviceHandler_measure]
  simp only [PMF.map_comp]
  convert PMF.map_id (s.measure (fun x => x wire)) using 1
  rfl

end Cslib.Quantum.DeviceProgram
