/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Handler

/-!
# Circuit execution through the native controller interface

An existing `OracleCircuit` can issue its instructions on the device's canonical word channels.
Its complete joint-state semantics is exactly conjugation by the existing circuit matrix,
tensored with the identity on the reference. The statement also covers malformed placements:
both interpreters skip them. It supplies the valid-code bridge without a second circuit model.

The translation is an ordinary oracle program. Its semantic agreement alone does not certify
the efficiency of constructing an arbitrary instruction list.

## Main definitions

* `Cslib.Quantum.OracleCircuit.controller`: issue existing circuit instructions as word requests.

## Main results

* `Cslib.Quantum.OracleCircuit.runWith_controller`: equality of complete joint-state execution.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped Kronecker

namespace DeviceState

variable {m : ℕ} {κ State : Type} [Fintype κ] [DecidableEq κ]

/-- The identity circuit leaves the entire device state unchanged. -/
@[simp] theorem evolve_one (s : DeviceState m κ State) : s.evolve 1 = s := by
  apply DeviceState.ext
  · simp only [evolve_density, UnitaryGroup.one_val, one_kronecker_one, densityConj_one]
  · exact evolve_serviceState _ _

/-- Sequential active-register unitaries agree with their matrix product, including the
reference. -/
theorem evolve_mul (U V : unitaryGroup (Fin m → Bool) ℂ) (s : DeviceState m κ State) :
    s.evolve (U * V) = (s.evolve V).evolve U := by
  apply DeviceState.ext
  · simp only [evolve_density, UnitaryGroup.mul_val]
    rw [← densityConj_mul, ← mul_kronecker_mul, one_mul]
  · simp only [evolve_serviceState]

/-- A single device instruction has the existing singleton-circuit interpretation. -/
theorem instruction_eq_evolve {a b : ℕ} (H : (Fin a → Bool) → Fin b → Bool)
    (code : OracleGateCode) (s : DeviceState m κ State) :
    s.instruction H code = s.evolve (OracleCircuit.toCircuit m H [code]).matrix := by
  rw [instruction_apply]
  unfold OracleCircuit.toCircuit
  cases h : code.toPlacedGate? m H <;>
    simp [h, Circuit.matrix_cons, Circuit.matrix_nil]

end DeviceState

namespace OracleGateCode

/-- The device request carrying an existing circuit instruction. -/
@[expose] def deviceRequest {m : ℕ} {Operation : Type} : OracleGateCode → DeviceRequest m Operation
  | .gate code => .gate code
  | .query => .query

end OracleGateCode

namespace OracleCircuit

/-- Execute an existing instruction list through the device's word channels. Replies to these
unitary commands are discarded. This is a program in the existing oracle-computation language. -/
@[expose] def controller {Operation : Type} (m : ℕ) : OracleCircuit →
    ProbOracleComp (fun _ : (DeviceOperation ⊕ Operation) × List Bool => List Bool) Unit
  | [] => pure ()
  | code :: codes => do
      let _ ← ProbOracleComp.query (code.deviceRequest (m := m)).encode
      controller m codes

/-- Executing instruction words is exactly the existing circuit evolution on the complete joint
state. Malformed placements are skipped by both sides. -/
theorem runWith_controller {a b m r : ℕ} {κ State Operation : Type}
    [Fintype κ] [DecidableEq κ] (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (codes : OracleCircuit) (s : DeviceState m κ State) :
    ProbOracleComp.runWith (deviceWordHandler H service) (controller m codes) s =
      PMF.pure ((), s.evolve (toCircuit m H codes).matrix) := by
  induction codes generalizing s with
  | nil => simp [controller, toCircuit, Circuit.matrix_nil]
  | cons code codes ih =>
    rw [controller, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      deviceWordHandler_encode]
    have hstep : deviceHandler H service code.deviceRequest s =
        PMF.pure ([], s.instruction H code) := by
      cases code
      · exact deviceHandler_gate _ _ _ _
      · exact deviceHandler_query _ _ _
    rw [hstep, PMF.pure_bind, ih, DeviceState.instruction_eq_evolve,
      ← DeviceState.evolve_mul]
    have heq : toCircuit m H (code :: codes) =
        toCircuit m H [code] ++ toCircuit m H codes := toCircuit_append H [code] codes
    rw [heq, Circuit.matrix_append]

end OracleCircuit

end Cslib.Quantum
