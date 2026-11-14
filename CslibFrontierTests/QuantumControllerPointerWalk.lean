/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontierTests.QuantumControllerFixture
public import CslibFrontierTests.QuantumControllerState
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.ProgramSemantics

/-! The actual native pointer controller under a fixed coherent oracle and an adaptive classical
pointer service. The same finite function is passed outside the entire execution. The ghost
parity in the mathematical specification is retained quantum phase, not classical machine state.
-/

public section

namespace CslibFrontierTests.QuantumControllerPointerWalk

open Cslib Cslib.Quantum
open CslibFrontierTests.QuantumControllerFixture CslibFrontierTests.QuantumControllerState

/-- A deterministic one-bit pointer service. Canonical requests contain the current address.
The total service also specifies an empty request: its address defaults to false. -/
@[expose] noncomputable def pointerService (next : Bool → Bool) :
    Unit × List Bool → StateT Unit PMF (Fin 1 → Bool) :=
  fun request _ => PMF.pure ((fun _ => next (request.2.headD false)), ())

/-- The normalized phase-memory fixture as a complete device state. -/
@[expose] noncomputable def phaseDevice (parity : Bool) : DeviceState 3 Unit Unit :=
  pureDevice (phaseState parity) (norm_phaseState parity)

/-- The device after terminal interference, before or after its certain memory-bit measurement. -/
@[expose] noncomputable def readoutDevice (parity : Bool) : DeviceState 3 Unit Unit :=
  pureDevice (hResponse.eval (ket ![parity, false, true])) (by simp)

/-- The classical specification updates the address and the relative phase stored in memory.
The second coordinate is a mathematical description of the qubit, not another controller bit. -/
@[expose] def advance (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (state : Bool × Bool) : Bool × Bool :=
  let address := next state.1
  (address, state.2 ^^ H ![false, address] 0 ^^ H ![true, address] 0)

/-- The classical pointer service returns the next address and leaves the complete quantum
state untouched. -/
theorem run_service (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (address : Bool) (s : DeviceState 3 Unit Unit) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (DeviceProgram.requestBit (.inr ()) [address]) s = PMF.pure (next address, s) := by
  have hhandler := deviceWordHandler_encode (κ := Unit) H (pointerService next)
    (DeviceRequest.service (m := 3) () [address])
  simp only [DeviceRequest.encode] at hhandler
  have hstate : { s with serviceState := () } = s := by
    apply DeviceState.ext rfl
    exact Subsingleton.elim _ _
  rw [DeviceProgram.requestBit, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_query, hhandler, deviceHandler_service]
  simp [pointerService, List.ofFn_succ, hstate]

private theorem instruction_phase (H : (Fin 2 → Bool) → Fin 1 → Bool)
    (parity address : Bool) :
    (((phaseDevice parity).instruction H
      (.gate (false, false, if address then 1 else 2, []))).instruction H .query).instruction H
        (.gate (false, false, if address then 1 else 2, [])) =
      phaseDevice (parity ^^ H ![false, address] 0 ^^ H ![true, address] 0) := by
  unfold phaseDevice
  rw [pureDevice_instruction H _ _ (decode_flip H address),
    pureDevice_instruction H _ _ (decode_query H),
    pureDevice_instruction H _ _ (decode_flip H address)]
  simp only [phase_state]
  exact pureDevice_smul_of_norm_eq_one _ (by split_ifs <;> simp) _ _

/-- The actual canonical word calls coherently update the retained phase, with the full final
device state identified rather than only its measurement probabilities. -/
theorem run_phase (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (parity address : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (PointerWalk.phase address) (phaseDevice parity) =
      PMF.pure (address,
        phaseDevice (parity ^^ H ![false, address] 0 ^^ H ![true, address] 0)) := by
  simp only [PointerWalk.phase, ProbOracleComp.runWith_bind, DeviceProgram.runWith_gate,
    DeviceProgram.runWith_query, PMF.pure_bind, ProbOracleComp.runWith_pure, instruction_phase]

/-- One round of the existing native controller realizes the address/parity specification. -/
theorem run_round (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (address parity : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (PointerWalk.round address) (phaseDevice parity) =
      PMF.pure ((advance H next (address, parity)).1,
        phaseDevice (advance H next (address, parity)).2) := by
  simp only [PointerWalk.round, ProbOracleComp.runWith_bind, run_service, PMF.pure_bind,
    run_phase, advance]

/-- All adaptive rounds share the same fixed oracle and retain their quantum phase memory.
The statement identifies the complete joint law of the final classical address and device. -/
theorem run_iterate (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (count : ℕ) (address parity : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (OracleComp.iterate count PointerWalk.round address) (phaseDevice parity) =
      PMF.pure (((advance H next)^[count] (address, parity)).1,
        phaseDevice ((advance H next)^[count] (address, parity)).2) := by
  induction count with
  | zero => simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure,
      Function.iterate_zero, id_eq]
  | succ count ih =>
    rw [OracleComp.iterate_succ, ProbOracleComp.runWith_bind, ih, PMF.pure_bind,
      run_round, Function.iterate_succ_apply']

/-- The exported native loop begins at the false address and realizes the same specification. -/
theorem run_walk (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (count : ℕ) (parity : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (PointerWalk.walk count) (phaseDevice parity) =
      PMF.pure (((advance H next)^[count] (false, parity)).1,
        phaseDevice ((advance H next)^[count] (false, parity)).2) :=
  run_iterate H next count false parity

private theorem instruction_readout (H : (Fin 2 → Bool) → Fin 1 → Bool) (parity : Bool) :
    (phaseDevice parity).instruction H (.gate (false, true, 0, [])) = readoutDevice parity := by
  unfold phaseDevice readoutDevice
  rw [pureDevice_instruction H _ hMemory (by rfl)]
  simp only [readout_state]

/-- Actual word-level preparation initializes the normalized phase memory from three zero bits. -/
theorem run_prepare (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next)) PointerWalk.prepare
      (pureDevice (ket ![false, false, false]) (norm_ket _)) =
        PMF.pure ((), phaseDevice false) := by
  simp only [PointerWalk.prepare, ProbOracleComp.runWith_bind, DeviceProgram.runWith_gate,
    PMF.pure_bind]
  rw [pureDevice_instruction H _ xResponse (by rfl),
    pureDevice_instruction H _ hResponse (by rfl),
    pureDevice_instruction H _ hMemory (by rfl)]
  simp only [prepare_state, phaseDevice]

private theorem readoutDevice_measure (parity : Bool) :
    (readoutDevice parity).measure (fun x => x 0) =
      PMF.pure (parity, readoutDevice parity) := by
  apply pureDevice_measure_eq_pure
  intro x hx
  by_contra hp
  exact hx (hResponse_ket_apply_of_ne parity false true x hp)

/-- Terminal native readout returns the exposed parity and retains the remaining coherent state. -/
theorem run_readout (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (parity : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (DeviceProgram.requestBit (.inl .measure) (Turing.MultiTapeTM.encUnary 0))
      (readoutDevice parity) = PMF.pure (parity, readoutDevice parity) := by
  simpa only [Fin.val_zero] using
    (DeviceProgram.runWith_measure H (pointerService next) (0 : Fin 3)
      (readoutDevice parity)).trans (readoutDevice_measure parity)

/-- The complete natively certified controller outputs the accumulated parity and retains the
response register, for every round count and one fixed coherent oracle. -/
theorem run_program (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (count : ℕ) (input : List Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (PointerWalk.program count input) (pureDevice (ket ![false, false, false]) (norm_ket _)) =
      PMF.pure (((advance H next)^[count] (false, false)).2,
        readoutDevice ((advance H next)^[count] (false, false)).2) := by
  simp only [PointerWalk.program, ProbOracleComp.runWith_bind, run_prepare, PMF.pure_bind,
    run_walk, DeviceProgram.runWith_gate, instruction_readout, run_readout]

/-- One complete experiment samples a finite table once, before all adaptive rounds. -/
@[expose] noncomputable def sampledProgram (next : Bool → Bool) (count : ℕ)
    (input : List Bool) : PMF Bool := do
  let H ← Probability.PMF.uniformOfFintype ((Fin 2 → Bool) → Fin 1 → Bool)
  (ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
    (PointerWalk.program count input)
    (pureDevice (ket ![false, false, false]) (norm_ket _))).map Prod.fst

/-- The sampled execution is precisely the accumulated parity under that single table. -/
theorem sampledProgram_eq (next : Bool → Bool) (count : ℕ) (input : List Bool) :
    sampledProgram next count input =
      (Probability.PMF.uniformOfFintype ((Fin 2 → Bool) → Fin 1 → Bool)).map
        (fun H => ((advance H next)^[count] (false, false)).2) := by
  simp only [sampledProgram, run_program, PMF.pure_map]
  rfl

/-- The empty loop outputs false; preparation and terminal interference cancel on memory. -/
theorem run_program_zero (H : (Fin 2 → Bool) → Fin 1 → Bool) (next : Bool → Bool)
    (input : List Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (PointerWalk.program 0 input) (pureDevice (ket ![false, false, false]) (norm_ket _)) =
      PMF.pure (false, readoutDevice false) := by
  rw [run_program]
  rfl

/-- A fixed coherent table whose relative phase at address `b` is `b`. -/
@[expose] def andOracle (x : Fin 2 → Bool) (_ : Fin 1) : Bool := x 0 && x 1

/-- The toggling service visits true and then false, giving accumulated parity true. -/
theorem run_program_two (input : List Bool) :
    ProbOracleComp.runWith (deviceWordHandler andOracle (pointerService Bool.not))
      (PointerWalk.program 2 input) (pureDevice (ket ![false, false, false]) (norm_ket _)) =
      PMF.pure (true, readoutDevice true) := by
  rw [run_program]
  rfl

/-- The two adaptive rounds succeed with certainty under the one fixed table. -/
example (input : List Bool) :
    ((ProbOracleComp.runWith (deviceWordHandler andOracle (pointerService Bool.not))
      (PointerWalk.program 2 input) (pureDevice (ket ![false, false, false]) (norm_ket _))).map
      Prod.fst) true = 1 := by
  rw [run_program_two, PMF.pure_map]
  simp

end CslibFrontierTests.QuantumControllerPointerWalk
