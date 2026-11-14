/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontierTests.QuantumControllerPointerWalk

/-! Measuring the complete one-qubit phase-memory subsystem destroys the two-round pointer
controller's certainty. The query address and response registers are not measured. The extra
readout is an actual native device request, using the handler's supported normalization. -/

public section

namespace CslibFrontierTests.QuantumControllerCoherence

open Cslib Cslib.Quantum Cslib.Probability Matrix
open CslibFrontierTests.QuantumControllerFixture CslibFrontierTests.QuantumControllerState
open CslibFrontierTests.QuantumControllerPointerWalk

private theorem project_phaseState (parity outcome : Bool) :
    projOutcomes (fun x : Fin 3 → Bool => x 0 = outcome) (phaseState parity) =
      ((if parity && outcome then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) •
        hResponse.eval (ket ![outcome, false, true]) := by
  ext x
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] := by
    refine ⟨x 0, x 1, x 2, ?_⟩
    ext i
    fin_cases i <;> rfl
  cases parity <;> cases outcome <;> cases a <;> cases b <;> cases c <;>
    norm_num [projOutcomes_apply, phaseState, hResponse_ket, hMemory_ket,
      map_add, map_smul, ket_apply, funext_iff, Fin.forall_fin_succ]

private theorem branch_phaseDevice (parity outcome : Bool) :
    classicalDensityBranch (fun x : (Fin 3 → Bool) × Unit => x.1 0) outcome
      (phaseDevice parity).density = (1 / 2 : ℝ) • (readoutDevice outcome).density := by
  have hproj :
      projOutcomes (fun x : (Fin 3 → Bool) × Unit => x.1 0 = outcome)
        (prodState (phaseState parity) (ket ())) =
      prodState (projOutcomes (fun x : Fin 3 → Bool => x 0 = outcome) (phaseState parity))
        (ket ()) := by
    ext x
    simp only [projOutcomes_apply, prodState_apply]
    split_ifs <;> simp
  simp only [phaseDevice, readoutDevice, pureDevice_density]
  rw [classicalDensityBranch_pureState, hproj, project_phaseState, prodState_smul_left,
    pureState_smul]
  have hc :
      ((if parity && outcome then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) *
          star ((if parity && outcome then -1 else 1) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) =
        (1 / 2 : ℂ) := by
    cases parity <;> cases outcome <;>
      norm_num [Complex.star_def, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt]
  rw [hc]
  ext i j
  simp [Complex.real_smul]

private theorem normalized_branch_phaseDevice (parity outcome : Bool) :
    normalizeDensity (classicalDensityBranch
      (fun x : (Fin 3 → Bool) × Unit => x.1 0) outcome (phaseDevice parity).density) =
      (readoutDevice outcome).density := by
  rw [branch_phaseDevice, normalizeDensity_apply]
  norm_num [Matrix.trace_smul, (readoutDevice outcome).isDensityMatrix.trace_eq_one, smul_smul]

private theorem outcome_phaseDevice (parity : Bool) :
    (POVM.basis.measureDensity (phaseDevice parity).density
      (phaseDevice parity).isDensityMatrix).map (fun x => x.1 0) =
      Probability.PMF.uniformOfFintype Bool := by
  ext outcome
  rw [map_measureDensity_basis_apply, branch_phaseDevice]
  norm_num [Matrix.trace_smul, (readoutDevice outcome).isDensityMatrix.trace_eq_one,
    Probability.PMF.uniformOfFintype_apply, ENNReal.ofReal_div_of_pos]

/-- Measuring the retained phase qubit is fair and leaves its conditional memory in a basis
state. Both outcomes are supported; no arbitrary zero-probability branch is introduced. -/
theorem measure_phaseDevice (parity : Bool) :
    (phaseDevice parity).measure (fun x => x 0) =
      (Probability.PMF.uniformOfFintype Bool).map (fun bit => (bit, readoutDevice bit)) := by
  have hm := DeviceState.measure_bind (fun x : Fin 3 → Bool => x 0) (phaseDevice parity)
    (fun bit state => PMF.pure (bit, state))
  simp only [Prod.mk.eta, PMF.bind_pure] at hm
  rw [hm]
  trans ((POVM.basis.measureDensity (phaseDevice parity).density
    (phaseDevice parity).isDensityMatrix).map (fun x => x.1 0)).bindOnSupport
      (fun bit _ => PMF.pure (bit, readoutDevice bit))
  · congr 1
    funext bit hbit
    congr 1
    congr 1
    apply DeviceState.ext
    · exact normalized_branch_phaseDevice parity bit
    · rfl
  · rw [PMF.bindOnSupport_eq_bind, outcome_phaseDevice]
    rfl

private theorem phase_basisState (H : (Fin 2 → Bool) → Fin 1 → Bool)
    (memory address : Bool) :
    (if address then xAddress else xResponse).eval
        ((xorQuery H (Function.Embedding.refl _)).eval
          ((if address then xAddress else xResponse).eval
            (hResponse.eval (ket ![memory, false, true])))) =
      (if H ![memory, address] 0 then -1 else 1 : ℂ) •
        hResponse.eval (ket ![memory, false, true]) := by
  cases h : H ![memory, address] 0 <;> cases address <;>
    simp only [hResponse_ket, map_add, map_smul, xAddress_ket, xResponse_ket, query_ket,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, h, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, smul_add, smul_smul] <;> module

private theorem instruction_phase_readout (H : (Fin 2 → Bool) → Fin 1 → Bool)
    (memory address : Bool) :
    (((readoutDevice memory).instruction H
      (.gate (false, false, if address then 1 else 2, []))).instruction H .query).instruction H
        (.gate (false, false, if address then 1 else 2, [])) = readoutDevice memory := by
  unfold readoutDevice
  rw [pureDevice_instruction H _ _ (decode_flip H address),
    pureDevice_instruction H _ _ (decode_query H),
    pureDevice_instruction H _ _ (decode_flip H address)]
  simp only [phase_basisState]
  exact pureDevice_smul_of_norm_eq_one _ (by split_ifs <;> simp) _ _

private theorem run_round_readout (H : (Fin 2 → Bool) → Fin 1 → Bool)
    (next : Bool → Bool) (address memory : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (PointerWalk.round address) (readoutDevice memory) =
      PMF.pure (next address, readoutDevice memory) := by
  simp only [PointerWalk.round, PointerWalk.phase, ProbOracleComp.runWith_bind, run_service,
    PMF.pure_bind, DeviceProgram.runWith_gate, DeviceProgram.runWith_query,
    ProbOracleComp.runWith_pure, instruction_phase_readout]

private theorem instruction_hadamard_readout (H : (Fin 2 → Bool) → Fin 1 → Bool)
    (memory : Bool) :
    (readoutDevice memory).instruction H (.gate (false, true, 0, [])) =
      phaseDevice memory := by
  unfold readoutDevice phaseDevice
  rw [pureDevice_instruction H _ hMemory (by rfl)]
  rfl

private theorem run_measure_phase (H : (Fin 2 → Bool) → Fin 1 → Bool)
    (next : Bool → Bool) (parity : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (pointerService next))
      (DeviceProgram.requestBit (.inl .measure) (Turing.MultiTapeTM.encUnary 0))
      (phaseDevice parity) =
      (Probability.PMF.uniformOfFintype Bool).map (fun bit => (bit, readoutDevice bit)) := by
  simpa only [Fin.val_zero] using
    (DeviceProgram.runWith_measure H (pointerService next) (0 : Fin 3)
      (phaseDevice parity)).trans (measure_phaseDevice parity)

/-- The two-round native program with an additional memory measurement between its rounds.
The controller discards this extra classical bit; the measurement still changes quantum memory. -/
@[expose] def interrupted (_input : List Bool) : WordOracleComp PointerWalk.Operation Bool := do
  PointerWalk.prepare
  let address ← PointerWalk.round false
  let _ ← DeviceProgram.requestBit (.inl .measure) (Turing.MultiTapeTM.encUnary 0)
  let _ ← PointerWalk.round address
  DeviceProgram.gate (false, true, 0, [])
  DeviceProgram.requestBit (.inl .measure) (Turing.MultiTapeTM.encUnary 0)

/-- The actual intervening measurement destroys the phase relation: the final bit is fair,
including its full conditional quantum state. The same fixed table serves both rounds. -/
theorem run_interrupted (input : List Bool) :
    ProbOracleComp.runWith (deviceWordHandler andOracle (pointerService Bool.not))
      (interrupted input) (pureDevice (ket ![false, false, false]) (norm_ket _)) =
      (Probability.PMF.uniformOfFintype Bool).map (fun bit => (bit, readoutDevice bit)) := by
  simp only [interrupted, ProbOracleComp.runWith_bind, run_prepare, PMF.pure_bind,
    run_round, run_measure_phase, PMF.bind_map, Function.comp_def, run_round_readout,
    DeviceProgram.runWith_gate, instruction_hadamard_readout, PMF.bind_const]

/-- A memory readout between rounds changes acceptance from one to one half. -/
example (input : List Bool) :
    ((ProbOracleComp.runWith (deviceWordHandler andOracle (pointerService Bool.not))
      (interrupted input) (pureDevice (ket ![false, false, false]) (norm_ket _))).map
      Prod.fst) true = 1 / 2 := by
  rw [run_interrupted, PMF.map_comp]
  norm_num [Function.comp_def, PMF.map_id, Probability.PMF.uniformOfFintype_apply]

end CslibFrontierTests.QuantumControllerCoherence
