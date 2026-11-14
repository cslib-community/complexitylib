/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Request
public import CslibFrontier.Foundations.Quantum.Measurement.Classical
public import CslibFrontier.Foundations.Quantum.Register

/-!
# A stateful quantum handler for native controllers

The handler uses the existing joint density matrix of a fixed active register and an untouched
reference, together with the classical service state. The native word program is unchanged:
`ProbOracleComp.runWith` interprets its requests through `DeviceRequest.codec`. One fixed `H` is
passed to the complete run. Sampling `H` belongs outside that run, so adaptive stages share it.

Gates and coherent queries use the existing `OracleGateCode` decoder. A malformed instruction is
a no-op. A measurement uses `classicalDensityBranch` and `PMF.bindOnSupport`; only supported
branches are normalized. It measures one wire while retaining the complete joint state.
Classical service replies have an explicit fixed bit width. Their implementation cost remains
outside the native controller's cost, as with other external oracle services.

These are original interface and composition results. The quantum operations reuse the unitary
and projective-measurement semantics of [de Wolf][deWolf2019], §15.1, p. 128. No density matrix is
encoded as a classical machine word, and no efficient classical simulation is claimed.

## Main definitions

* `Cslib.Quantum.DeviceState`: the joint density matrix and the external classical service state.
* `Cslib.Quantum.DeviceState.evolve`: an existing active-register unitary, with reference intact.
* `Cslib.Quantum.DeviceState.measure`: supported finite classical readout.
* `Cslib.Quantum.deviceHandler`: typed elementary quantum and classical service operations.
* `Cslib.Quantum.deviceWordHandler`: the canonical word interface for the existing controller.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped Kronecker

/-- The semantic state of the device: the existing joint density matrix and classical service
state. The reference register is never addressed by a controller request. -/
structure DeviceState (m : ℕ) (κ State : Type) [Fintype κ] where
  /-- Joint active/reference density matrix. -/
  density : Matrix ((Fin m → Bool) × κ) ((Fin m → Bool) × κ) ℂ
  /-- Positivity and unit trace of that matrix. -/
  isDensityMatrix : IsDensityMatrix density
  /-- State used only by the external classical service. -/
  serviceState : State

namespace DeviceState

variable {m : ℕ} {κ State : Type} [Fintype κ]

@[ext] theorem ext {s t : DeviceState m κ State} (hρ : s.density = t.density)
    (hs : s.serviceState = t.serviceState) : s = t := by
  cases s
  cases t
  cases hρ
  cases hs
  rfl

variable [DecidableEq κ]

/-- Apply an existing unitary to the active register, retaining every reference correlation. -/
noncomputable def evolve (U : unitaryGroup (Fin m → Bool) ℂ) (s : DeviceState m κ State) :
    DeviceState m κ State where
  density := densityConj (onFirst (κ := κ) U) s.density
  isDensityMatrix := by
    rw [densityConj_apply]
    exact s.isDensityMatrix.conj_unitary (onFirst U).property
  serviceState := s.serviceState

/-- The state update is exactly the existing matrix conjugation by `U ⊗ I`. -/
theorem evolve_density (U : unitaryGroup (Fin m → Bool) ℂ) (s : DeviceState m κ State) :
    (s.evolve U).density = densityConj ((U : Matrix _ _ ℂ) ⊗ₖ (1 : Matrix κ κ ℂ)) s.density := by
  simp only [evolve, coe_onFirst]

@[simp] theorem evolve_serviceState (U : unitaryGroup (Fin m → Bool) ℂ)
    (s : DeviceState m κ State) : (s.evolve U).serviceState = s.serviceState := by
  unfold evolve
  rfl

/-- Every active-register unitary preserves the reference marginal, including entangled inputs. -/
theorem partialTraceLeft_evolve (U : unitaryGroup (Fin m → Bool) ℂ)
    (s : DeviceState m κ State) :
    partialTraceLeft (s.evolve U).density = partialTraceLeft s.density := by
  rw [evolve_density]
  apply partialTraceLeft_densityConj_kronecker
  exact UnitaryGroup.star_mul_self U

/-- Execute one existing instruction. Malformed placements or an oversized query are skipped,
exactly as in `OracleCircuit.toCircuit`. -/
noncomputable def instruction {a b : ℕ} (H : (Fin a → Bool) → Fin b → Bool)
    (code : OracleGateCode) (s : DeviceState m κ State) : DeviceState m κ State :=
  match code.toPlacedGate? m H with
  | some gate => s.evolve gate.matrix
  | none => s

/-- Instruction execution uses precisely the existing placed-gate decoder. -/
theorem instruction_apply {a b : ℕ} (H : (Fin a → Bool) → Fin b → Bool)
    (code : OracleGateCode) (s : DeviceState m κ State) :
    s.instruction H code = match code.toPlacedGate? m H with
      | some gate => s.evolve gate.matrix
      | none => s := by rfl

/-- The existing decoder's rejection leaves the complete state unchanged. -/
theorem instruction_of_invalid {a b : ℕ} (H : (Fin a → Bool) → Fin b → Bool)
    (code : OracleGateCode) (h : code.toPlacedGate? m H = none) (s : DeviceState m κ State) :
    s.instruction H code = s := by
  simp [instruction, h]

variable {Outcome : Type} [DecidableEq Outcome]

/-- Read a finite classical function of the active basis index, retaining the supported normalized
joint state. The native handler specializes this operation to reading one wire. -/
noncomputable def measure (read : (Fin m → Bool) → Outcome) (s : DeviceState m κ State) :
    PMF (Outcome × DeviceState m κ State) :=
  ((POVM.basis.measureDensity s.density s.isDensityMatrix).map
    (read ∘ Prod.fst)).bindOnSupport fun y hy => PMF.pure
      (y, ⟨normalizeDensity (classicalDensityBranch (read ∘ Prod.fst) y s.density),
        isDensityMatrix_normalize_classicalDensityBranch _ _ _ _ hy, s.serviceState⟩)

/-- Continue directly from the supported conditional states of a classical readout. -/
theorem measure_bind {α : Type} (read : (Fin m → Bool) → Outcome) (s : DeviceState m κ State)
    (next : Outcome → DeviceState m κ State → PMF α) :
    (s.measure read).bind (fun p => next p.1 p.2) =
      ((POVM.basis.measureDensity s.density s.isDensityMatrix).map
        (read ∘ Prod.fst)).bindOnSupport fun y hy =>
          next y ⟨normalizeDensity (classicalDensityBranch (read ∘ Prod.fst) y s.density),
            isDensityMatrix_normalize_classicalDensityBranch _ _ _ _ hy, s.serviceState⟩ := by
  unfold measure
  rw [← PMF.bindOnSupport_eq_bind, PMF.bindOnSupport_bindOnSupport]
  simp only [PMF.pure_bindOnSupport]

/-- Forgetting the conditional state gives exactly the existing mapped basis measurement. -/
theorem measure_map_fst (read : (Fin m → Bool) → Outcome) (s : DeviceState m κ State) :
    (s.measure read).map Prod.fst =
      (POVM.basis.measureDensity s.density s.isDensityMatrix).map (read ∘ Prod.fst) := by
  have h := measure_bind read s (fun y _ => PMF.pure y)
  rw [← PMF.bind_pure_comp]
  simpa only [Function.comp_def, PMF.bindOnSupport_pure] using h

/-- A readout whose selected branch already contains the whole state is deterministic and
preserves that state, including its reference correlations. -/
theorem measure_eq_pure_of_branch (read : (Fin m → Bool) → Outcome)
    (s : DeviceState m κ State) (y : Outcome)
    (hy : classicalDensityBranch (read ∘ Prod.fst) y s.density = s.density) :
    s.measure read = PMF.pure (y, s) := by
  let p := (POVM.basis.measureDensity s.density s.isDensityMatrix).map (read ∘ Prod.fst)
  have hmass : p y = 1 := by
    dsimp only [p]
    rw [map_measureDensity_basis_apply, hy, s.isDensityMatrix.trace_eq_one]
    simp
  have hsupp := (PMF.apply_eq_one_iff p y).mp hmass
  unfold measure
  change p.bindOnSupport _ = _
  trans p.bindOnSupport (fun _ _ => PMF.pure (y, s))
  · congr 1
    funext z hz
    change z ∈ p.support at hz
    have hzy : z = y := by simpa only [hsupp, Set.mem_singleton_iff] using hz
    subst z
    congr 1
    apply Prod.ext
    · rfl
    · apply DeviceState.ext
      · simp [hy, normalizeDensity_apply, s.isDensityMatrix.trace_eq_one]
      · rfl
  · rw [PMF.bindOnSupport_eq_bind, PMF.bind_const]

end DeviceState

variable {a b m r : ℕ} {κ State Operation : Type} [Fintype κ] [DecidableEq κ]

/-- Typed device operations. The service returns exactly `r` bits and never accesses the joint
quantum state. All coherent calls use the same supplied function `H`. -/
noncomputable def deviceHandler (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool)) :
    DeviceRequest m Operation → StateT (DeviceState m κ State) PMF (List Bool)
  | .gate code, s => PMF.pure ([], s.instruction H (.gate code))
  | .query, s => PMF.pure ([], s.instruction H .query)
  | .measure wire, s => (s.measure (fun x => x wire)).map fun p => ([p.1], p.2)
  | .service operation word, s => (service (operation, word) s.serviceState).map
      fun p => (List.ofFn p.1, { s with serviceState := p.2 })

/-- An elementary gate returns the empty acknowledgement. -/
theorem deviceHandler_gate (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (code : PhaseGateCode) (s : DeviceState m κ State) :
    deviceHandler H service (.gate code) s = PMF.pure ([], s.instruction H (.gate code)) := by rfl

/-- A coherent query returns the empty acknowledgement. -/
theorem deviceHandler_query (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (s : DeviceState m κ State) :
    deviceHandler H service .query s = PMF.pure ([], s.instruction H .query) := by rfl

/-- A wire measurement reports its single outcome bit. -/
theorem deviceHandler_measure (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (wire : Fin m) (s : DeviceState m κ State) :
    deviceHandler H service (.measure wire) s =
      (s.measure (fun x => x wire)).map (fun p => ([p.1], p.2)) := by
  rfl

/-- The classical service changes only its own state and reports exactly its fixed-width reply. -/
theorem deviceHandler_service (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (operation : Operation) (word : List Bool) (s : DeviceState m κ State) :
    deviceHandler H service (.service operation word) s =
      (service (operation, word) s.serviceState).map
        (fun p => (List.ofFn p.1, { s with serviceState := p.2 })) := by rfl

/-- Every reply has an explicit size bound: quantum acknowledgements are empty, measurements
return one bit, and classical services return their declared `r` bits. -/
theorem deviceHandler_reply_length (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (q : DeviceRequest m Operation) (s : DeviceState m κ State)
    (result : List Bool × DeviceState m κ State)
    (hresult : result ∈ (deviceHandler H service q s).support) :
    result.1.length ≤ max 1 r := by
  cases q with
  | gate code =>
    rw [deviceHandler_gate, PMF.mem_support_pure_iff] at hresult
    subst result
    simp
  | query =>
    rw [deviceHandler_query, PMF.mem_support_pure_iff] at hresult
    subst result
    simp
  | measure wire =>
    rw [deviceHandler_measure] at hresult
    obtain ⟨p, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    simp
  | service operation word =>
    rw [deviceHandler_service] at hresult
    obtain ⟨p, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    simp

/-- The word interface uses `OracleCodec.wordOracle`; noncanonical words return `[]` without
an operation or state change. -/
noncomputable def deviceWordHandler (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool)) :
    (DeviceOperation ⊕ Operation) × List Bool →
      StateT (DeviceState m κ State) PMF (List Bool) :=
  (DeviceRequest.codec m Operation).wordOracle (deviceHandler H service)

/-- The word handler is the existing codec adaptation of the typed handler. -/
theorem deviceWordHandler_eq (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool)) :
    deviceWordHandler (m := m) (κ := κ) H service =
      (DeviceRequest.codec m Operation).wordOracle (deviceHandler H service) := by rfl

/-- A canonically encoded request executes its typed operation, with the same complete state. -/
theorem deviceWordHandler_encode (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (q : DeviceRequest m Operation) :
    deviceWordHandler (κ := κ) H service q.encode = deviceHandler H service q := by
  unfold deviceWordHandler
  rw [DeviceRequest.codec_wordOracle_encode, id_map]

/-- Rejected word requests have the explicit answer `[]` and preserve the full device state. -/
theorem deviceWordHandler_of_invalid (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (request : (DeviceOperation ⊕ Operation) × List Bool)
    (h : (DeviceRequest.codec m Operation).decodeQuery request = none)
    (s : DeviceState m κ State) : deviceWordHandler H service request s = PMF.pure ([], s) := by
  unfold deviceWordHandler
  rw [OracleCodec.wordOracle_of_decodeQuery_eq_none _ _ h]
  rfl

end Cslib.Quantum
