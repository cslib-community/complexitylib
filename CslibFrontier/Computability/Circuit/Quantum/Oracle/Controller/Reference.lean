/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Handler
import CslibFrontier.Foundations.Quantum.POVM.Mixture

/-!
# Reference readout after adaptive execution

Every finite POVM on the inaccessible reference has the same outcome law before and after any
native word-oracle program runs against the quantum device. This includes adaptive intermediate
measurements, randomized stateful classical services, private coins and malformed requests.
Individual conditional reference states may change; the theorem averages over the whole run.

The proof composes the existing summed-branch partial-trace identity through `runWith`. It does
not assume a separate adversary semantics or a matrix encoding on the controller's tapes.

## Main results

* `Cslib.Quantum.DeviceState.measure_referenceMeasure`: supported measurement preserves the
  averaged reference readout.
* `Cslib.Quantum.runWith_deviceWordHandler_referenceMeasure`: the same law for the full adaptive
  program and its fixed oracle.
-/

public section

namespace Cslib.Quantum

namespace DeviceState

variable {m : ℕ} {κ State A : Type} [Fintype κ] [DecidableEq κ] [Fintype A]

/-- Read only the reference marginal with the existing density-matrix POVM semantics. -/
noncomputable def referenceMeasure (M : POVM A κ) (s : DeviceState m κ State) : PMF A :=
  M.measureDensity (partialTraceLeft s.density) s.isDensityMatrix.partialTraceLeft

/-- Reference readout depends only on the joint density, not the service's classical state. -/
theorem referenceMeasure_congr_density (M : POVM A κ) {s t : DeviceState m κ State}
    (hρ : s.density = t.density) : s.referenceMeasure M = t.referenceMeasure M := by
  ext outcome
  simp only [referenceMeasure, POVM.measureDensity_apply, hρ]

/-- Active unitary evolution preserves every reference POVM law. -/
theorem referenceMeasure_evolve (M : POVM A κ) (U : Matrix.unitaryGroup (Fin m → Bool) ℂ)
    (s : DeviceState m κ State) : (s.evolve U).referenceMeasure M = s.referenceMeasure M := by
  unfold referenceMeasure
  simp only [partialTraceLeft_evolve]

/-- Even a malformed unitary instruction preserves the reference readout. -/
theorem referenceMeasure_instruction {a b : ℕ} (M : POVM A κ)
    (H : (Fin a → Bool) → Fin b → Bool) (code : OracleGateCode) (s : DeviceState m κ State) :
    (s.instruction H code).referenceMeasure M = s.referenceMeasure M := by
  rw [instruction_apply]
  split
  · exact referenceMeasure_evolve _ _ _
  · rfl

/-- Sum over the supported normalized measurement outcomes before reading the reference. -/
theorem measure_referenceMeasure {Outcome : Type} [Finite Outcome] [DecidableEq Outcome]
    (M : POVM A κ) (read : (Fin m → Bool) → Outcome) (s : DeviceState m κ State) :
    (s.measure read).bind (fun p => p.2.referenceMeasure M) = s.referenceMeasure M := by
  let := Fintype.ofFinite Outcome
  rw [measure_bind (next := fun _ σ => σ.referenceMeasure M)]
  unfold referenceMeasure
  ext outcome
  have h := bindOnSupport_classicalDensityBranch_apply
    (read ∘ Prod.fst) s.density s.isDensityMatrix
    (fun _ => partialTraceLeftLinearMap (Fin m → Bool) κ)
    (fun _ _ hρ => by simpa only [partialTraceLeftLinearMap_apply] using hρ.partialTraceLeft)
    (fun _ => M) outcome
  simp only [partialTraceLeftLinearMap_apply] at h
  rw [h, POVM.measureDensity_apply, ← ENNReal.ofReal_sum_of_nonneg
    (fun y _ => M.densityProb_nonneg (posSemidef_partialTraceLeft
      (classicalDensityBranch_posSemidef _ y s.isDensityMatrix.posSemidef)) outcome)]
  congr 1
  rw [← POVM.densityProb_sum, ← partialTraceLeft_sum]
  exact congrArg (fun ρ => M.densityProb ρ outcome)
    (partialTraceLeft_sum_classicalDensityBranch read s.density)

end DeviceState

variable {a b m r : ℕ} {κ State Operation A : Type}
  [Fintype κ] [DecidableEq κ] [Fintype A]

/-- Each typed operation preserves the reference readout when its classical result is discarded. -/
theorem deviceHandler_referenceMeasure (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (M : POVM A κ) (q : DeviceRequest m Operation) (s : DeviceState m κ State) :
    (deviceHandler H service q s).bind (fun p => p.2.referenceMeasure M) =
      s.referenceMeasure M := by
  cases q with
  | gate code =>
    rw [deviceHandler_gate, PMF.pure_bind, DeviceState.referenceMeasure_instruction]
  | query =>
    rw [deviceHandler_query, PMF.pure_bind, DeviceState.referenceMeasure_instruction]
  | measure wire =>
    rw [deviceHandler_measure, PMF.bind_map]
    exact s.measure_referenceMeasure M (fun x => x wire)
  | service operation word =>
    rw [deviceHandler_service, PMF.bind_map]
    simp only [Function.comp_def]
    trans (service (operation, word) s.serviceState).bind (fun _ => s.referenceMeasure M)
    · congr 1
    · exact PMF.bind_const _ _

/-- Rejected words preserve the state, so the typed reference law also holds on every word. -/
theorem deviceWordHandler_referenceMeasure (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (M : POVM A κ) (q : (DeviceOperation ⊕ Operation) × List Bool)
    (s : DeviceState m κ State) :
    (deviceWordHandler H service q s).bind (fun p => p.2.referenceMeasure M) =
      s.referenceMeasure M := by
  cases h : (DeviceRequest.codec m Operation).decodeQuery q with
  | some request =>
    have hq := (DeviceRequest.codec m Operation).decodeQuery_eq_some_iff q request |>.mp h
    rw [DeviceRequest.codec_encodeQuery] at hq
    subst q
    rw [deviceWordHandler_encode]
    exact deviceHandler_referenceMeasure _ _ _ _ _
  | none => rw [deviceWordHandler_of_invalid _ _ _ h, PMF.pure_bind]

/-- Full adaptive execution preserves every finite reference POVM law. The reference can start
entangled with the active register. The final classical result is discarded in this marginal. -/
theorem runWith_deviceWordHandler_referenceMeasure {α : Type}
    (H : (Fin a → Bool) → Fin b → Bool)
    (service : Operation × List Bool → StateT State PMF (Fin r → Bool))
    (M : POVM A κ)
    (program : ProbOracleComp (fun _ : (DeviceOperation ⊕ Operation) × List Bool => List Bool) α)
    (s : DeviceState m κ State) :
    (ProbOracleComp.runWith (deviceWordHandler H service) program s).bind
      (fun p => p.2.referenceMeasure M) = s.referenceMeasure M := by
  induction program using OracleComp.induction generalizing s with
  | pure value => rw [ProbOracleComp.runWith_pure, PMF.pure_bind]
  | query_bind q next ih =>
    rw [ProbOracleComp.runWith, OracleComp.runWith_bind, OracleComp.runWith_query, PMF.bind_bind]
    simp only [ProbOracleComp.runWith] at ih
    simp only [ih]
    cases q with
    | inl n =>
      simp [OracleComp.sumHandler, StateT.lift, PMF.bind_const]
    | inr request => exact deviceWordHandler_referenceMeasure _ _ _ _ _

end Cslib.Quantum
