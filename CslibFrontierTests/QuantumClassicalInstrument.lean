/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Foundations.Quantum.Measurement.Classical
public import CslibFrontierTests.QuantumState
import CslibFrontier.Foundations.Quantum.Bipartite

/-! Classical projection retains coherence inside a fiber. These clients use the exported module
API, test conditional Bell branches and null outcomes, and check supported continuation readout. -/

public section

namespace CslibFrontierTests.QuantumClassicalInstrument

open Cslib.Quantum Matrix Finset QuantumProtocols
open scoped Kronecker

/-- A deterministic request qubit and a coherent work qubit. -/
noncomputable def requestMemory : EuclideanSpace ℂ (Bool × Bool) :=
  prodState (ket false) plus

theorem requestMemory_apply (r m : Bool) :
    requestMemory.ofLp (r, m) = if r = false then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  simp [requestMemory, prodState_apply, plus_apply]

theorem norm_requestMemory : ‖requestMemory‖ = 1 := by
  rw [requestMemory, norm_prodState, norm_ket, norm_plus, mul_one]

/-- Measuring only the request preserves the entire coherent work state. -/
theorem branch_requestMemory :
    classicalDensityBranch Prod.fst false (pureState requestMemory) = pureState requestMemory := by
  rw [classicalDensityBranch_pureState]
  congr 1
  ext ⟨r, m⟩
  cases r <;> simp [projOutcomes_apply, requestMemory_apply]

/-- A branch that cannot occur has zero matrix, with no chosen substitute state. -/
theorem null_branch_requestMemory :
    classicalDensityBranch Prod.fst true (pureState requestMemory) = 0 := by
  ext ⟨r, m⟩ ⟨s, n⟩
  cases r <;> cases s <;>
    simp [classicalDensityBranch_apply, pureState_apply, requestMemory_apply]

/-- Full-register measurement would destroy coherence that the declared readout retains. -/
theorem full_measurement_changes_requestMemory :
    (∑ y, classicalDensityBranch id y (pureState requestMemory)) ≠
      classicalDensityBranch Prod.fst false (pureState requestMemory) := by
  intro h
  have he := congrArg (fun ρ : Matrix (Bool × Bool) (Bool × Bool) ℂ =>
    ρ (false, false) (false, true)) h
  rw [branch_requestMemory] at he
  norm_num [Matrix.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    classicalDensityBranch_apply, pureState_apply, requestMemory_apply,
    Complex.star_def, ← Complex.ofReal_mul] at he

/-- Each Bell branch has probability one half and keeps its correlated joint basis state. -/
theorem branch_bell (b : Bool) :
    classicalDensityBranch Prod.fst b (pureState bell) =
      (1 / 2 : ℝ) • pureState (ket (b, b)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  cases b <;> cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [classicalDensityBranch_apply, pureState_apply, bell_apply, ket_apply,
      Complex.star_def, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt]

/-- Normalizing a Bell branch yields its correlated joint basis state. -/
theorem normalized_branch_bell (b : Bool) :
    normalizeDensity (classicalDensityBranch Prod.fst b (pureState bell)) =
      pureState (ket (b, b)) := by
  rw [branch_bell, normalizeDensity_apply]
  norm_num [trace_smul, trace_pureState, smul_smul]

/-- Conditioning changes the reference; this is compatible with summed no-signalling. -/
theorem reference_branch_bell (b : Bool) :
    partialTraceLeft (classicalDensityBranch Prod.fst b (pureState bell)) =
      (1 / 2 : ℝ) • pureState (ket b) := by
  rw [branch_bell]
  ext i j
  cases b <;> cases i <;> cases j <;>
    norm_num [partialTraceLeft_apply, pureState_apply, Fintype.sum_bool]

example : partialTraceLeft (∑ b, classicalDensityBranch Prod.fst b (pureState bell)) =
    (2 : ℂ)⁻¹ • (1 : Matrix Bool Bool ℂ) := by
  rw [show (Prod.fst : Bool × Bool → Bool) = id ∘ Prod.fst from rfl,
    partialTraceLeft_sum_classicalDensityBranch, bell_eq_maxEntangled,
    partialTraceLeft_pureState_maxEntangled]
  norm_num

example : true ∉ ((POVM.basis.measureDensity (pureState requestMemory)
    (isDensityMatrix_pureState norm_requestMemory)).map Prod.fst).support := by
  rw [PMF.mem_support_iff, map_measureDensity_basis_apply, null_branch_requestMemory]
  simp

-- This exact continuation requires a support proof for normalization. Its final readout of a Bell
-- basis pair is correlated and fair, rather than an independent pair of fair bits.
example : (((POVM.basis.measureDensity (pureState bell)
      (isDensityMatrix_pureState norm_bell)).map Prod.fst).bindOnSupport fun b hb =>
    POVM.basis.measureDensity
      (normalizeDensity (classicalDensityBranch Prod.fst b (pureState bell)))
      (isDensityMatrix_normalize_classicalDensityBranch Prod.fst (pureState bell)
        (isDensityMatrix_pureState norm_bell) b hb)) (false, false) = 1 / 2 := by
  have h := bindOnSupport_classicalDensityBranch_apply Prod.fst (pureState bell)
    (isDensityMatrix_pureState norm_bell) (fun _ => LinearMap.id) (fun _ _ h => h)
    (fun _ => POVM.basis) (false, false)
  simp only [LinearMap.id_apply] at h
  rw [h]
  norm_num [Fintype.sum_bool, branch_bell, POVM.densityProb_smul,
    POVM.densityProb_pureState, POVM.prob_basis, ENNReal.ofReal_div_of_pos]

example :
    normalizeDensity (classicalDensityBranch Prod.fst true (pureState requestMemory)) = 0 := by
  rw [null_branch_requestMemory, normalizeDensity_apply]
  simp

end CslibFrontierTests.QuantumClassicalInstrument
