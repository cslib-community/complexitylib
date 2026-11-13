/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Foundations.Quantum.POVM.Density
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import CslibFrontier.Foundations.Quantum.Measurement.Basis
import CslibFrontier.Foundations.Quantum.Pauli

/-! Mixed-state POVM readout through ordinary module imports: biased mixtures, noncommuting
measurement effects, pure-state agreement and the empty-dimensional edge case. -/

public section

namespace CslibFrontierTests.QuantumDensityPOVM

open Cslib.Quantum Matrix Finset
open scoped ComplexOrder ENNReal

/-- A biased classical mixture of the two basis states. -/
@[expose] noncomputable def biasedState : Matrix Bool Bool ℂ :=
  (1 / 3 : ℝ) • pureState (ket false) + (2 / 3 : ℝ) • pureState (ket true)

theorem isDensityMatrix_biasedState : IsDensityMatrix biasedState := by
  refine ⟨((posSemidef_pureState (ket false)).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)).add
    ((posSemidef_pureState (ket true)).smul (by norm_num : (0 : ℝ) ≤ 2 / 3)), ?_⟩
  norm_num [biasedState, trace_add, trace_smul, trace_pureState]

-- The public effect equation identifies the basis effect with its pure-state projector.
example (b : Bool) : (POVM.basis : POVM Bool Bool).effect b = pureState (ket b) := by
  rw [POVM.basis_effect]
  ext i j
  cases b <;> cases i <;> cases j <;> simp [Matrix.single, pureState_apply]

-- Complex-order positivity includes reality of the trace, not only positivity of its real part.
example (M : POVM Bool Bool) (a : Bool) : (M.effect a * biasedState).trace.im = 0 :=
  (Complex.nonneg_iff.mp
    ((M.posSemidef a).trace_mul_nonneg isDensityMatrix_biasedState.posSemidef)).2.symm

-- The mixed readout retains its classical weights; it is not a uniform or pure output.
example : POVM.basis.measureDensity biasedState isDensityMatrix_biasedState false = 1 / 3 := by
  rw [POVM.measureDensity_apply, biasedState, POVM.densityProb_add,
    POVM.densityProb_smul, POVM.densityProb_smul, POVM.densityProb_pureState,
    POVM.densityProb_pureState, POVM.prob_basis, POVM.prob_basis]
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

example : POVM.basis.measureDensity biasedState isDensityMatrix_biasedState true = 2 / 3 := by
  rw [POVM.measureDensity_apply, POVM.densityProb_basis]
  norm_num [biasedState, pureState_apply, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

-- The X measurement is fair on this same mixed state.
example (b : Bool) :
    (POVM.ofObservable pauliX pauliX_isHermitian pauliX_mul_self).measureDensity
      biasedState isDensityMatrix_biasedState b = 1 / 2 := by
  rw [POVM.measureDensity_apply]
  cases b <;> norm_num [POVM.densityProb, POVM.ofObservable_effect, biasedState,
    trace, Matrix.mul_apply, Fintype.sum_bool, pureState_apply,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]

-- Positivity of Tr(Eρ) does not assume the effect and state commute.
example : ¬Commute
    ((POVM.ofObservable pauliX pauliX_isHermitian pauliX_mul_self).effect false) biasedState := by
  intro h
  have hc := congrArg (fun X : Matrix Bool Bool ℂ => X false true) h.eq
  norm_num [POVM.ofObservable_effect, biasedState, Matrix.mul_apply, Fintype.sum_bool,
    pureState_apply] at hc

-- Density readout of a pure basis state recovers the existing deterministic outcome.
example (b : Bool) :
    POVM.basis.measureDensity (pureState (ket b)) (isDensityMatrix_pureState (norm_ket b)) =
      PMF.pure b := by
  rw [POVM.measureDensity_pureState _ _ (norm_ket b), POVM.measure_basis, measure_ket]

-- The zero-dimensional matrix cannot satisfy the trace-one condition.
example : ¬∃ ρ : Matrix (Fin 0) (Fin 0) ℂ, IsDensityMatrix ρ := by
  rintro ⟨ρ, hρ⟩
  have h := hρ.trace_eq_one
  simp at h

end CslibFrontierTests.QuantumDensityPOVM
