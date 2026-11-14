/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Measurement.Basis

/-!
# Multi-outcome classical readouts of computational-basis measurements

Measuring a unit quantum state `ψ : EuclideanSpace ℂ ι` in the computational basis and applying
a classical readout map `out : ι → β` yields a probability mass function `Cslib.Quantum.measureOut`
over arbitrary outcome values `β` (such as `ℝ` or an ordered alphabet `α`).

## Main definitions

* `Cslib.Quantum.measureOut`: distribution of a classical readout of a computational-basis
  measurement.

## Main results

* `Cslib.Quantum.measureOut_apply`: probability mass of an outcome value `b : β`.
* `Cslib.Quantum.measureOut_ket`: reading a basis state returns its readout with certainty.
* `Cslib.Quantum.measureOut_eq_ofReal_measureProb`: point mass at `b` equals the computational-basis
  probability of the readout fiber over `b`.
* `Cslib.Quantum.measureOut_toOuterMeasure_apply`: event probabilities under `measureOut`.
-/

public section

namespace Cslib.Quantum

open Finset

/-- Measuring a unit state `ψ` in the computational basis and decoding outcomes through
`out : ι → β`. -/
@[expose] noncomputable def measureOut {ι β : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (out : ι → β) : PMF β :=
  (measure ψ hψ).map out

/-- Reading a computational basis state returns its classical readout with certainty. -/
@[simp] theorem measureOut_ket {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι) (out : ι → β) : measureOut (ket x) (norm_ket x) out = PMF.pure (out x) := by
  simp [measureOut, PMF.pure_map]

/-- Probability mass of an outcome value `b` under `measureOut`. -/
@[simp] theorem measureOut_apply {ι β : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (out : ι → β) (b : β) :
    measureOut ψ hψ out b =
      ∑ a : ι, by classical exact if b = out a then measure ψ hψ a else 0 := by
  classical
  simp [measureOut, PMF.map_apply]

/-- The probability that `measureOut` lands in `{b | P b}` equals `measureProb` of the preimage
subset `{y | P (out y)}`. -/
theorem measureOut_toOuterMeasure_apply {ι β : Type*} [Fintype ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (out : ι → β) (P : β → Prop)
    [DecidablePred P] :
    (measureOut ψ hψ out).toOuterMeasure {b | P b} =
      ENNReal.ofReal (measureProb ψ (univ.filter fun y => P (out y))) := by
  classical
  rw [measureOut, PMF.toOuterMeasure_map_apply, ← measure_toOuterMeasure_apply ψ hψ]
  congr 1
  ext y
  simp

/-- Point mass of `measureOut` at `b : β` equals `ENNReal.ofReal` of `measureProb` on the preimage
fiber `{a | out a = b}`. -/
theorem measureOut_eq_ofReal_measureProb {ι β : Type*} [Fintype ι] [DecidableEq β]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (out : ι → β) (b : β) :
    measureOut ψ hψ out b = ENNReal.ofReal (measureProb ψ {a | out a = b}) := by
  have h := measureOut_toOuterMeasure_apply ψ hψ out (fun y => y = b)
  rwa [Set.ofPred_eq_eq_singleton, PMF.toOuterMeasure_apply_singleton] at h

end Cslib.Quantum
