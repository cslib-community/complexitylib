/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.POVM
public import CslibFrontier.Foundations.Quantum.DensityMatrix
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace

/-!
# POVM readout of density matrices

For the existing POVM `M` and density matrix `ρ`, outcome `a` has probability
`Re (Tr (M.effect a * ρ))`, the mixed-state POVM rule of [de Wolf][deWolf2019], §15.1, p. 128.
The trace pairing is real and nonnegative for positive matrices; trace one makes the probabilities
a PMF. The construction uses the existing state and measurement types and agrees with
`POVM.measure` on pure states. It describes the classical outcome distribution, without specifying
a post-measurement state or an instrument.

## Main definitions

* `Cslib.Quantum.POVM.densityProb`: the real trace pairing with a measurement effect.
* `Cslib.Quantum.POVM.measureDensity`: the outcome PMF for a density matrix.

## Main results

* `Cslib.Quantum.POVM.densityProb_nonneg`, `Cslib.Quantum.POVM.sum_densityProb`: positivity and
  total mass.
* `Cslib.Quantum.POVM.densityProb_add`, `Cslib.Quantum.POVM.densityProb_smul`: linearity in real
  mixtures of state matrices.
* `Cslib.Quantum.POVM.densityProb_pureState`, `Cslib.Quantum.POVM.measureDensity_pureState`:
  agreement with the existing pure-state readout.
* `Cslib.Quantum.POVM.densityProb_basis`: basis measurement reads the diagonal of the density
  matrix.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum.POVM

open Matrix Finset
open scoped ComplexOrder

variable {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]

/-- The probability `Re (Tr (E_a ρ))` of outcome `a`. For an unnormalized positive matrix,
these weights sum to its trace. -/
@[expose] noncomputable def densityProb (M : POVM A ι) (ρ : Matrix ι ι ℂ) (a : A) : ℝ :=
  (M.effect a * ρ).trace.re

/-- A positive matrix assigns nonnegative weight to every POVM outcome. -/
theorem densityProb_nonneg (M : POVM A ι) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (a : A) :
    0 ≤ M.densityProb ρ a :=
  (Complex.nonneg_iff.mp ((M.posSemidef a).trace_mul_nonneg hρ)).1

/-- The outcome weights sum to the real part of the trace, hence to one for a density matrix. -/
theorem sum_densityProb (M : POVM A ι) (ρ : Matrix ι ι ℂ) :
    ∑ a, M.densityProb ρ a = ρ.trace.re := by
  simp only [densityProb, ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    M.sum_effect, Matrix.one_mul]

/-- POVM probabilities are additive in the state matrix. -/
theorem densityProb_add (M : POVM A ι) (ρ σ : Matrix ι ι ℂ) (a : A) :
    M.densityProb (ρ + σ) a = M.densityProb ρ a + M.densityProb σ a := by
  simp [densityProb, Matrix.mul_add, Matrix.trace_add]

/-- Scaling a state matrix by a real weight scales each outcome weight. -/
theorem densityProb_smul (M : POVM A ι) (c : ℝ) (ρ : Matrix ι ι ℂ) (a : A) :
    M.densityProb (c • ρ) a = c * M.densityProb ρ a := by
  simp [densityProb, Matrix.trace_smul]

/-- The outcome distribution of a POVM applied to a density matrix. -/
noncomputable def measureDensity (M : POVM A ι) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (M.densityProb ρ a)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => M.densityProb_nonneg hρ.posSemidef a,
      sum_densityProb, hρ.trace_eq_one, Complex.one_re, ENNReal.ofReal_one]

@[simp] theorem measureDensity_apply (M : POVM A ι) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) (a : A) :
    M.measureDensity ρ hρ a = ENNReal.ofReal (M.densityProb ρ a) := by
  rw [measureDensity, PMF.ofFintype_apply]

/-- The trace pairing with a pure-state projector equals the vector-state probability. -/
@[simp] theorem densityProb_pureState (M : POVM A ι) (ψ : EuclideanSpace ℂ ι) (a : A) :
    M.densityProb (pureState ψ) a = M.prob ψ a := by
  have hp : pureState ψ = Matrix.vecMulVec ψ.ofLp (star ψ.ofLp) := by
    ext i j
    exact pureState_apply ψ i j
  rw [densityProb, hp, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  rfl

/-- Density-matrix readout agrees with vector readout on every normalized pure state. -/
@[simp] theorem measureDensity_pureState (M : POVM A ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) :
    M.measureDensity (pureState ψ) (isDensityMatrix_pureState hψ) = M.measure ψ hψ := by
  ext a
  simp

/-- Computational-basis measurement reads the diagonal entries of the density matrix. -/
theorem densityProb_basis (ρ : Matrix ι ι ℂ) (i : ι) :
    basis.densityProb ρ i = (ρ i i).re := by
  rw [densityProb, basis_effect, Matrix.trace_single_mul, one_smul]

end Cslib.Quantum.POVM
