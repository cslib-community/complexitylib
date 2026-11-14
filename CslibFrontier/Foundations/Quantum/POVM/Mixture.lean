/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.POVM.Density
public import CslibFrontier.Probability.PMF

/-!
# Measuring finite mixtures

A finite PMF-weighted sum of density matrices is a density matrix. Measuring that sum agrees
with first sampling the classical index and then measuring its state. These are original bridges
between the existing density-matrix and PMF representations, with no new mixture or state type.

## Main results

* `Cslib.Quantum.isDensityMatrix_pmf_sum`: a finite probabilistic mixture is normalized.
* `Cslib.Quantum.POVM.measureDensity_pmf_sum`: measuring a mixture is a probabilistic bind.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped ComplexOrder

variable {ι A B : Type*} [Fintype ι] [Fintype A]

/-- A finite probabilistic mixture of density matrices is again a density matrix. -/
theorem isDensityMatrix_pmf_sum (p : PMF A) (ρ : A → Matrix ι ι ℂ)
    (hρ : ∀ a, IsDensityMatrix (ρ a)) :
    IsDensityMatrix (∑ a, (p a).toReal • ρ a) := by
  refine ⟨posSemidef_sum _ (fun a _ => (hρ a).posSemidef.smul ENNReal.toReal_nonneg), ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, (hρ _).trace_eq_one]
  rw [← sum_smul, Probability.PMF.sum_toReal, one_smul]

omit [Fintype A] in
/-- The density probability is additive over finite sums, without normalization assumptions. -/
theorem POVM.densityProb_sum [DecidableEq ι] [Fintype B] (M : POVM B ι)
    (s : Finset A) (ρ : A → Matrix ι ι ℂ) (b : B) :
    M.densityProb (∑ a ∈ s, ρ a) b = ∑ a ∈ s, M.densityProb (ρ a) b := by
  simp [POVM.densityProb, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- Measuring a finite mixture agrees with sampling its classical index and measuring once. -/
theorem POVM.measureDensity_pmf_sum [DecidableEq ι] [Fintype B] (M : POVM B ι)
    (p : PMF A) (ρ : A → Matrix ι ι ℂ) (hρ : ∀ a, IsDensityMatrix (ρ a)) :
    M.measureDensity (∑ a, (p a).toReal • ρ a) (isDensityMatrix_pmf_sum p ρ hρ) =
      p.bind (fun a => M.measureDensity (ρ a) (hρ a)) := by
  ext b
  rw [POVM.measureDensity_apply, PMF.bind_apply, tsum_fintype, POVM.densityProb_sum]
  simp only [POVM.densityProb_smul, POVM.measureDensity_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ =>
    mul_nonneg ENNReal.toReal_nonneg (M.densityProb_nonneg (hρ a).posSemidef b))]
  apply sum_congr rfl
  intro a _
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (p.apply_ne_top a)]

end Cslib.Quantum
