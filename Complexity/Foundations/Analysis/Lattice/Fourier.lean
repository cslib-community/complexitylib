/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier coefficients of lattice periodization

An integrable function has the expected unnormalized Fourier coefficient over a lattice
fundamental domain at every frequency in the existing inner-product dual submodule. The
periodization is the pointwise `tsum`; no pointwise convergence hypothesis is required.
The integration and summation interchange follows from integrability and Mathlib's
fundamental-domain decomposition of the integral of the norm.

This is a supporting unfolding identity, not Poisson summation. It neither reconstructs
the periodization from its Fourier series nor normalizes the quotient Haar measure.

## Main results

* `ZLattice.fourierChar_inner_eq_one`: dual frequencies annihilate lattice translations.
* `ZLattice.integral_fourierChar_tsum_translate`: unnormalized Fourier coefficient identity.
-/

public section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A frequency in the inner-product dual submodule has trivial character on the lattice. -/
theorem fourierChar_inner_eq_one {L : Submodule ℤ E} {w : E}
    (hw : w ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (z : L) :
    Real.fourierChar ⟪(z : E), w⟫ = 1 := by
  obtain ⟨m, hm⟩ := Submodule.mem_one.mp (hw z z.property)
  change (m : ℝ) = ⟪w, (z : E)⟫ at hm
  rw [real_inner_comm, ← hm, Real.fourierChar_apply']
  exact Circle.exp_two_pi_mul_int m

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The integral over a fundamental domain is the Fourier transform at a dual frequency.
The domain integral uses ambient volume, without division by the lattice covolume. -/
theorem integral_fourierChar_tsum_translate {L : Submodule ℤ E} [Countable L]
    {s : Set E} (hs : IsAddFundamentalDomain L s volume) {f : E → ℂ}
    (hf : Integrable f) {w : E} (hw : w ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :
    (∫ x in s, (Real.fourierChar (-⟪x, w⟫) : ℂ) * ∑' z : L, f (x + z)) =
      𝓕 f w := by
  let : VAddInvariantMeasure L E volume :=
    inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E volume)
  let g : E → ℂ := fun x => Real.fourierChar (-⟪x, w⟫) • f x
  have hg : Integrable g := (Real.fourierIntegral_convergent_iff w).2 hf
  have hinv (z : L) (x : E) :
      Real.fourierChar (-⟪x + z, w⟫) = Real.fourierChar (-⟪x, w⟫) := by
    simp only [inner_add_left, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
      fourierChar_inner_eq_one hw z, inv_one, mul_one]
  calc
    _ = ∫ x in s, ∑' z : L, g (z +ᵥ x) := by
      congr 1
      funext x
      simp only [g, Submodule.vadd_def, vadd_eq_add, add_comm (↑_ : E) x, hinv, Circle.smul_def,
        smul_eq_mul, tsum_mul_left]
    _ = ∑' z : L, ∫ x in s, g (z +ᵥ x) := by
      apply integral_tsum
      · exact fun z => (hg.1.comp_quasiMeasurePreserving
          (measurePreserving_vadd z volume).quasiMeasurePreserving).restrict
      · rw [← hs.lintegral_eq_tsum'' (‖g ·‖ₑ)]
        exact ne_of_lt hg.2
    _ = ∫ x, g x := (hs.integral_eq_tsum'' g hg).symm
    _ = 𝓕 f w := rfl

end ZLattice
