/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, discrete Gaussian distributions on lattices)

public import Complexity.Init
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Discrete Gaussian distributions on lattices

A discrete subgroup of a finite-dimensional real normed space has finite, strictly positive
Gaussian mass at every center and every positive width. Normalizing this mass gives a PMF on
the lattice, including lattices that do not span the ambient space.

## Main definitions

* `ProbabilityTheory.gaussianWeight`: the unnormalized weight `exp (-π * ‖x‖² / s²)`.
* `ZLattice.gaussianMass`: the sum of these weights over a shifted lattice.
* `ZLattice.discreteGaussian`: the normalized distribution on lattice points.

## Main results

* `ZLattice.summable_gaussianWeight`: convergence of the shifted lattice sum.
* `ZLattice.gaussianMass_pos`: strict positivity of the normalizer.
* `ZLattice.support_discreteGaussian`: every lattice point has positive probability.

## References

The Euclidean specialization is [Regev2009], §2, equations (4) and (6), printed pages 13–14
of the May 2, 2009 author version. Here the center is explicit, and the convergence proof also
works for arbitrary norms and lower-rank discrete subgroups. This constructs a mathematical
distribution; it supplies no sampling algorithm, smoothing estimate, or worst-case reduction.
-/

public section

noncomputable section

open Filter ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E]

/-- The unnormalized Gaussian weight of width `s`. The width is required to be positive when
constructing a distribution. -/
@[expose] def gaussianWeight (s : ℝ) (x : E) : ℝ :=
  Real.exp (-Real.pi * ‖x‖ ^ 2 / s ^ 2)

/-- Gaussian weights are strictly positive. -/
theorem gaussianWeight_pos (s : ℝ) (x : E) : 0 < gaussianWeight s x :=
  Real.exp_pos _

end ProbabilityTheory

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- Gaussian weights are summable on every shifted discrete lattice at positive width. -/
theorem summable_gaussianWeight (s : ℝ) (hs : 0 < s) (c : E) :
    Summable (fun z : L ↦ gaussianWeight s ((z : E) - c)) := by
  have hclosed : IsClosed (L : Set E) := L.toAddSubgroup.isClosed_of_discreteTopology
  have ht : Tendsto (fun z : L ↦ ‖(z : E) - c‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
      ((Homeomorph.subRight c).isClosedEmbedding.comp hclosed.isClosedEmbedding_subtypeVal)
  let r : ℝ := -(Module.finrank ℤ L : ℝ) - 1
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r]; linarith
  have ha : -Real.pi / s ^ 2 < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos)
    (sq_pos_of_pos hs)
  have hdecay := (rexp_neg_quadratic_isLittleO_rpow_atTop ha 0 r).comp_tendsto ht
  apply summable_of_isBigO (summable_norm_sub_rpow L r hr c)
  convert hdecay.isBigO using 1 <;> simp only [Function.comp_def, gaussianWeight,
    zero_mul, add_zero, div_mul_eq_mul_div]

/-- The total unnormalized Gaussian mass of `L`, centered at `c` with width `s`. -/
@[expose] def gaussianMass (s : ℝ) (c : E) : ℝ :=
  ∑' z : L, gaussianWeight s ((z : E) - c)

/-- At positive width the convergent Gaussian normalizer is strictly positive. -/
theorem gaussianMass_pos (s : ℝ) (hs : 0 < s) (c : E) : 0 < gaussianMass L s c :=
  (summable_gaussianWeight L s hs c).tsum_pos
    (fun z ↦ (gaussianWeight_pos s ((z : E) - c)).le) 0 (gaussianWeight_pos _ _)

/-- The discrete Gaussian on `L` centered at `c`, with strictly positive width `s`.
The sample is a lattice point; the center need not belong to the lattice. -/
def discreteGaussian (s : ℝ) (hs : 0 < s) (c : E) : PMF L :=
  PMF.normalize (fun z : L ↦ ENNReal.ofReal (gaussianWeight s ((z : E) - c)))
    (by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun z : L ↦ (gaussianWeight_pos s ((z : E) - c)).le)
        (summable_gaussianWeight L s hs c)]
      exact (ENNReal.ofReal_pos.mpr (gaussianMass_pos L s hs c)).ne')
    (summable_gaussianWeight L s hs c).tsum_ofReal_ne_top

/-- The probability of a point is its Gaussian weight divided by the total lattice mass. -/
theorem discreteGaussian_apply (s : ℝ) (hs : 0 < s) (c : E) (z : L) :
    discreteGaussian L s hs c z =
      ENNReal.ofReal (gaussianWeight s ((z : E) - c)) / ENNReal.ofReal (gaussianMass L s c) := by
  rw [discreteGaussian, PMF.normalize_apply, ← ENNReal.ofReal_tsum_of_nonneg
    (fun z : L ↦ (gaussianWeight_pos s ((z : E) - c)).le)
    (summable_gaussianWeight L s hs c)]
  rfl

/-- The real-valued probability of a lattice point. -/
theorem discreteGaussian_apply_toReal (s : ℝ) (hs : 0 < s) (c : E) (z : L) :
    (discreteGaussian L s hs c z).toReal =
      gaussianWeight s ((z : E) - c) / gaussianMass L s c := by
  rw [discreteGaussian_apply, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (gaussianWeight_pos s ((z : E) - c)).le,
    ENNReal.toReal_ofReal (gaussianMass_pos L s hs c).le]

/-- Every point of the lattice is in the support of its discrete Gaussian. -/
@[simp] theorem support_discreteGaussian (s : ℝ) (hs : 0 < s) (c : E) :
    (discreteGaussian L s hs c).support = Set.univ := by
  ext z
  simp [discreteGaussian, gaussianWeight_pos]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- Moving the center by a lattice vector leaves the total Gaussian mass unchanged. -/
theorem gaussianMass_add (s : ℝ) (c : E) (a : L) :
    gaussianMass L s (c + a) = gaussianMass L s c := by
  unfold gaussianMass
  rw [← (Equiv.addRight a).tsum_eq
    (fun z : L ↦ gaussianWeight s ((z : E) - (c + a)))]
  simp only [Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub]

/-- Translating the center and the sampled point by the same lattice vector preserves mass. -/
theorem discreteGaussian_apply_add (s : ℝ) (hs : 0 < s) (c : E) (a z : L) :
    discreteGaussian L s hs (c + a) (z + a) = discreteGaussian L s hs c z := by
  rw [discreteGaussian_apply, discreteGaussian_apply, gaussianMass_add]
  simp only [Submodule.coe_add, add_sub_add_right_eq_sub]

/-- Translating a discrete Gaussian by a lattice vector translates its center. -/
theorem map_add_discreteGaussian (s : ℝ) (hs : 0 < s) (c : E) (a : L) :
    (discreteGaussian L s hs c).map (fun z ↦ z + a) = discreteGaussian L s hs (c + a) := by
  classical
  ext z
  rw [PMF.map_apply]
  simp only [← sub_eq_iff_eq_add, tsum_ite_eq']
  simpa only [sub_add_cancel] using (discreteGaussian_apply_add L s hs c a (z - a)).symm

end ZLattice
