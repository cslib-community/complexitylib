/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.Lattice.Periodization
public import CslibFrontier.Foundations.Probability.Gaussian.Discrete

import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Continuous lattice Gaussian mass

## Main results

* `ZLattice.summable_norm_restrict_gaussianWeight`: normal convergence of Gaussian lattice sums.
* `ZLattice.continuous_gaussianMass`: the Gaussian normalizer is continuous in its center.

Every positive width and every discrete lattice in a finite-dimensional real normed space
is allowed. These are analytic prerequisites for lattice Poisson summation, not a Poisson,
smoothing, dimension-uniform mass comparison, or sampling theorem.

## References

The Gaussian convention is [Regev2009], equations (4) and (6), printed pages 13–14 of the
May 2, 2009 author version. Continuity here is a proved analytic prerequisite, not a claim
that Regev's Lemma 2.14 or the reduction has been formalized.
-/

public section

noncomputable section

open Asymptotics Filter ProbabilityTheory TopologicalSpace
open scoped Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E]

/-- The Gaussian weight is continuous, including at width zero under Lean's division convention. -/
theorem continuous_gaussianWeight (s : ℝ) : Continuous (gaussianWeight s : E → ℝ) := by
  unfold gaussianWeight
  fun_prop

variable [ProperSpace E]

/-- At positive width, Gaussian decay dominates every real power of the norm. -/
theorem isBigO_gaussianWeight_cocompact (s : ℝ) (hs : 0 < s) (r : ℝ) :
    (gaussianWeight s : E → ℝ) =O[cocompact E] (fun x ↦ ‖x‖ ^ r) := by
  have ha : -Real.pi / s ^ 2 < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos)
    (sq_pos_of_pos hs)
  have hdecay := (rexp_neg_quadratic_isLittleO_rpow_atTop ha 0 r).comp_tendsto
    (tendsto_norm_cocompact_atTop (E := E))
  change (fun x : E ↦ Real.exp (-Real.pi * ‖x‖ ^ 2 / s ^ 2)) =O[cocompact E] _
  simpa only [Function.comp_def, zero_mul, add_zero, div_mul_eq_mul_div] using hdecay.isBigO

end ProbabilityTheory

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- Gaussian lattice translates have summable sup norms on every compact set. -/
theorem summable_norm_restrict_gaussianWeight (s : ℝ) (hs : 0 < s) (K : Compacts E) :
    Summable (fun z : L ↦ ‖((⟨gaussianWeight s, continuous_gaussianWeight s⟩ : C(E, ℝ)).comp
      (ContinuousMap.addRight (z : E))).restrict K‖) :=
  summable_norm_restrict_translate L ⟨gaussianWeight s, continuous_gaussianWeight s⟩
    (b := (Module.finrank ℤ L : ℝ) + 1) (by linarith)
    (isBigO_gaussianWeight_cocompact s hs _) K

/-- The normalizing Gaussian mass is continuous in the arbitrary center. -/
theorem continuous_gaussianMass (s : ℝ) (hs : 0 < s) : Continuous (gaussianMass L s) := by
  have h := (continuous_tsum_translate L
    ⟨gaussianWeight s, continuous_gaussianWeight s⟩
    (b := (Module.finrank ℤ L : ℝ) + 1) (by linarith)
    (isBigO_gaussianWeight_cocompact s hs _)).comp continuous_neg
  change Continuous (fun c : E ↦ ∑' z : L, gaussianWeight s ((z : E) - c))
  simpa only [Function.comp_def, ContinuousMap.coe_mk, neg_add_eq_sub] using h

end ZLattice
