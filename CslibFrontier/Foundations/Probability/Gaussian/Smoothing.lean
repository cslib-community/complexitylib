/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside the lattice Gaussian Poisson API)

public import CslibFrontier.Foundations.Probability.Gaussian.ShiftBounds
public import CslibFrontier.Foundations.Probability.Gaussian.CenteredTail

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Width criteria for small nonzero dual Gaussian mass

An explicit lower bound on the norm of every nonzero dual vector yields a sufficient width
criterion for the actual nonzero dual mass. The criterion follows from the proved centered
Gaussian tail estimate and the probability of the zero lattice point. Discreteness supplies
a positive gap, so every positive error tolerance is attained at all sufficiently large widths.
No minimum smoothing parameter or small-tail assumption is introduced as a definition.

## Main results

* `ZLattice.gaussianMass_dual_sub_one_le_of_gap`: a quantitative sufficient width criterion.
* `ZLattice.eventually_gaussianMass_dual_sub_one_le`: the criterion is eventually satisfiable
  for every full-rank discrete lattice and every positive error tolerance.

## References

These are supporting consequences of the centered Gaussian tail estimate for the explicit
dual-tail condition in [Regev2009], Claim 3.8, printed page 22 of the May 2, 2009 author version.
The numerical width criterion is derived here; it is not a definition of the source's minimum
smoothing parameter. Uniform shifted mass estimates are in `Gaussian.ShiftBounds`.
-/

public section

noncomputable section

open Module ProbabilityTheory MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem discreteGaussian_nonzero_toReal
    (L : Submodule ℤ E) [DiscreteTopology L] (s : ℝ) (hs : 0 < s) :
    ((discreteGaussian L s hs 0).toOuterMeasure {z : L | z ≠ 0}).toReal =
      1 - 1 / gaussianMass L s 0 := by
  let p := discreteGaussian L s hs 0
  have hevent : {z : L | z ≠ 0} = ({0} : Set L)ᶜ := rfl
  rw [hevent, ← PMF.toMeasure_apply_eq_toOuterMeasure_apply p
    (measurableSet_singleton 0).compl]
  change p.toMeasure.real ({0} : Set L)ᶜ = _
  rw [probReal_compl_eq_one_sub (measurableSet_singleton 0), Measure.real,
    PMF.toMeasure_apply_singleton p 0 (measurableSet_singleton 0)]
  simp [p, discreteGaussian_apply_toReal, gaussianWeight]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- An explicit dual gap and exponential width criterion bound the actual nonzero dual mass.
The error `ε` is arbitrary and positive; it is not assumed to bound the desired mass. -/
theorem gaussianMass_dual_sub_one_le_of_gap (s : ℝ) (hs : 0 < s) (a : ℝ) (ha : 0 < a)
    (hgap : ∀ w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
      w ≠ 0 → a ≤ ‖(w : E)‖)
    (ε : ℝ) (hε : 0 < ε)
    (hwidth : 2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * s ^ 2 * a ^ 2 / 4) ≤
      ε / (1 + ε)) :
    gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have : IsZLattice ℝ D := isZLattice_dualSubmodule L
  have hs' : 0 < 1 / s := one_div_pos.mpr hs
  have htail := discreteGaussian_zero_norm_ge_le D (1 / s) hs' a ha.le
  have hexp : -3 * Real.pi * a ^ 2 / (4 * (1 / s) ^ 2) =
      -3 * Real.pi * s ^ 2 * a ^ 2 / 4 := by
    field_simp
  rw [hexp] at htail
  have hsubset : {w : D | w ≠ 0} ⊆ {w : D | a ≤ ‖(w : E)‖} := fun w hw ↦ hgap w hw
  have hprob := ((discreteGaussian D (1 / s) hs' 0).toOuterMeasure.mono hsubset).trans
    (htail.trans (ENNReal.ofReal_le_ofReal hwidth))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
  rw [OuterMeasure.measureOf_eq_coe, discreteGaussian_nonzero_toReal D (1 / s) hs',
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hm : 0 < gaussianMass D (1 / s) 0 := gaussianMass_pos D (1 / s) hs' 0
  have he : 0 < 1 + ε := by positivity
  have hr : 1 - 1 / gaussianMass D (1 / s) 0 =
      (gaussianMass D (1 / s) 0 - 1) / gaussianMass D (1 / s) 0 := by
    field_simp
  rw [hr] at hreal
  have hmul := (div_le_div_iff₀ hm he).mp hreal
  change gaussianMass D (1 / s) 0 - 1 ≤ ε
  nlinarith

/-- Every positive error tolerance eventually bounds the actual nonzero dual mass at
reciprocal width. The conclusion includes positivity of the original width, and dimension zero
is covered without a separate nontriviality hypothesis. -/
theorem eventually_gaussianMass_dual_sub_one_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, 0 < s ∧
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ≤ ε := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_discrete ({0} : Set D)) 0 (by simp)
  have hgap : ∀ w : D, w ≠ 0 → a ≤ ‖(w : E)‖ := by
    intro w hw
    apply le_of_not_gt
    intro hnorm
    apply hw
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hnorm)
  have hc : -3 * Real.pi * a ^ 2 / 4 < 0 := by
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) (sq_pos_of_pos ha)) (by norm_num)
  have hexp : Tendsto (fun s : ℝ ↦ -3 * Real.pi * s ^ 2 * a ^ 2 / 4) atTop atBot := by
    convert (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg hc using 1
    ext s
    ring
  have hlimit : Tendsto
      (fun s : ℝ ↦ 2 ^ finrank ℝ E * Real.exp (-3 * Real.pi * s ^ 2 * a ^ 2 / 4))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hexp).const_mul (2 ^ finrank ℝ E)
  have hevent := hlimit.eventually (gt_mem_nhds (by positivity : 0 < ε / (1 + ε)))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hevent] with s hs hwidth
  exact ⟨hs, gaussianMass_dual_sub_one_le_of_gap L s hs a ha hgap ε hε hwidth.le⟩

end ZLattice
