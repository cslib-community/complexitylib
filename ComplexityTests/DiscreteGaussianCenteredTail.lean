/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.Gaussian.CenteredTail

/-! Centered mass scaling and strict-radius tails on a nonunit lattice and in dimension zero. -/

open Module ProbabilityTheory MeasureTheory

noncomputable section

namespace ComplexityTests.DiscreteGaussianCenteredTail

private def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ => (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

private abbrev L := Submodule.span ℤ (Set.range twoBasis)

example : DiscreteTopology L := inferInstance
example : IsZLattice ℝ L := inferInstance

example : ZLattice.gaussianMass L 2 0 / ZLattice.gaussianMass L 1 0 ≤ 2 := by
  simpa using ZLattice.gaussianMass_zero_div_le L 1 (by norm_num) 2 (by norm_num)

/-- The one-width source statement follows from the two-width ratio bound. -/
example (a : ℝ) (ha : 1 ≤ a) :
    ZLattice.gaussianMass L a 0 ≤ a * ZLattice.gaussianMass L 1 0 := by
  apply (div_le_iff₀ (ZLattice.gaussianMass_pos L 1 (by norm_num) 0)).mp
  simpa using ZLattice.gaussianMass_zero_div_le L 1 (by norm_num) a ha

example (s : ℝ) (hs : 0 < s) :
    ZLattice.gaussianMass L s 0 / ZLattice.gaussianMass L s 0 ≤ (s / s) := by
  simpa using ZLattice.gaussianMass_zero_div_le L s hs s le_rfl

example (s : ℝ) (hs : 0 < s) :
    ZLattice.gaussianMass L s 0 / ZLattice.gaussianMass L s 0 = 1 :=
  div_self (ZLattice.gaussianMass_pos L s hs 0).ne'

/-- At width two, the source radius in dimension one is exactly two. -/
example : (ZLattice.discreteGaussian L 2 (by norm_num) 0).toOuterMeasure
    {z : L | 2 < ‖(z : ℝ)‖} < ENNReal.ofReal (1 / 4) := by
  simpa using ZLattice.discreteGaussian_zero_norm_gt_sqrt_lt L 2 (by norm_num)

example : (ZLattice.discreteGaussian L 2 (by norm_num) 0).toOuterMeasure
    {z : L | 0 ≤ ‖(z : ℝ)‖} ≤ 2 := by
  simpa using ZLattice.discreteGaussian_zero_norm_ge_le L 2 (by norm_num) 0 le_rfl

private def boundaryPoint : L := ⟨twoBasis (), Submodule.subset_span (Set.mem_range_self ())⟩

example : ‖(boundaryPoint : ℝ)‖ = 2 := by
  norm_num [boundaryPoint, twoBasis, Basis.isUnitSMul_apply]

/-- The nonzero lattice point at the radius is excluded by the source's strict event. -/
example : boundaryPoint ∉ {z : L | 2 < ‖(z : ℝ)‖} := by
  norm_num [boundaryPoint, twoBasis, Basis.isUnitSMul_apply]

private abbrev Point := EuclideanSpace ℝ (Fin 0)
private abbrev pointLattice := Submodule.span ℤ
  (Set.range (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis)

example : DiscreteTopology pointLattice := inferInstance
example : IsZLattice ℝ pointLattice := inferInstance

example (s : ℝ) (hs : 0 < s) (t : ℝ) (hst : s ≤ t) :
    ZLattice.gaussianMass pointLattice t 0 / ZLattice.gaussianMass pointLattice s 0 ≤ 1 := by
  simpa using ZLattice.gaussianMass_zero_div_le pointLattice s hs t hst

example (s : ℝ) (hs : 0 < s) :
    (ZLattice.discreteGaussian pointLattice s hs 0).toOuterMeasure
      {z : pointLattice | 0 < ‖(z : Point)‖} < 1 := by
  simpa using ZLattice.discreteGaussian_zero_norm_gt_sqrt_lt pointLattice s hs

example (s : ℝ) (hs : 0 < s) :
    (ZLattice.discreteGaussian pointLattice s hs 0).toOuterMeasure
      {z : pointLattice | 0 < ‖(z : Point)‖} = 0 := by
  have hempty : {z : pointLattice | 0 < ‖(z : Point)‖} = ∅ := by
    ext z
    change (0 < ‖(z : Point)‖) ↔ False
    rw [Subsingleton.elim (z : Point) 0]
    simp
  rw [hempty, measure_empty]

end ComplexityTests.DiscreteGaussianCenteredTail
