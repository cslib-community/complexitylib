/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Gaussian.Poisson

/-!
# Centered lattice Gaussian mass scaling

## Main results

* `ZLattice.gaussianMass_zero_div_le`: increasing the width from `s` to `t` increases
  centered Gaussian mass by at most `(t / s) ^ dim`.

## References

This is the two-width form of [Regev2009], Lemma 2.4, printed page 16 of the May 2, 2009
author version, credited there to Banaszczyk. The proof uses actual Poisson summation and
monotonicity of the positive dual Gaussian weights. No mass comparison is assumed.
-/

public section

noncomputable section

open Module ProbabilityTheory MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory

/-- A Gaussian weight increases with its positive width. -/
theorem gaussianWeight_le_of_le {E : Type*} [NormedAddCommGroup E]
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : E) :
    gaussianWeight s x ≤ gaussianWeight t x := by
  apply Real.exp_le_exp.mpr
  have hsq : s ^ 2 ≤ t ^ 2 := by nlinarith [hs.trans_le hst]
  simp only [neg_mul, neg_div]
  exact neg_le_neg (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hs) hsq)

end ProbabilityTheory

namespace ZLattice

/-- A lattice Gaussian mass increases with its positive width. -/
theorem gaussianMass_le_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (c : E) : gaussianMass L s c ≤ gaussianMass L t c :=
  Summable.tsum_le_tsum (fun z : L ↦ gaussianWeight_le_of_le hs hst ((z : E) - c))
    (summable_gaussianWeight L s hs c) (summable_gaussianWeight L t (hs.trans_le hst) c)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private theorem gaussianMass_zero_poisson (s : ℝ) (hs : 0 < s) :
    gaussianMass L s 0 = s ^ finrank ℝ E / covolume L *
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 := by
  apply Complex.ofReal_injective
  simpa only [inner_zero_left, neg_zero, Real.fourierChar.map_zero_eq_one, Circle.coe_one,
    one_mul, mul_one, gaussianMass,
    sub_zero, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_tsum] using gaussianMass_eq_tsum_dual L s hs 0

/-- The centered Gaussian mass ratio is bounded uniformly over full-rank lattices.
The width may remain unchanged, and dimension zero is included. -/
theorem gaussianMass_zero_div_le (s : ℝ) (hs : 0 < s) (t : ℝ) (hst : s ≤ t) :
    gaussianMass L t 0 / gaussianMass L s 0 ≤ (t / s) ^ finrank ℝ E := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  have ht : 0 < t := hs.trans_le hst
  have hm : gaussianMass D (1 / t) 0 ≤ gaussianMass D (1 / s) 0 :=
    gaussianMass_le_of_le D (one_div_pos.mpr ht) (one_div_le_one_div_of_le hs hst) 0
  apply (div_le_iff₀ (gaussianMass_pos L s hs 0)).mpr
  rw [gaussianMass_zero_poisson L s hs, gaussianMass_zero_poisson L t ht]
  change t ^ finrank ℝ E / covolume L * gaussianMass D (1 / t) 0 ≤
    (t / s) ^ finrank ℝ E * (s ^ finrank ℝ E / covolume L * gaussianMass D (1 / s) 0)
  calc
    _ ≤ t ^ finrank ℝ E / covolume L * gaussianMass D (1 / s) 0 :=
      mul_le_mul_of_nonneg_left hm
        (div_nonneg (pow_nonneg ht.le _) (covolume_pos L volume).le)
    _ = (t / s) ^ finrank ℝ E *
        (s ^ finrank ℝ E / covolume L * gaussianMass D (1 / s) 0) := by
      rw [div_pow]
      field_simp

end ZLattice
