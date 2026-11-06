/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.Gaussian.CoefficientFiber
public import Complexity.Foundations.Probability.Gaussian.ShiftBounds

import Complexity.Probability.PMF

/-!
# Near-uniform coefficient residues of a discrete Gaussian

## Main results

* `ZLattice.sum_abs_map_coefficientMod_discreteGaussian_sub_uniform_le`: an actual nonzero
  dual Gaussian mass bound controls the full-L1 error of the actual coefficient marginal.

## References

[Regev2009], Lemma 3.11, printed pages 23–24. The explicit error `2ε / (1 - ε)` is obtained
from the proved coefficient-fiber masses and Claim 3.8, without assuming residue uniformity.
-/

public section

noncomputable section

open ProbabilityTheory Module MeasureTheory
open scoped ENNReal Pointwise RealInnerProductSpace

namespace ZLattice

private theorem sum_abs_sub_uniform_le {A : Type*} [Fintype A] [Nonempty A]
    (q : PMF A) (k ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hq : ∀ a, k * (1 - ε) ≤ (q a).toReal ∧ (q a).toReal ≤ k * (1 + ε)) :
    ∑ a, |(q a).toReal - 1 / Fintype.card A| ≤ 2 * ε / (1 - ε) := by
  have hN : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  have hs := Cslib.Probability.PMF.sum_toReal q
  have hlo : (Fintype.card A : ℝ) * (k * (1 - ε)) ≤ 1 := by
    calc
      _ = ∑ a : A, k * (1 - ε) := by simp
      _ ≤ ∑ a, (q a).toReal := Finset.sum_le_sum fun a _ ↦ (hq a).1
      _ = 1 := hs
  have hhi : 1 ≤ (Fintype.card A : ℝ) * (k * (1 + ε)) := by
    calc
      1 = ∑ a, (q a).toReal := hs.symm
      _ ≤ ∑ a : A, k * (1 + ε) := Finset.sum_le_sum fun a _ ↦ (hq a).2
      _ = _ := by simp
  have hu : k * (1 - ε) ≤ 1 / Fintype.card A ∧
      1 / Fintype.card A ≤ k * (1 + ε) := by
    constructor
    · apply (le_div_iff₀ hN).mpr
      nlinarith [hlo]
    · apply (div_le_iff₀ hN).mpr
      nlinarith [hhi]
  have hpoint (a : A) : |(q a).toReal - 1 / Fintype.card A| ≤ 2 * k * ε := by
    rw [abs_le]
    constructor <;> nlinarith [(hq a).1, (hq a).2, hu.1, hu.2]
  calc
    _ ≤ ∑ a : A, 2 * k * ε := Finset.sum_le_sum fun a _ ↦ hpoint a
    _ = (Fintype.card A : ℝ) * (2 * k * ε) := by simp
    _ ≤ 2 * ε / (1 - ε) := by
      apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * ε by positivity)]

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (b : Module.Basis ι ℤ L) (p : ℕ) [NeZero p]

local instance : DiscreteTopology ↥((p : ℝ) • L) :=
  DiscreteTopology.of_subset inferInstance (natCast_smul_le L p)

local instance : IsZLattice ℝ ((p : ℝ) • L) where
  span_top := by
    rw [Submodule.coe_pointwise_smul, ← Submodule.smul_span, IsZLattice.span_top]
    ext x
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    rw [show x = (p : ℝ) • ((p : ℝ)⁻¹ • x) by simp [hp]]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (by trivial)

/-- The actual residue marginal is close to uniform under a bound on the actual nonzero dual
mass of the scalar lattice. The distance is the full sum of absolute probability differences. -/
theorem sum_abs_map_coefficientMod_discreteGaussian_sub_uniform_le
    (r : ℝ) (hr : 0 < r) (c : E) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E)
      ((p : ℝ) • L)) (1 / r) 0 - 1 ≤ ε) :
    ∑ a : ι → ZMod p,
      |((discreteGaussian L r hr c).map (coefficientMod L b p) a).toReal -
        1 / Fintype.card (ι → ZMod p)| ≤ 2 * ε / (1 - ε) := by
  let H := (p : ℝ) • L
  let k := (r ^ finrank ℝ E / covolume H) / gaussianMass L r c
  apply sum_abs_sub_uniform_le _ k ε hε hε1
  intro a
  rw [map_coefficientMod_discreteGaussian_apply, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (gaussianMass_pos _ r hr _).le,
    ENNReal.toReal_ofReal (gaussianMass_pos _ r hr _).le]
  have hm := gaussianMass_mem_Icc_of_dual_mass_le H r hr ε hdual
    (c - coefficientLift L b p a)
  constructor
  · simpa only [k, div_mul_eq_mul_div] using
      div_le_div_of_nonneg_right hm.1 (gaussianMass_pos L r hr c).le
  · simpa only [k, div_mul_eq_mul_div] using
      div_le_div_of_nonneg_right hm.2 (gaussianMass_pos L r hr c).le

end ZLattice
