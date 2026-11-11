/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Algebra.Module.ZLattice.CoefficientFiber
public import Complexity.Foundations.Probability.Gaussian.Discrete

import Complexity.Probability.PMF.Map

/-!
# Discrete Gaussian coefficient fibers

Conditioning an actual lattice discrete Gaussian on a vector of basis coefficients modulo a
positive integer gives the actual Gaussian on the corresponding coset. Residue probabilities
are ratios of convergent Gaussian masses and need not be uniform.

## Main results

* `ZLattice.map_coefficientMod_discreteGaussian_apply`: the exact residue probability.
* `ZLattice.filter_coefficientMod_discreteGaussian`: the actual conditional coset law.
* `ZLattice.map_coefficientMod_pair_discreteGaussian`: reconstruction of the tagged joint law.

## References

[Regev2009], Lemma 3.11 and equation (12), printed pages 23–24 of the May 2, 2009 author version.
The source uses center zero; the arbitrary-center version here is an original generalization.
These identities do not assert residue uniformity or provide a sampling algorithm.
-/

public section

noncomputable section

open ProbabilityTheory
open scoped ENNReal Pointwise

namespace ZLattice

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Fintype ι]
variable (L : Submodule ℤ E) [DiscreteTopology L]
variable (b : Module.Basis ι ℤ L) (p : ℕ) [NeZero p]

local instance : DiscreteTopology ↥((p : ℝ) • L) :=
  DiscreteTopology.of_subset inferInstance (natCast_smul_le L p)

/-- The probability of a coefficient residue is the mass of its coset divided by the total
mass. The coset is represented by `coefficientLift`, with center shifted by subtraction. -/
theorem map_coefficientMod_discreteGaussian_apply (r : ℝ) (hr : 0 < r) (c : E)
    (a : ι → ZMod p) :
    (discreteGaussian L r hr c).map (coefficientMod L b p) a =
      ENNReal.ofReal (gaussianMass ((p : ℝ) • L) r (c - coefficientLift L b p a)) /
        ENNReal.ofReal (gaussianMass L r c) := by
  classical
  have hfiber : (discreteGaussian L r hr c).map (coefficientMod L b p) a =
      ∑' v : {v : L // coefficientMod L b p v = a}, discreteGaussian L r hr c v.val := by
    rw [PMF.map_apply]
    calc
      _ = ∑' v, {v : L | coefficientMod L b p v = a}.indicator
          (fun v ↦ discreteGaussian L r hr c v) v := by
        apply tsum_congr
        intro v
        by_cases hv : coefficientMod L b p v = a
        · rw [ite_eq_left hv.symm, Set.indicator_of_mem hv]
        · rw [ite_eq_right (Ne.symm hv), Set.indicator_of_notMem hv]
      _ = _ := (tsum_subtype {v : L | coefficientMod L b p v = a}
        (fun v ↦ discreteGaussian L r hr c v)).symm
  rw [hfiber, ← (coefficientFiberEquiv L b p a).tsum_eq]
  simp only [discreteGaussian_apply, coe_coefficientFiberEquiv]
  have hsub (w : ↥((p : ℝ) • L)) :
      (w : E) + coefficientLift L b p a - c =
        (w : E) - (c - coefficientLift L b p a) := by abel
  simp only [hsub, div_eq_mul_inv, ENNReal.tsum_mul_right]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun w : ↥((p : ℝ) • L) ↦ (gaussianWeight_pos r _).le)
    (summable_gaussianWeight ((p : ℝ) • L) r hr (c - coefficientLift L b p a))]
  rfl

/-- Every coefficient residue has positive probability under the actual discrete Gaussian. -/
theorem map_coefficientMod_discreteGaussian_pos (r : ℝ) (hr : 0 < r) (c : E)
    (a : ι → ZMod p) :
    0 < (discreteGaussian L r hr c).map (coefficientMod L b p) a := by
  rw [PMF.apply_pos_iff, PMF.mem_support_map_iff]
  exact ⟨coefficientLift L b p a, by simp, coefficientMod_coefficientLift L b p a⟩

/-- Filtering on a coefficient residue gives the translated discrete Gaussian on the actual
scalar lattice. The positive event required by `PMF.filter` is proved from the chosen lift. -/
theorem filter_coefficientMod_discreteGaussian (r : ℝ) (hr : 0 < r) (c : E)
    (a : ι → ZMod p) :
    (discreteGaussian L r hr c).filter {v | coefficientMod L b p v = a}
        ⟨coefficientLift L b p a, coefficientMod_coefficientLift L b p a, by simp⟩ =
      (discreteGaussian ((p : ℝ) • L) r hr (c - coefficientLift L b p a)).map
        (fun w ↦ Submodule.inclusion (natCast_smul_le L p) w + coefficientLift L b p a) := by
  classical
  let f : ↥((p : ℝ) • L) → L :=
    fun w ↦ Submodule.inclusion (natCast_smul_le L p) w + coefficientLift L b p a
  have hfi : Function.Injective f := by
    intro w z h
    apply Subtype.ext
    exact add_right_cancel (congrArg (fun v : L ↦ (v : E)) h)
  have hm : (∑' v, {v : L | coefficientMod L b p v = a}.indicator
      (fun v ↦ discreteGaussian L r hr c v) v) =
      (discreteGaussian L r hr c).map (coefficientMod L b p) a := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro v
    by_cases hv : coefficientMod L b p v = a
    · rw [Set.indicator_of_mem hv, ite_eq_left hv.symm]
    · rw [Set.indicator_of_notMem hv, ite_eq_right (Ne.symm hv)]
  ext v
  by_cases hv : coefficientMod L b p v = a
  · let w := (coefficientFiberEquiv L b p a).symm ⟨v, hv⟩
    have hw : f w = v := congrArg Subtype.val
      ((coefficientFiberEquiv L b p a).apply_symm_apply ⟨v, hv⟩)
    change _ = (discreteGaussian ((p : ℝ) • L) r hr
      (c - coefficientLift L b p a)).map f v
    rw [← hw, PMF.map_apply]
    simp only [hfi.eq_iff, tsum_ite_eq']
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [PMF.filter_apply, hm,
      Set.indicator_of_mem (show f w ∈ {v | coefficientMod L b p v = a} from hw ▸ hv),
      ENNReal.toReal_mul, ENNReal.toReal_inv, discreteGaussian_apply_toReal,
      map_coefficientMod_discreteGaussian_apply, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (gaussianMass_pos _ r hr _).le,
      ENNReal.toReal_ofReal (gaussianMass_pos _ r hr _).le,
      discreteGaussian_apply_toReal]
    have hsub : ((f w : L) : E) - c = (w : E) - (c - coefficientLift L b p a) := by
      change (w : E) + coefficientLift L b p a - c = _
      abel
    rw [hsub]
    field_simp [ne_of_gt (gaussianMass_pos L r hr c)]
  · rw [PMF.filter_apply_eq_zero_of_notMem _ hv]
    change 0 = (discreteGaussian ((p : ℝ) • L) r hr
      (c - coefficientLift L b p a)).map f v
    rw [PMF.map_apply]
    symm
    have hz (w : ↥((p : ℝ) • L)) : v ≠ f w := by
      intro he
      apply hv
      rw [he]
      exact (coefficientFiberEquiv L b p a w).property
    simp [hz]

/-- The tagged joint sample is recovered by first sampling its actual residue marginal and
then sampling the corresponding coset Gaussian. The marginal is not replaced by uniform noise. -/
theorem map_coefficientMod_pair_discreteGaussian (r : ℝ) (hr : 0 < r) (c : E) :
    (discreteGaussian L r hr c).map (fun v ↦ (coefficientMod L b p v, v)) =
      ((discreteGaussian L r hr c).map (coefficientMod L b p)).bind (fun a ↦
        (discreteGaussian ((p : ℝ) • L) r hr (c - coefficientLift L b p a)).map
          (fun w ↦ (a, Submodule.inclusion (natCast_smul_le L p) w +
            coefficientLift L b p a))) := by
  classical
  let q := discreteGaussian L r hr c
  let k (a : ι → ZMod p) := q.filter {v | coefficientMod L b p v = a}
    ⟨coefficientLift L b p a, coefficientMod_coefficientLift L b p a, by simp [q]⟩
  have hk (a : ι → ZMod p) :
      (k a).map (a, ·) =
        (discreteGaussian ((p : ℝ) • L) r hr (c - coefficientLift L b p a)).map
          (fun w ↦ (a, Submodule.inclusion (natCast_smul_le L p) w +
            coefficientLift L b p a)) := by
    rw [show k a = _ from filter_coefficientMod_discreteGaussian L b p r hr c a,
      PMF.map_comp]
    rfl
  simp_rw [← hk]
  ext ⟨a, v⟩
  rw [Cslib.Probability.PMF.bind_map_prodMk_apply]
  have hm : (∑' v, {v : L | coefficientMod L b p v = a}.indicator (fun v ↦ q v) v) =
      q.map (coefficientMod L b p) a := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro v
    by_cases hv : coefficientMod L b p v = a
    · rw [Set.indicator_of_mem hv, ite_eq_left hv.symm]
    · rw [Set.indicator_of_notMem hv, ite_eq_right (Ne.symm hv)]
  change q.map (fun v ↦ (coefficientMod L b p v, v)) (a, v) = _
  have hj : q.map (fun v ↦ (coefficientMod L b p v, v)) (a, v) =
      if a = coefficientMod L b p v then q v else 0 := by
    simp only [PMF.map_apply, Prod.mk.injEq, and_comm, ite_and, tsum_ite_eq']
  rw [hj, show k a v = _ from PMF.filter_apply _ v, hm]
  by_cases hv : coefficientMod L b p v = a
  · rw [ite_eq_left hv.symm, Set.indicator_of_mem hv]
    have hpos := (map_coefficientMod_discreteGaussian_pos L b p r hr c a).ne'
    have hfinite := (q.map (coefficientMod L b p)).apply_ne_top a
    change q v = q.map (coefficientMod L b p) a *
      (q v * (q.map (coefficientMod L b p) a)⁻¹)
    rw [mul_left_comm, ENNReal.mul_inv_cancel hpos hfinite, mul_one]
  · rw [ite_eq_right (Ne.symm hv), Set.indicator_of_notMem hv]
    simp

end ZLattice
