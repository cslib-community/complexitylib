/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Freivalds
public import CslibFrontier.Probability.LinearCombination
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Probability.PMF.Event

/-!
# Bilinear fingerprints over finite fields

For independent uniform vectors, a nonzero rectangular matrix has nonzero bilinear
fingerprint with probability at least `(1 - 1 / |F|)^2`.
This is Exercise 9.22 of [Goldreich2007DraftR5], printed page 452 (PDF page 70).
The source states the prime-field case. We allow every finite field and arbitrary finite
row and column types. No running-time or matrix-rank formula is asserted.

## Main results

* `toOuterMeasure_bilinear_ne_zero_eq`: exact factorization through the event `M *ᵥ s ≠ 0`.
* `toOuterMeasure_bilinear_ne_zero_ge`: the two-vector lower bound.
* `toOuterMeasure_bilinear_zmod_ne_zero_ge`: the prime-field specialization.
* `toOuterMeasure_bilinear_vecMulVec`: equality for nonzero outer products.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2007DraftR5],
  March 2007 draft, Exercise 9.22
-/

public section

namespace Cslib.Probability

open scoped Matrix ENNReal

variable {m n F : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Field F] [Fintype F]

private theorem uniform_linearComb_ne_zero {d : m → F} (hd : d ≠ 0) :
    (PMF.uniformOfFintype (m → F)).toOuterMeasure {r | ∑ i, r i * d i ≠ 0} =
      1 - (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := Function.ne_iff.mp hd
  have h := PMF.toOuterMeasure_add_compl_ennreal (PMF.uniformOfFintype (m → F))
    {r | ∑ i, r i * d i = 0}
  rw [toOuterMeasure_uniform_linearComb_eq_zero hi, one_div] at h
  have h' : 1 = (PMF.uniformOfFintype (m → F)).toOuterMeasure
      {r | ∑ i, r i * d i ≠ 0} + (Fintype.card F : ℝ≥0∞)⁻¹ := by
    simpa only [Set.compl_ofPred, add_comm] using h.symm
  exact (ENNReal.sub_eq_of_eq_add (by simp) h').symm

/-- Exact success probability, with independent uniform sampling represented by the uniform
law on the product of the column-vector and row-vector spaces. -/
theorem toOuterMeasure_bilinear_ne_zero_eq (M : Matrix m n F) :
    (PMF.uniformOfFintype ((n → F) × (m → F))).toOuterMeasure
        {p | ∑ i, p.2 i * (M *ᵥ p.1) i ≠ 0} =
      (1 - (Fintype.card F : ℝ≥0∞)⁻¹) *
        (PMF.uniformOfFintype (n → F)).toOuterMeasure {s | M *ᵥ s ≠ 0} := by
  classical
  change (PMF.uniformOfFintype ((n → F) × (m → F))).toOuterMeasure
    ((fun p : (n → F) × (m → F) => ∑ i, p.2 i * (M *ᵥ p.1) i) ⁻¹' {x | x ≠ 0}) = _
  rw [← PMF.toOuterMeasure_map_apply (f := fun p : (n → F) × (m → F) =>
    ∑ i, p.2 i * (M *ᵥ p.1) i)]
  rw [← PMF.uniformOfFintype_bind_map (fun (s : n → F) (r : m → F) =>
      ∑ i, r i * (M *ᵥ s) i), PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro s
  rw [PMF.toOuterMeasure_map_apply]
  change (PMF.uniformOfFintype (n → F)) s *
    (PMF.uniformOfFintype (m → F)).toOuterMeasure {r | ∑ i, r i * (M *ᵥ s) i ≠ 0} = _
  by_cases hs : M *ᵥ s = 0
  · simp [hs]
  · rw [uniform_linearComb_ne_zero hs]
    simp [hs, mul_comm]

/-- A nonzero rectangular matrix is detected by two independent uniform vectors with
probability at least `(1 - 1 / |F|)^2`. -/
theorem toOuterMeasure_bilinear_ne_zero_ge {M : Matrix m n F} (hM : M ≠ 0) :
    (1 - (Fintype.card F : ℝ≥0∞)⁻¹) ^ 2 ≤
      (PMF.uniformOfFintype ((n → F) × (m → F))).toOuterMeasure
        {p | ∑ i, p.2 i * (M *ᵥ p.1) i ≠ 0} := by
  classical
  have hb := toOuterMeasure_mulVec_eq_le (S := F) (e := id)
    (fun d hd _ _ h => mul_left_cancel₀ hd h) hM
  simp only [Function.id_comp, Matrix.zero_mulVec] at hb
  have hc := PMF.toOuterMeasure_add_compl_ennreal (PMF.uniformOfFintype (n → F))
    {s | M *ᵥ s = 0}
  have hl : 1 - (Fintype.card F : ℝ≥0∞)⁻¹ ≤
      (PMF.uniformOfFintype (n → F)).toOuterMeasure {s | M *ᵥ s ≠ 0} := by
    apply tsub_le_iff_right.mpr
    calc
      1 = (PMF.uniformOfFintype (n → F)).toOuterMeasure {s | M *ᵥ s ≠ 0} +
          (PMF.uniformOfFintype (n → F)).toOuterMeasure {s | M *ᵥ s = 0} := by
            simpa only [Set.compl_ofPred, add_comm] using hc.symm
      _ ≤ _ := add_le_add_right hb _
  rw [toOuterMeasure_bilinear_ne_zero_eq, pow_two]
  exact mul_le_mul_right hl _

/-- The prime-field specialization stated in Goldreich's Exercise 9.22. -/
theorem toOuterMeasure_bilinear_zmod_ne_zero_ge (p : ℕ) [Fact p.Prime]
    {M : Matrix m n (ZMod p)} (hM : M ≠ 0) :
    (1 - (p : ℝ≥0∞)⁻¹) ^ 2 ≤
      (PMF.uniformOfFintype ((n → ZMod p) × (m → ZMod p))).toOuterMeasure
        {rs | ∑ i, rs.2 i * (M *ᵥ rs.1) i ≠ 0} := by
  simpa only [ZMod.card] using toOuterMeasure_bilinear_ne_zero_ge hM

/-- The lower bound is sharp for every outer product of two nonzero vectors, including
in characteristic two. This is a rank-one presentation, without a rank API hypothesis. -/
theorem toOuterMeasure_bilinear_vecMulVec {u : m → F} {v : n → F}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (PMF.uniformOfFintype ((n → F) × (m → F))).toOuterMeasure
        {p | ∑ i, p.2 i * (Matrix.vecMulVec u v *ᵥ p.1) i ≠ 0} =
      (1 - (Fintype.card F : ℝ≥0∞)⁻¹) ^ 2 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.mp hu
  have he : {s : n → F | Matrix.vecMulVec u v *ᵥ s ≠ 0} =
      {s | ∑ j, s j * v j ≠ 0} := by
    ext s
    have hz : Matrix.vecMulVec u v *ᵥ s = 0 ↔ ∑ j, s j * v j = 0 := by
      constructor
      · intro h
        have h' := congrFun h i
        simpa [Matrix.vecMulVec_mulVec, dotProduct, mul_comm, hi] using h'
      · intro h
        ext k
        change (∑ j, (u k * v j) * s j) = 0
        simp only [mul_assoc, ← Finset.mul_sum]
        rw [show (∑ j, v j * s j) = 0 by simpa only [mul_comm] using h, mul_zero]
    exact not_congr hz
  rw [toOuterMeasure_bilinear_ne_zero_eq, he, uniform_linearComb_ne_zero hv, pow_two]

end Cslib.Probability
