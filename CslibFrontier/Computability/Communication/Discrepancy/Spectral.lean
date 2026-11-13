/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Discrepancy
public import CslibFrontier.Computability.Communication.Rank
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
import CslibFrontier.Probability.PMF

/-!
# Spectral bounds for uniform communication discrepancy

The uniform discrepancy of a Boolean matrix on finite nonempty rectangular input sets is at
most its sign matrix's Euclidean operator norm divided by `sqrt (|X| * |Y|)`.
The matrix estimate is `Matrix.abs_sum_sum_le_l2_opNorm`; it also applies to empty rectangles
and empty index types without a probability distribution.

This is the corrected operator-norm version of [AroraBarak07, Lemma 12.13], rather than its
literal eigenvalue claim for arbitrary matrices. A nonsymmetric nilpotent matrix can have a
nonzero rectangle sum. The library sign matrix is the negative of the draft's `2 M(f) - 1`,
which preserves its norm and absolute rectangle sums. No symmetry assumption is needed here.

## Main results

* `Cslib.Communication.discrepancy_uniformOfFintype_le_l2_opNorm`: the spectral discrepancy bound.
* `Cslib.Communication.discrepancy_bitString_le_l2_opNorm`: the `2^n` denominator on bit cubes.
* `Cslib.Communication.discrepancy_uniformOfFintype_mul_sqrt_card_le_l2_opNorm`: its
  division-free form.
-/

public section

namespace Cslib.Communication

open Finset BitString Probability
open scoped Matrix.Norms.L2Operator

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [Nonempty Y]

/-- Uniform discrepancy is bounded by the sign matrix's spectral norm divided by the square
root of the input-domain size. This uses the Euclidean operator norm, not eigenvalue magnitude. -/
theorem discrepancy_uniformOfFintype_le_l2_opNorm (f : X → Y → Bool) :
    discrepancy (PMF.uniformOfFintype (X × Y)) f ≤
      ‖signMatrix ℝ f‖ / √((Fintype.card X : ℝ) * Fintype.card Y) := by
  obtain ⟨A, B, hAB⟩ := exists_abs_sum_eq_discrepancy (PMF.uniformOfFintype (X × Y)) f
  let N : ℝ := (Fintype.card X : ℝ) * Fintype.card Y
  have hN : 0 < N := by
    dsimp [N]
    exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  have hs : 0 < √N := Real.sqrt_pos.mpr hN
  have hmass (x : X) (y : Y) :
      ((PMF.uniformOfFintype (X × Y)) (x, y)).toReal = N⁻¹ := by
    simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Fintype.card_prod, N]
  have hscale : discrepancy (PMF.uniformOfFintype (X × Y)) f * N =
      |∑ x ∈ A, ∑ y ∈ B, signVal (f x y)| := by
    rw [← hAB]
    simp only [hmass, ← mul_sum, abs_mul, abs_inv, abs_of_pos hN]
    field_simp
  have hrect : |∑ x ∈ A, ∑ y ∈ B, signVal (f x y)| ≤
      ‖signMatrix ℝ f‖ * √N := by
    have hA : (#A : ℝ) ≤ Fintype.card X := by exact_mod_cast card_le_univ A
    have hB : (#B : ℝ) ≤ Fintype.card Y := by exact_mod_cast card_le_univ B
    calc _ ≤ ‖signMatrix ℝ f‖ * √(#A : ℝ) * √(#B : ℝ) := by
          simpa only [signMatrix_apply_eq_signVal] using
            Matrix.abs_sum_sum_le_l2_opNorm (signMatrix ℝ f) A B
      _ ≤ ‖signMatrix ℝ f‖ * √(Fintype.card X) * √(Fintype.card Y) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA) (norm_nonneg _))
          (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _) (by positivity)
      _ = ‖signMatrix ℝ f‖ * √N := by
        rw [mul_assoc, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply (le_div_iff₀ hs).mpr
  apply (mul_le_mul_iff_right₀ hs).mp
  calc √N * (discrepancy (PMF.uniformOfFintype (X × Y)) f * √N)
      = discrepancy (PMF.uniformOfFintype (X × Y)) f * N := by
        rw [mul_left_comm, Real.mul_self_sqrt hN.le]
    _ ≤ ‖signMatrix ℝ f‖ * √N := hscale.trans_le hrect
    _ = √N * ‖signMatrix ℝ f‖ := mul_comm _ _

/-- Division-free spectral discrepancy bound on finite nonempty input domains. -/
theorem discrepancy_uniformOfFintype_mul_sqrt_card_le_l2_opNorm (f : X → Y → Bool) :
    discrepancy (PMF.uniformOfFintype (X × Y)) f *
      √((Fintype.card X : ℝ) * Fintype.card Y) ≤ ‖signMatrix ℝ f‖ :=
  (le_div_iff₀ (Real.sqrt_pos.mpr
    (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)))).mp
      (discrepancy_uniformOfFintype_le_l2_opNorm f)

/-- On equal `n`-bit cubes the square root of the input-domain size is exactly `2^n`. -/
theorem discrepancy_bitString_le_l2_opNorm {n : ℕ} (f : BitString n → BitString n → Bool) :
    discrepancy (PMF.uniformOfFintype (BitString n × BitString n)) f ≤
      ‖signMatrix ℝ f‖ / 2 ^ n := by
  have h := discrepancy_uniformOfFintype_le_l2_opNorm f
  have hcard : (Fintype.card (BitString n) : ℝ) = 2 ^ n := by simp
  rw [hcard, ← sq, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)] at h
  exact h

end Cslib.Communication
