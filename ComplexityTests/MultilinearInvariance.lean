/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.Invariance

/-! # The Basic Invariance Principle on small examples

Standard Gaussians and uniform random signs satisfy Hypothesis 11.65 of O'Donnell's *Analysis of
Boolean Functions*, and a point mass at `0` does not (its second moment is `0`). The fourth
derivative of `cos` is `cos`, so the Basic Invariance Principle compares `E[cos f(x)]` at uniform
bits with `E[cos F(g)]` at standard Gaussians for any function `f` on two bits; the third
derivative of `sin` is `-cos`, which instantiates the `C³` form. A polynomial of degree `0` is
constant, so both sides agree exactly, and the bound `C / 12 · 9 ^ 0 · ∑ Inf ^ 2 = 0` is tight.
-/

namespace ComplexityTests.MultilinearInvariance

open MeasureTheory ProbabilityTheory Cslib Cslib.BitString Finset
open scoped BigOperators

/-! ### Hypothesis 11.65 -/

example : HasInvarianceMoments (gaussianReal 0 1) := hasInvarianceMoments_gaussianReal

example : HasInvarianceMoments rademacher := hasInvarianceMoments_rademacher

/-- A point mass at `0` has second moment `0`, so it fails Hypothesis 11.65. -/
example : ¬ HasInvarianceMoments (Measure.dirac (0 : ℝ)) := fun h => by
  have := h.integral_sq
  simp at this

/-- A uniform random sign has fourth moment `1`. -/
example : ∫ s, s ^ 4 ∂rademacher = 1 := by
  rw [integral_rademacher]; norm_num

/-- A standard Gaussian has fourth moment `3`. -/
example : ∫ s, s ^ 4 ∂gaussianReal 0 1 = 3 := integral_pow_four_gaussianReal

/-! ### Test functions -/

theorem iteratedDeriv_four_cos : iteratedDeriv 4 Real.cos = Real.cos := by
  simp [show 4 = 2 * 2 from rfl]

theorem iteratedDeriv_three_sin : iteratedDeriv 3 Real.sin = fun x => -Real.cos x := by
  rw [show 3 = 2 * 1 + 1 from rfl, Real.iteratedDeriv_odd_sin]
  funext x; simp

/-! ### Bits versus Gaussians -/

/-- **Bits versus Gaussians, `C⁴` form**: for any function `f` of two bits, `E[cos f(x)]` at
uniform bits and `E[cos F(g)]` at independent standard Gaussians differ by at most
`1 / 12 · 9 ^ 2 · ∑ Inf_i[f] ^ 2`. -/
example (f : (Fin 2 → Bool) → ℝ) :
    |𝔼 x, Real.cos (f x) -
        ∫ y, Real.cos (multilinearEval (fourierCoeff f) y) ∂Measure.pi fun _ => gaussianReal 0 1| ≤
      1 / 12 * 9 ^ 2 * ∑ i, influence i f ^ 2 :=
  abs_expect_comp_sub_integral_comp_multilinearEval_le _
    (fun _ => hasInvarianceMoments_gaussianReal)
    ((totalDegree_le_card f).trans_eq (Fintype.card_fin 2)) Real.contDiff_cos
    (fun y => by rw [iteratedDeriv_four_cos]; exact Real.abs_cos_le_one y)

/-- **Bits versus Gaussians, `C³` form**, with `ψ = sin`. -/
example (f : (Fin 2 → Bool) → ℝ) :
    |𝔼 x, Real.sin (f x) -
        ∫ y, Real.sin (multilinearEval (fourierCoeff f) y) ∂Measure.pi fun _ => gaussianReal 0 1| ≤
      1 / 3 * 3 ^ 2 * ∑ i, influence i f ^ ((3 : ℝ) / 2) :=
  abs_expect_comp_sub_integral_comp_multilinearEval_le_of_contDiff_three _
    (fun _ => hasInvarianceMoments_gaussianReal)
    ((totalDegree_le_card f).trans_eq (Fintype.card_fin 2)) Real.contDiff_sin
    (fun y => by rw [iteratedDeriv_three_sin, abs_neg]; exact Real.abs_cos_le_one y)

/-- A polynomial of degree `0` has no influential coordinates, so the Basic Invariance Principle
says the two expectations are equal. -/
example (c : Finset (Fin 3) → ℝ) (hc : ∀ S, 0 < #S → c S = 0) :
    ∫ z, Real.cos (multilinearEval c z) ∂Measure.pi (fun _ => rademacher) =
      ∫ z, Real.cos (multilinearEval c z) ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have h := abs_integral_comp_multilinearEval_sub_le (fun _ => rademacher)
    (fun _ => gaussianReal 0 1) (fun _ => hasInvarianceMoments_rademacher)
    (fun _ => hasInvarianceMoments_gaussianReal) hc Real.contDiff_cos
    (fun y => by rw [iteratedDeriv_four_cos]; exact Real.abs_cos_le_one y)
  have hI (t : Fin 3) : multilinearInfluence c t = 0 := by
    rw [multilinearInfluence_def]
    exact sum_eq_zero fun S hS => by
      rw [hc S (card_pos.2 ⟨t, (mem_filter.1 hS).2⟩)]; norm_num
  simp only [hI] at h
  norm_num at h
  exact sub_eq_zero.1 h

end ComplexityTests.MultilinearInvariance
