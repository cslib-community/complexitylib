/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.RootMetric.ConditionalWalk
public import Complexity.Foundations.Probability.RootMetric.AbsoluteError

/-!
# Perturbation through retained-pair completion

Completion is linear and cannot increase the uncentered fourth moment on its actual
source and terminal slices. These finite comparisons include empty slices and do not
assume independence of the input errors.
-/
public section
namespace Cslib
open Finset
open scoped BigOperators
/-- Completing an input difference is exactly the difference of the two completions. -/
theorem conditionalWalk_sub {Ω V D : Type*} [Fintype Ω] [Fintype D]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D) (t : V → V → ℕ)
    (A C : Ω → V → V → ℝ) :
    conditionalWalk X Y G t (A - C) =
      conditionalWalk X Y G t A - conditionalWalk X Y G t C := by
  funext σ x y
  simp only [Pi.sub_apply]
  unfold conditionalWalk
  split_ifs with h
  · change ((G x y).walk ^ (2 * t x y))
      ((fun τ => A τ.val x y) - (fun τ => C τ.val x y)) _ = _
    rw [map_sub]
    rfl
  · simp

/-- Actual conditional completion does not increase an uncentered fourth moment.
The same source and terminal masks are retained, with no reciprocal atom penalty. -/
theorem rowNormPow_conditionalWalk_fourth_le {Ω V D : Type*}
    [Fintype Ω] [Fintype V] [Fintype D] [Nonempty D]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D) (t : V → V → ℕ)
    (A : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (conditionalWalk X Y G t A) ≤ rowNormPow 4 N u X Y A := by
  apply (rowNormPow_le_of_conditional_expect_le hNu A
    (conditionalWalk X Y G t A) 1 ?_).trans_eq (one_mul _)
  intro x y
  rw [one_mul, ← expect_retainedPairSlice X Y x y,
    ← expect_retainedPairSlice X Y x y]
  have habs (r : ℝ) : |r| ^ 4 = r ^ 4 := (by decide : Even (4 : ℕ)).pow_abs r
  simp only [habs, conditionalWalk_coe]
  exact (G x y).expect_walk_pow_pow_four_le (2 * t x y) (fun σ => A σ.val x y)

/-- The actual completed perturbation is paid entirely by the input perturbation. -/
theorem rowNormPow_conditionalWalk_sub_fourth_le {Ω V D : Type*}
    [Fintype Ω] [Fintype V] [Fintype D] [Nonempty D]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D) (t : V → V → ℕ)
    (A C : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (conditionalWalk X Y G t A - conditionalWalk X Y G t C) ≤
      rowNormPow 4 N u X Y (A - C) := by
  rw [← conditionalWalk_sub]
  exact rowNormPow_conditionalWalk_fourth_le X Y hNu G t (A - C)
/-- Correlated paired endpoint errors are paid before completion, with both endpoint
moments on the same masks. No equality of their statistical budgets is needed. -/
theorem rowNormPow_conditionalWalk_paired_fourth_le {Ω V D : Type*}
    [Fintype Ω] [Fintype V] [Fintype D] [Nonempty D]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D) (t : V → V → ℕ)
    (A C A₀ C₀ : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y
      (conditionalWalk X Y G t (A - C) - conditionalWalk X Y G t (A₀ - C₀)) ≤
      8 * (rowNormPow 4 N u X Y (A - A₀) + rowNormPow 4 N u X Y (C - C₀)) := by
  apply (rowNormPow_conditionalWalk_sub_fourth_le X Y hNu G t _ _).trans
  have he : (A - C) - (A₀ - C₀) =
      (fun σ x y => (A - A₀) σ x y + (-(C - C₀)) σ x y) := by
    funext σ x y
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [he]
  have h := rowNormPow_add_le (X := X) (Y := Y) hNu (A - A₀) (-(C - C₀))
  simpa only [rowNormPow, Pi.neg_apply, abs_neg] using h
end Cslib
