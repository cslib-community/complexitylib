/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric.ClippedMean
public import Complexity.Foundations.Probability.TrueSampleMeans

/-!
# Bounded means under a change of usage slice

A supported table has an exact density-ratio mean under a larger terminal event.
Bounded root-to-ordinary conversion on its own usage slice, then exact terminal
transport and Jensen, retains the cube of that ratio. No independence of the
table and the masks is assumed. These are original finite consequences of the
slice and bounded-conversion APIs.
-/

public section
noncomputable section
open Finset
open scoped BigOperators
namespace Cslib

/-- Restrict a supported table to its own usage slice, with the exact density ratio.
The error table may depend on every coordinate of the conditioning environment. -/
theorem rowSliceMean_eq_density_mul_of_subset
    {Ω V : Type*} [Fintype Ω] {q : ℝ} (hq : q ≠ 0)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (F : Ω → V → V → ℝ)
    (hsub : ∀ σ y, U σ y → Y σ y)
    (hoff : ∀ σ x y, ¬ U σ y → F σ x y = 0)
    (hne : ∀ x y, ({σ | X σ x ∧ U σ y} : Finset Ω).Nonempty)
    (hratio : ∀ x y,
      (({σ | X σ x ∧ Y σ y} : Finset Ω).dens : ℝ) /
        (({σ | X σ x ∧ U σ y} : Finset Ω).dens : ℝ) = q⁻¹) :
    ∀ x y, rowSliceMean X Y F x y = q * rowSliceMean X U F x y := by
  classical
  intro x y
  let S : Finset Ω := {σ | X σ x ∧ Y σ y}
  let T : Finset Ω := {σ | X σ x ∧ U σ y}
  have hh := expect_mul_dens_div_of_subset (S := S) (T := T)
    (by intro σ hσ; simp only [S, T, mem_filter, mem_univ, true_and] at hσ ⊢
        exact ⟨hσ.1, hsub σ y hσ.2⟩) (hne x y) (fun σ => F σ x y)
    (by intro σ hσ hn
        have hy : ¬ U σ y := by
          simp only [S, mem_filter, mem_univ, true_and] at hσ
          simpa only [T, mem_filter, mem_univ, true_and, hσ.1, true_and] using hn
        exact hoff σ x y hy)
  rw [← mul_expect, hratio x y] at hh
  change (𝔼 σ ∈ S, F σ x y) = q * (𝔼 σ ∈ T, F σ x y)
  rw [← hh, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

/-- Bounded root-to-ordinary conversion on the usage slice, followed by exact
terminal transport and Jensen. The density occurs cubically before importance
scaling. This is an ordinary moment estimate, before any relative clipping. -/
theorem rowNormPow_bounded_sliceMean_fourth_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u q cap : ℝ}
    (hNu : 0 ≤ N * u) (hq : 0 ≤ q) (hcap : 0 ≤ cap)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (A C : Ω → V → V → ℝ)
    (hA : ∀ σ x y, X σ x → U σ y → A σ x y ∈ Set.Icc 0 cap)
    (hC : ∀ σ x y, X σ x → U σ y → C σ x y ∈ Set.Icc 0 cap)
    (hmean : ∀ x y, rowSliceMean X Y (A - C) x y =
      q * rowSliceMean X U (A - C) x y)
    (hdens : ∀ x y,
      (({σ | X σ x ∧ Y σ y} : Finset Ω).dens : ℝ) * q =
        (({σ | X σ x ∧ U σ y} : Finset Ω).dens : ℝ)) :
    rowNormPow 4 N u X Y (fun _ => rowSliceMean X Y (A - C)) ≤
      q ^ 3 * (256 * cap ^ 3) * rootDistPow 4 N u X U A C := by
  have hrange := rowNormPow_sub_le_rootDistPow (s := 4) (by decide) hNu hA hC
  change rowNormPow 4 N u X U (A - C) ≤ _ at hrange
  norm_num only [Nat.cast_ofNat, show ((4 : ℝ) - 1) / 4 = 3 / 4 by norm_num] at hrange
  have hroot : (cap ^ ((3 : ℝ) / 4)) ^ 4 = cap ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hcap]
    norm_num
  have hfactor : (4 * cap ^ ((3 : ℝ) / 4)) ^ 4 = 256 * cap ^ 3 := by
    rw [mul_pow, hroot]
    norm_num
  rw [hfactor] at hrange
  have hj := rowNormPow_sliceMean_change_terminal_fourth_le hNu hq X Y U (A - C) hmean hdens
  exact hj.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hrange (pow_nonneg hq 3))

end Cslib
