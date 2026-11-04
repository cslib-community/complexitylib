/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.RootMetric.AbsoluteError
public import Complexity.Foundations.Probability.RootMetric.FiniteError
import Mathlib.Analysis.MeanInequalities

/-!
# Importance-weighted errors on a child's own usage mask

Bounded normalized root errors pay ordinary errors after an endpoint weight and a change
of terminal mask. Zero extension preserves the child's actual source and usage slices.
The coefficient is a finite sum of fourth powers, with no environment-atom payment.
-/
public section
namespace Cslib
open Finset
open scoped BigOperators

/-- An endpoint weight and arbitrary parent terminal mask cost the sum of fourth powers
of the weights. Both normalized tables vanish outside the child's usage; no inclusion
between the parent terminal mask and child usage, or independence, is needed. -/
theorem rowNormPow_weighted_sub_le_rootDistPow {Ω V : Type*} [Fintype Ω] [Fintype V]
    {N u B : ℝ} (hNu : 0 ≤ N * u)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (A A' : Ω → V → V → ℝ) (w : V → ℝ)
    (hA : ∀ σ x y, A σ x y ∈ Set.Icc 0 B)
    (hA' : ∀ σ x y, A' σ x y ∈ Set.Icc 0 B)
    (hoff : ∀ σ x y, ¬ U σ y → A σ x y = A' σ x y) :
    rowNormPow 4 N u X Y (fun σ x y => w y * (A σ x y - A' σ x y)) ≤
      (∑ y, |w y| ^ 4) * (4 * B ^ ((3 : ℝ) / 4)) ^ 4 *
        rootDistPow 4 N u X U A A' := by
  classical
  let E := fun σ x y => A σ x y - A' σ x y
  have he : (fun σ x y => if U σ y then E σ x y else 0) = E := by
    funext σ x y
    split_ifs with h
    · rfl
    · exact (sub_eq_zero.mpr (hoff σ x y h)).symm
  have hw (y : V) : |w y| ^ 4 ≤ ∑ z, |w z| ^ 4 :=
    single_le_sum (f := fun z => |w z| ^ 4) (fun _ _ => by positivity) (mem_univ y)
  have hmul : rowNormPow 4 N u X (fun _ _ => True) (fun σ x y => w y * E σ x y) ≤
      (∑ y, |w y| ^ 4) * rowNormPow 4 N u X (fun _ _ => True) E := by
    apply rowNormPow_le_mul hNu
    intro σ x y _ _
    rw [abs_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (hw y) (by positivity)
  have hmask : rowNormPow 4 N u X (fun _ _ => True) E = rowNormPow 4 N u X U E := by
    have hm := rowNormPow_usage_mask (N := N) (u := u) (X := X)
      (Y := fun _ _ => True) (U := U) (fun _ _ _ => True.intro) E
    rw [he] at hm
    exact hm
  have hroot := rowNormPow_sub_le_rootDistPow (s := 4) (N := N) (u := u)
    (X := X) (Y := U) (C := B) (H := A) (H' := A') (by decide) hNu
    (fun σ x y _ _ => hA σ x y) (fun σ x y _ _ => hA' σ x y)
  norm_num only [Nat.cast_ofNat, show ((4 : ℝ) - 1) / 4 = 3 / 4 by norm_num] at hroot
  calc
    _ ≤ rowNormPow 4 N u X (fun _ _ => True) (fun σ x y => w y * E σ x y) :=
      rowNormPow_mono_terminal hNu (fun _ _ _ => True.intro) _
    _ ≤ (∑ y, |w y| ^ 4) * rowNormPow 4 N u X U E := by rw [← hmask]; exact hmul
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hroot (sum_nonneg fun _ _ => by positivity)
/-- A finite sum pays the sum of actual fourth moments with the cube of its cardinality.
This includes empty sums and correlated tables on the same environment. -/
theorem rowNormPow_sum_fourth_le {I Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : Finset I) {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (A : I → Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => ∑ i ∈ S, A i σ x y) ≤
      (#S : ℝ) ^ 3 * ∑ i ∈ S, rowNormPow 4 N u X Y (A i) := by
  have hp (σ : Ω) (x y : V) : |∑ i ∈ S, A i σ x y| ^ 4 ≤
      (#S : ℝ) ^ 3 * ∑ i ∈ S, |A i σ x y| ^ 4 := by
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sum_le_sum_abs _ _) 4).trans
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S
      (f := fun i => |A i σ x y|) (p := 4) (by norm_num) (fun _ _ => abs_nonneg _)
    norm_num only [show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_natCast,
      Real.rpow_ofNat] at h
    exact h
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ y ∈ ({y | Y σ y} : Finset V), (#S : ℝ) ^ 3 * ∑ i ∈ S, |A i σ x y| ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
      exact expect_le_expect fun σ _ => sum_le_sum fun x _ => sum_le_sum fun y _ => hp σ x y
    _ = _ := by
      simp_rw [← mul_sum, sum_comm (s := ({y | Y _ y} : Finset V)) (t := S),
        sum_comm (s := ({x | X _ x} : Finset V)) (t := S)]
      rw [← mul_expect, expect_sum_comm]
      ring

end Cslib
