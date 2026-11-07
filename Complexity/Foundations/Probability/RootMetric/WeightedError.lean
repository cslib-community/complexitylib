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
The coefficient is the fourth power of the finite-function sup norm, with no
cardinality or environment-atom payment. Fixed pair weights also have a sup-norm
payment on the unchanged source and terminal conditioning, used for target denominators.
-/
public section
namespace Cslib
open Finset
open scoped BigOperators

/-- An endpoint weight and arbitrary parent terminal mask cost the fourth power of the sup norm
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
      ‖w‖ ^ 4 * (4 * B ^ ((3 : ℝ) / 4)) ^ 4 *
        rootDistPow 4 N u X U A A' := by
  classical
  let E := fun σ x y => A σ x y - A' σ x y
  have he : (fun σ x y => if U σ y then E σ x y else 0) = E := by
    funext σ x y
    split_ifs with h
    · rfl
    · exact (sub_eq_zero.mpr (hoff σ x y h)).symm
  have hw (y : V) : |w y| ^ 4 ≤ ‖w‖ ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm w y) 4
  have hmul : rowNormPow 4 N u X (fun _ _ => True) (fun σ x y => w y * E σ x y) ≤
      ‖w‖ ^ 4 * rowNormPow 4 N u X (fun _ _ => True) E := by
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
    _ ≤ ‖w‖ ^ 4 * rowNormPow 4 N u X U E := by rw [← hmask]; exact hmul
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hroot (by positivity)
/-- Joint endpoint transport keeps a positive accuracy scale attached to the weight
before its sup norm. The original source normalization and the child's own usage mask
are retained; only the parent terminal mask is enlarged, using proved zero extension.
In particular this conversion introduces no inverse terminal density. -/
theorem rowNormPow_weighted_sub_precision_le {Ω V : Type*} [Fintype Ω] [Fintype V]
    {N u B ε C t : ℝ} (hNu : 0 ≤ N * u) (hε : 0 < ε) (ht : 0 ≤ t)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (A A' : Ω → V → V → ℝ) (w : V → ℝ)
    (hA : ∀ σ x y, A σ x y ∈ Set.Icc 0 B)
    (hA' : ∀ σ x y, A' σ x y ∈ Set.Icc 0 B)
    (hoff : ∀ σ x y, ¬ U σ y → A σ x y = A' σ x y)
    (hw : ∀ y, |w y| * ε ≤ t)
    (herr : rootDistPow 4 N u X U A A' ≤ C ^ 4 * ε ^ 4) :
    rowNormPow 4 N u X Y (fun σ x y => w y * (A σ x y - A' σ x y)) ≤
      ((4 * B ^ ((3 : ℝ) / 4)) * |C| * t) ^ 4 := by
  have hn : ‖w‖ ≤ t / ε := (pi_norm_le_iff_of_nonneg (div_nonneg ht hε.le)).mpr
    (fun y => by simpa only [Real.norm_eq_abs] using (le_div_iff₀ hε).mpr (hw y))
  have hnt : ‖w‖ * ε ≤ t := (le_div_iff₀ hε).mp hn
  have hb := (rowNormPow_weighted_sub_le_rootDistPow hNu X Y U A A' w
    hA hA' hoff).trans (mul_le_mul_of_nonneg_left herr (by positivity))
  have hp := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hε.le) hnt 4
  have hc := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (4 * B ^ ((3 : ℝ) / 4)) ^ 4 * C ^ 4 by positivity)
  rw [mul_pow] at hc
  rw [mul_pow, mul_pow, (by decide : Even (4 : ℕ)).pow_abs]
  nlinarith only [hb, hc]

/-- A fixed pair weight costs its finite sup norm. The weight is independent of the
sampled environment; source and terminal conditioning are unchanged. -/
theorem rowNormPow_mul_le_pi_norm {Ω V : Type*} [Fintype Ω] [Fintype V]
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (A : Ω → V → V → ℝ) (w : V × V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => A σ x y * w (x, y)) ≤
      ‖w‖ ^ 4 * rowNormPow 4 N u X Y A := by
  apply rowNormPow_le_mul hNu
  intro σ x y _ _
  rw [abs_mul, mul_pow]
  have hw : |w (x, y)| ^ 4 ≤ ‖w‖ ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm w (x, y)) 4
  exact (mul_le_mul_of_nonneg_left hw (by positivity)).trans_eq (mul_comm _ _)

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

/-- Mutually exclusive events pay a sum of moments, without a cardinality loss.
The events may depend on the same environment and vertex as the values. -/
theorem vertexNormPow_sum_ite {I Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : Finset I) (s : ℕ) (hs : s ≠ 0) (N u : ℝ)
    (X : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    (E : I → Ω → V → Prop) [∀ i σ x, Decidable (E i σ x)]
    (hE : ∀ σ x i j, E i σ x → E j σ x → i = j)
    (f : I → Ω → V → ℝ) :
    vertexNormPow s N u X (fun σ x => ∑ i ∈ S, if E i σ x then f i σ x else 0) =
      ∑ i ∈ S, vertexNormPow s N u X (fun σ x => if E i σ x then f i σ x else 0) := by
  classical
  have hpoint (σ : Ω) (x : V) :
      |∑ i ∈ S, if E i σ x then f i σ x else 0| ^ s =
        ∑ i ∈ S, |if E i σ x then f i σ x else 0| ^ s := by
    by_cases he : ∃ i ∈ S, E i σ x
    · obtain ⟨i, hi, hei⟩ := he
      have hz (j : I) (_hj : j ∈ S) (hne : j ≠ i) : ¬ E j σ x :=
        fun hej => hne (hE σ x j i hej hei)
      rw [sum_eq_single i (fun j hj hne => ite_eq_right (hz j hj hne))
        (fun h => (h hi).elim)]
      rw [sum_eq_single i (fun j hj hne => by
        rw [ite_eq_right (hz j hj hne), abs_zero, zero_pow hs]) (fun h => (h hi).elim)]
    · have hz (i : I) (hi : i ∈ S) : ¬ E i σ x := fun hei => he ⟨i, hi, hei⟩
      rw [sum_eq_zero (fun i hi => ite_eq_right (hz i hi)), abs_zero, zero_pow hs]
      exact (sum_eq_zero (fun i hi => by
        rw [ite_eq_right (hz i hi), abs_zero, zero_pow hs])).symm
  unfold vertexNormPow
  simp_rw [hpoint, sum_comm (s := ({x | X _ x} : Finset V)) (t := S)]
  rw [expect_sum_comm, mul_sum]

/-- Centering a perturbation preserves its conditional mean subtraction on the same
slice. Conditional Jensen pays the mean perturbation; no target or independence is used. -/
theorem rowNormPow_centered_sub_fourth_le {Ω V : Type*} [Fintype Ω] [Fintype V]
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (A C : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y =>
      (A σ x y - rowSliceMean X Y A x y) -
        (C σ x y - rowSliceMean X Y C x y)) ≤
      16 * rowNormPow 4 N u X Y (A - C) := by
  have hj := rowNormPow_sliceMean_fourth_le hNu X Y (A - C)
  have hb := rowNormPow_add_le (X := X) (Y := Y) hNu (A - C)
    (fun _ x y => -rowSliceMean X Y (A - C) x y)
  have he : (fun σ x y => A σ x y - C σ x y +
      -rowSliceMean X Y (A - C) x y) =
      (fun σ x y => (A σ x y - rowSliceMean X Y A x y) -
        (C σ x y - rowSliceMean X Y C x y)) := by
    funext σ x y
    simp only [rowSliceMean, Pi.sub_apply, expect_sub_distrib]
    ring
  change rowNormPow 4 N u X Y (fun σ x y => A σ x y - C σ x y +
    -rowSliceMean X Y (A - C) x y) ≤ _ at hb
  rw [he] at hb
  have hn : rowNormPow 4 N u X Y (fun _ x y => -rowSliceMean X Y (A - C) x y) =
      rowNormPow 4 N u X Y (fun _ => rowSliceMean X Y (A - C)) := by
    simp only [rowNormPow, abs_neg]
  rw [hn] at hb
  linarith


/-- The centered noise of an actual history is paid by its centered reference noise
and the uncentered history difference. The reference mean is preserved literally. -/
theorem rowNormPow_centered_fourth_le {Ω V : Type*} [Fintype Ω] [Fintype V]
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (A C : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => A σ x y - rowSliceMean X Y A x y) ≤
      8 * (16 * rowNormPow 4 N u X Y (A - C) +
        rowNormPow 4 N u X Y (fun σ x y => C σ x y - rowSliceMean X Y C x y)) := by
  have h := rowNormPow_add_le (X := X) (Y := Y) hNu
    (fun σ x y => (A σ x y - rowSliceMean X Y A x y) -
      (C σ x y - rowSliceMean X Y C x y))
    (fun σ x y => C σ x y - rowSliceMean X Y C x y)
  have he : (fun σ x y => (A σ x y - rowSliceMean X Y A x y) -
      (C σ x y - rowSliceMean X Y C x y) +
      (C σ x y - rowSliceMean X Y C x y)) =
      (fun σ x y => A σ x y - rowSliceMean X Y A x y) := by
    funext σ x y; ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add
    (rowNormPow_centered_sub_fourth_le hNu X Y A C) le_rfl) (by norm_num))

end Cslib
