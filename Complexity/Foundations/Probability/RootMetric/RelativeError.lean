/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric.WeightedError
public import Complexity.Foundations.Probability.ProductError

/-!
# Pairwise range and denominator payments for ordinary errors

The range, importance weight and decoder denominator are compared together at
an endpoint pair before averaging. The rooted error remains on the child's own
source and usage masks. A local range may be substantially smaller than a global
cap where the denominator is small; neither factor is replaced by a separate norm.
These original inequalities do not supply that range comparison from scalar IH.

## Main results

* `Cslib.rowNormPow_relative_sub_le_rootDistPow`: coupled pairwise conversion.
* `Cslib.rowNormPow_relative_sub_precision_le`: joint precision comparison.
* `Cslib.rowNormPow_relative_product_sub_le_root`: local product range and reset source.
-/

public section
noncomputable section
namespace Cslib
open Finset
open scoped BigOperators

/-- A joint range/importance/denominator comparison pays an ordinary relative
fourth moment. Agreement outside own usage permits an arbitrary parent terminal
mask. No conditioning density, environment atom or independence is introduced. -/
theorem rowNormPow_relative_sub_le_rootDistPow
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u K : ℝ}
    (hNu : 0 ≤ N * u)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (A C : Ω → V → V → ℝ) (w : V → ℝ) (den cap : V → V → ℝ)
    (hA : ∀ σ x y, A σ x y ∈ Set.Icc 0 (cap x y))
    (hC : ∀ σ x y, C σ x y ∈ Set.Icc 0 (cap x y))
    (hoff : ∀ σ x y, ¬ U σ y → A σ x y = C σ x y)
    (hcoef : ∀ x y, |w y / den x y| * (4 * (cap x y) ^ ((3 : ℝ) / 4)) ≤ K) :
    rowNormPow 4 N u X Y (fun σ x y => w y * (A σ x y - C σ x y) / den x y) ≤
      K ^ 4 * rootDistPow 4 N u X U A C := by
  classical
  let E := fun σ x y => A σ x y ^ (4⁻¹ : ℝ) - C σ x y ^ (4⁻¹ : ℝ)
  have he : (fun σ x y => if U σ y then E σ x y else 0) = E := by
    funext σ x y
    split_ifs with h
    · rfl
    · simp only [E, hoff σ x y h, sub_self]
  have hmask : rowNormPow 4 N u X (fun _ _ => True) E = rowNormPow 4 N u X U E := by
    have hm := rowNormPow_usage_mask (N := N) (u := u) (X := X)
      (Y := fun _ _ => True) (U := U) (fun _ _ _ => True.intro) E
    rw [he] at hm
    exact hm
  calc
    _ ≤ rowNormPow 4 N u X (fun _ _ => True)
        (fun σ x y => w y * (A σ x y - C σ x y) / den x y) :=
      rowNormPow_mono_terminal hNu (fun _ _ _ => True.intro) _
    _ ≤ K ^ 4 * rowNormPow 4 N u X (fun _ _ => True) E := by
      apply rowNormPow_le_mul hNu
      intro σ x y _ _
      have hp := abs_sub_le_mul_abs_rpow_inv_sub (s := 4) (by decide)
        (hA σ x y).1 (hC σ x y).1 (hA σ x y).2 (hC σ x y).2
      norm_num only [Nat.cast_ofNat,
        show ((4 : ℝ) - 1) / 4 = 3 / 4 by norm_num] at hp
      have hh : |w y * (A σ x y - C σ x y) / den x y| ≤ K * |E σ x y| := by
        rw [mul_div_right_comm, abs_mul]
        apply (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans
        simpa only [mul_assoc, E, one_div] using
          mul_le_mul_of_nonneg_right (hcoef x y) (abs_nonneg (E σ x y))
      simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hh 4
    _ = _ := by rw [hmask]; rfl

/-- Precision stays in the same pairwise comparison as the range and denominator.
The scalar rooted IH is consumed only after this explicit comparison is proved. -/
theorem rowNormPow_relative_sub_precision_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u ε D t : ℝ}
    (hNu : 0 ≤ N * u) (hε : 0 < ε)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (A C : Ω → V → V → ℝ) (w : V → ℝ) (den cap : V → V → ℝ)
    (hA : ∀ σ x y, A σ x y ∈ Set.Icc 0 (cap x y))
    (hC : ∀ σ x y, C σ x y ∈ Set.Icc 0 (cap x y))
    (hoff : ∀ σ x y, ¬ U σ y → A σ x y = C σ x y)
    (hcoef : ∀ x y,
      |w y / den x y| * (4 * (cap x y) ^ ((3 : ℝ) / 4)) * ε ≤ t)
    (herr : rootDistPow 4 N u X U A C ≤ D ^ 4 * ε ^ 4) :
    rowNormPow 4 N u X Y (fun σ x y => w y * (A σ x y - C σ x y) / den x y) ≤
      (|D| * t) ^ 4 := by
  have hb := rowNormPow_relative_sub_le_rootDistPow hNu
    X Y U A C w den cap hA hC hoff
    (fun x y => (le_div_iff₀ hε).mpr (hcoef x y))
  apply hb.trans
  apply (mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ (t / ε) ^ 4)).trans_eq
  rw [mul_pow, (by decide : Even (4 : ℕ)).pow_abs]
  field_simp

/-- A product uses its pairwise range before ordinary-error conversion. Its
reset-right rooted error retains the exact source-rate ratio. The pairwise product
range may be proved using the smaller of support, row-sum or entrywise bounds;
this theorem does not replace it by a global support-times-range estimate. -/
theorem rowNormPow_relative_product_sub_le_root
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u f CA CB K : ℝ}
    (hN : 0 < N) (hu : 0 < u) (hf : 0 < f) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (X Z Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ z, Decidable (Z σ z)] [∀ σ y, Decidable (Y σ y)]
    [∀ σ y, Decidable (U σ y)]
    (L L' R R' : Ω → V → V → ℝ) (w : V → ℝ)
    (den cap : V → V → ℝ) (KR Kc : ℕ)
    (hL : ∀ σ x z, 0 ≤ L σ x z) (hL' : ∀ σ x z, L' σ x z ∈ Set.Icc 0 CA)
    (hR : ∀ σ z y, R σ z y ∈ Set.Icc 0 CB) (hR' : ∀ σ z y, 0 ≤ R' σ z y)
    (hprod : ∀ σ x y,
      (∑ z ∈ ({z | Z σ z} : Finset V), L σ x z * R σ z y) ∈ Set.Icc 0 (cap x y) ∧
      (∑ z ∈ ({z | Z σ z} : Finset V), L' σ x z * R' σ z y) ∈ Set.Icc 0 (cap x y))
    (hr : ∀ σ z, Z σ z → #{y ∈ ({y | U σ y} : Finset V) | R σ z y ≠ 0} ≤ KR)
    (hc : ∀ σ z, Z σ z → #{x ∈ ({x | X σ x} : Finset V) | L' σ x z ≠ 0} ≤ Kc)
    (hoff : ∀ σ z y, ¬ U σ y → R σ z y = 0 ∧ R' σ z y = 0)
    (hcoef : ∀ x y, |w y / den x y| * (4 * (cap x y) ^ ((3 : ℝ) / 4)) ≤ K) :
    rowNormPow 4 N u X Y (fun σ x y => w y *
      ((∑ z ∈ ({z | Z σ z} : Finset V), L σ x z * R σ z y) -
        ∑ z ∈ ({z | Z σ z} : Finset V), L' σ x z * R' σ z y) / den x y) ≤
      K ^ 4 * (16384 * (CB * KR * rootDistPow 4 N u X Z L L' +
        CA * Kc * (f / u) * rootDistPow 4 N f Z U R R')) := by
  have hb := rowNormPow_relative_sub_le_rootDistPow (mul_pos hN hu).le X Y U
    (fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), L σ x z * R σ z y)
    (fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), L' σ x z * R' σ z y)
    w den cap (fun σ x y => (hprod σ x y).1) (fun σ x y => (hprod σ x y).2)
    (by
      intro σ x y hy
      have hr0 : ∀ z, R σ z y = 0 := fun z => (hoff σ z y hy).1
      have hr1 : ∀ z, R' σ z y = 0 := fun z => (hoff σ z y hy).2
      simp only [hr0, hr1, mul_zero, sum_const_zero]) hcoef
  have hp := rootDistPow_mul_le (s := 4) (by decide) hN hu hf hL
    (fun σ x z => (hL' σ x z).1) (fun σ z y => (hR σ z y).1) hR'
    hCA hCB (fun σ x z => (hL' σ x z).2) (fun σ z y => (hR σ z y).2) hr hc
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat] at hp
  exact hb.trans (mul_le_mul_of_nonneg_left hp (by positivity))

end Cslib
