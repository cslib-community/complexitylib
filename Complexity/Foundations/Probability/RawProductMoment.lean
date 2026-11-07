/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.SourceRelease
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fourth moments of products on a shared environment

Original finite inequalities by Christian Reitwiessner, using Samuel Schlesinger's
source-release argument. The left row cap and entry range control the fourth power
of the midpoint sum; its incoming cap releases the old source. No independence is used.
The right child keeps its actual lower-child fourth moment and the explicit `f / u`
normalization. This does not prove recursive child moment budgets.

## Main results

* `Cslib.rowNormPow_product_le`: a lower right-child moment pays the product moment.
* `Cslib.rowNormPow_add_sub_le`: signed three-term moment assembly.
-/
public section
open Finset
open scoped BigOperators

namespace Finset

/-- The fourth power of a sparse sum, with no ambient cardinality cost. -/
theorem abs_sum_pow_four_le {α : Type*} (T : Finset α) (v : α → ℝ) {K : ℕ}
    (hK : T.card ≤ K) :
    |∑ z ∈ T, v z| ^ 4 ≤ (K : ℝ) ^ 3 * ∑ z ∈ T, |v z| ^ 4 := by
  calc
    _ ≤ (∑ z ∈ T, |v z|) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_sum_le_sum_abs _ _) _
    _ ≤ (T.card : ℝ) ^ 3 * ∑ z ∈ T, |v z| ^ 4 := by
      simpa using (pow_sum_le_card_mul_sum_pow (s := T) (f := fun z => |v z|)
        (fun _ _ => abs_nonneg _) 3)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hK) _) (by positivity)

end Finset

namespace Cslib

variable {Ω V : Type*} [Fintype Ω] [Fintype V]
  {N u f : ℝ} {X Z Y : Ω → V → Prop}
  [∀ σ x, Decidable (X σ x)] [∀ σ z, Decidable (Z σ z)] [∀ σ y, Decidable (Y σ y)]

/-- A two-factor input moment from a lower right-child moment. Both children may depend
on every coordinate of the same environment. The old source is absent from the right child. -/
theorem rowNormPow_product_le (hN : 0 < N) (hu : 0 < u) (hf : 0 < f)
    {A B : Ω → V → V → ℝ} {CA : ℝ}
    (hA : ∀ σ x z, |A σ x z| ≤ CA) {K Kc : ℕ}
    (hrow : ∀ σ x, X σ x → #{z ∈ ({z | Z σ z} : Finset V) | A σ x z ≠ 0} ≤ K)
    (hcol : ∀ σ z, Z σ z → #{x ∈ ({x | X σ x} : Finset V) | A σ x z ≠ 0} ≤ Kc) :
    rowNormPow 4 N u X Y (fun σ x y =>
      ∑ z ∈ ({z | Z σ z} : Finset V), A σ x z * B σ z y) ≤
      (K : ℝ) ^ 3 * CA ^ 4 * Kc * (f / u) * rowNormPow 4 N f Z Y B := by
  classical
  have hp : ∀ σ x y, X σ x →
      |∑ z ∈ ({z | Z σ z} : Finset V), A σ x z * B σ z y| ^ 4 ≤
        (K : ℝ) ^ 3 * CA ^ 4 *
          ∑ z ∈ ({z | Z σ z} : Finset V) with A σ x z ≠ 0, |B σ z y| ^ 4 := by
    intro σ x y hx
    rw [← sum_filter_of_ne (p := fun z => A σ x z ≠ 0)
      (fun z _ h hz => h (by rw [hz, zero_mul]))]
    calc
      _ ≤ (K : ℝ) ^ 3 * ∑ z ∈ ({z | Z σ z} : Finset V) with A σ x z ≠ 0,
          |A σ x z * B σ z y| ^ 4 := abs_sum_pow_four_le _ _ (hrow σ x hx)
      _ ≤ (K : ℝ) ^ 3 * ∑ z ∈ ({z | Z σ z} : Finset V) with A σ x z ≠ 0,
          CA ^ 4 * |B σ z y| ^ 4 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => ?_) (by positivity)
        rw [abs_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hA σ x z) _) (by positivity)
      _ = _ := by rw [← mul_sum]; ring
  have hrelease := sourceRelease_le_rowNormPow (s := 4) (Y := Y) hN hu hf
    (fun σ x z => A σ x z ≠ 0) hcol B
  calc
    _ ≤ (K : ℝ) ^ 3 * CA ^ 4 * ((N * u)⁻¹ * 𝔼 σ,
        ∑ x ∈ ({x | X σ x} : Finset V),
          ∑ z ∈ ({z | Z σ z} : Finset V) with A σ x z ≠ 0,
            ∑ y ∈ ({y | Y σ y} : Finset V), |B σ z y| ^ 4) := by
      rw [rowNormPow]
      have hs : ∀ σ x, X σ x →
          ∑ y ∈ ({y | Y σ y} : Finset V),
            |∑ z ∈ ({z | Z σ z} : Finset V), A σ x z * B σ z y| ^ 4 ≤
          (K : ℝ) ^ 3 * CA ^ 4 *
            ∑ z ∈ ({z | Z σ z} : Finset V) with A σ x z ≠ 0,
              ∑ y ∈ ({y | Y σ y} : Finset V), |B σ z y| ^ 4 := by
        intro σ x hx
        rw [sum_comm, mul_sum]
        exact sum_le_sum fun y _ => hp σ x y hx
      calc
        _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
            (K : ℝ) ^ 3 * CA ^ 4 *
              ∑ z ∈ ({z | Z σ z} : Finset V) with A σ x z ≠ 0,
                ∑ y ∈ ({y | Y σ y} : Finset V), |B σ z y| ^ 4 := by
          refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (by positivity)
          exact sum_le_sum fun x hx => hs σ x (by simpa using hx)
        _ = _ := by simp only [← mul_sum, ← mul_expect]; ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hrelease
        (show 0 ≤ (K : ℝ) ^ 3 * CA ^ 4 by positivity) using 1; ring

/-- A conservative three-term signed input estimate. It applies before any slice walk. -/
theorem rowNormPow_add_sub_le (hNu : 0 ≤ N * u)
    (A B C : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => A σ x y + B σ x y - C σ x y) ≤
      64 * (rowNormPow 4 N u X Y A + rowNormPow 4 N u X Y B +
        rowNormPow 4 N u X Y C) := by
  have hp (a b c : ℝ) : |a + b - c| ^ 4 ≤ 64 * (|a| ^ 4 + |b| ^ 4 + |c| ^ 4) := by
    have hab := add_pow_le (abs_nonneg a) (abs_nonneg b) 4
    have habc := add_pow_le (add_nonneg (abs_nonneg a) (abs_nonneg b)) (abs_nonneg c) 4
    have ht : |a + b - c| ≤ (|a| + |b|) + |c| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have ht4 := pow_le_pow_left₀ (abs_nonneg _) ht 4
    norm_num at hab habc
    nlinarith [pow_nonneg (abs_nonneg c) 4]
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ y ∈ ({y | Y σ y} : Finset V),
          64 * (|A σ x y| ^ 4 + |B σ x y| ^ 4 + |C σ x y| ^ 4) := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.2 hNu)
      exact sum_le_sum fun x _ => sum_le_sum fun y _ => hp _ _ _
    _ = _ := by
      simp only [mul_add, sum_add_distrib, expect_add_distrib, ← mul_sum, ← mul_expect]
      ring

end Cslib
