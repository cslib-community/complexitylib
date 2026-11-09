/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The potential for hard-core boosting

The signed margin of a collection of predictors is the number of correct votes minus the
number of incorrect votes. For a positive rate and relative to a movable threshold,
`weight rate margin` assigns full
weight to nonpositive margins, decreases linearly with slope `-rate`, and vanishes at `1 / rate`.
`potential rate margin` is the area under this curve to the right of the margin.

The quadratic upper bound on a change of potential gives both the progress from adding a
predictor and the cost of moving the threshold. These are scalar inequalities; no real-valued
operation here is being asserted to have an efficient implementation.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.Boosting.weight`: the clipped linear weight of a margin.
* `Cslib.Crypto.Pseudoentropy.Boosting.potential`: its integrated potential.

## Main results

* `Cslib.Crypto.Pseudoentropy.Boosting.potential_le_quadratic`: a uniform quadratic remainder.
* `Cslib.Crypto.Pseudoentropy.Boosting.potential_lower_bound`: the global affine lower bound.

## References

The potential argument of [Holenstein, Section 2.2, Figure 1 and Claims 2.10–2.11][Holenstein2005].
Our `rate` is the product `γδ`, and our margin is `N_C(x) - s` in that write-up.
Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

private def curve (x : ℝ) : ℝ := min 1 (max 0 (1 - x))

private noncomputable def area (x : ℝ) : ℝ :=
  if x ≤ 0 then 1 / 2 - x else (max 0 (1 - x)) ^ 2 / 2

private theorem curve_of_nonpos {x : ℝ} (hx : x ≤ 0) : curve x = 1 := by
  simp [curve, max_eq_right (by linarith : 0 ≤ 1 - x),
    min_eq_left (by linarith : 1 ≤ 1 - x)]

private theorem curve_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 1) : curve x = 1 - x := by
  simp [curve, max_eq_right (by linarith [hx.2] : 0 ≤ 1 - x),
    min_eq_right (by linarith [hx.1] : 1 - x ≤ 1)]

private theorem curve_of_one_le {x : ℝ} (hx : 1 ≤ x) : curve x = 0 := by
  simp [curve, max_eq_left (by linarith : 1 - x ≤ 0)]

private theorem area_of_nonpos {x : ℝ} (hx : x ≤ 0) : area x = 1 / 2 - x := by
  simp [area, hx]

private theorem area_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    area x = (1 - x) ^ 2 / 2 := by
  unfold area
  split_ifs with h
  · have : x = 0 := le_antisymm h hx.1
    subst x
    norm_num
  · rw [max_eq_right (by linarith [hx.2] : 0 ≤ 1 - x)]

private theorem area_of_one_le {x : ℝ} (hx : 1 ≤ x) : area x = 0 := by
  simp [area, not_le.mpr (by linarith : 0 < x),
    max_eq_left (by linarith : 1 - x ≤ 0)]

private theorem area_lower_bound (x : ℝ) : 1 / 2 - x ≤ area x := by
  rcases le_total x 0 with hx | hx
  · rw [area_of_nonpos hx]
  · rcases le_total x 1 with hx' | hx'
    · rw [area_of_mem_Icc ⟨hx, hx'⟩]
      nlinarith [sq_nonneg x]
    · rw [area_of_one_le hx']
      linarith

private theorem area_le_quadratic (x y : ℝ) :
    area y ≤ area x - curve x * (y - x) + (y - x) ^ 2 / 2 := by
  rcases le_total x 0 with hx | hx
  · rw [area_of_nonpos hx, curve_of_nonpos hx]
    rcases le_total y 0 with hy | hy
    · rw [area_of_nonpos hy]
      nlinarith [sq_nonneg (y - x)]
    · rcases le_total y 1 with hy' | hy'
      · rw [area_of_mem_Icc ⟨hy, hy'⟩]
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hx hy, sq_nonneg x]
      · rw [area_of_one_le hy']
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hx hy, sq_nonneg (y - 1),
          sq_nonneg x]
  · rcases le_total x 1 with hx' | hx'
    · rw [area_of_mem_Icc ⟨hx, hx'⟩, curve_of_mem_Icc ⟨hx, hx'⟩]
      rcases le_total y 0 with hy | hy
      · rw [area_of_nonpos hy]
        nlinarith [sq_nonneg y]
      · rcases le_total y 1 with hy' | hy'
        · rw [area_of_mem_Icc ⟨hy, hy'⟩]
          nlinarith
        · rw [area_of_one_le hy']
          nlinarith [sq_nonneg (y - 1)]
    · rw [area_of_one_le hx', curve_of_one_le hx']
      rcases le_total y 0 with hy | hy
      · rw [area_of_nonpos hy]
        nlinarith [sq_nonneg (x - 1), sq_nonneg y,
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx') hy]
      · rcases le_total y 1 with hy' | hy'
        · rw [area_of_mem_Icc ⟨hy, hy'⟩]
          nlinarith [sq_nonneg (x - 1),
            mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy')]
        · rw [area_of_one_le hy']
          nlinarith [sq_nonneg (y - x)]

/-- The clipped linear weight on an example's signed margin relative to the threshold. -/
def weight (rate margin : ℝ) : ℝ := min 1 (max 0 (1 - rate * margin))

/-- The area to the right of the margin under the clipped linear weight curve. -/
noncomputable def potential (rate margin : ℝ) : ℝ :=
  if margin ≤ 0 then 1 / (2 * rate) - margin else (max 0 (1 - rate * margin)) ^ 2 / (2 * rate)

/-- Weights are probabilities. -/
theorem weight_mem_Icc (rate margin : ℝ) : weight rate margin ∈ Set.Icc 0 1 := by
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- Increasing a margin can only decrease its weight. -/
theorem weight_antitone {rate : ℝ} (hrate : 0 ≤ rate) : Antitone (weight rate) := by
  intro x y hxy
  exact min_le_min_left _ (max_le_max_left _ (by nlinarith : 1 - rate * y ≤ 1 - rate * x))

/-- An example at or below the threshold has full weight. -/
theorem weight_of_nonpos {rate margin : ℝ} (hrate : 0 ≤ rate) (hmargin : margin ≤ 0) :
    weight rate margin = 1 :=
  curve_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hrate hmargin)

/-- Below the threshold, the potential has slope `-1`. -/
theorem potential_of_nonpos (rate : ℝ) {margin : ℝ} (hmargin : margin ≤ 0) :
    potential rate margin = 1 / (2 * rate) - margin := by
  simp [potential, hmargin]

private theorem potential_eq_area {rate : ℝ} (hrate : 0 < rate) (margin : ℝ) :
    potential rate margin = area (rate * margin) / rate := by
  unfold potential area
  by_cases hmargin : margin ≤ 0
  · rw [ite_eq_left hmargin,
      ite_eq_left (mul_nonpos_of_nonneg_of_nonpos hrate.le hmargin)]
    field_simp
  · rw [ite_eq_right hmargin,
      ite_eq_right (not_le.mpr (mul_pos hrate (not_le.mp hmargin)))]
    ring

/-- The potential is nonnegative. -/
theorem potential_nonneg {rate : ℝ} (hrate : 0 < rate) (margin : ℝ) :
    0 ≤ potential rate margin := by
  unfold potential
  split_ifs with hmargin
  · exact sub_nonneg.mpr (hmargin.trans (by positivity))
  · positivity

/-- The affine part of the potential is a global lower bound, including above the threshold. -/
theorem potential_lower_bound {rate : ℝ} (hrate : 0 < rate) (margin : ℝ) :
    1 / (2 * rate) - margin ≤ potential rate margin := by
  rw [potential_eq_area hrate]
  convert div_le_div_of_nonneg_right (area_lower_bound (rate * margin)) hrate.le using 1
  field_simp

/-- A quadratic remainder controls the change in potential at any margin. -/
theorem potential_le_quadratic {rate : ℝ} (hrate : 0 < rate) (x y : ℝ) :
    potential rate y ≤ potential rate x - weight rate x * (y - x) +
      rate * (y - x) ^ 2 / 2 := by
  have h := div_le_div_of_nonneg_right (area_le_quadratic (rate * x) (rate * y)) hrate.le
  rw [potential_eq_area hrate, potential_eq_area hrate]
  convert h using 1
  unfold weight curve
  field_simp

/-- A correct vote decreases the potential by its current weight, up to `rate / 2`. -/
theorem potential_add_one_le {rate : ℝ} (hrate : 0 < rate) (margin : ℝ) :
    potential rate (margin + 1) ≤ potential rate margin - weight rate margin + rate / 2 := by
  simpa using potential_le_quadratic hrate margin (margin + 1)

/-- An incorrect vote, or a unit threshold increase, costs at most the weight plus `rate / 2`. -/
theorem potential_sub_one_le {rate : ℝ} (hrate : 0 < rate) (margin : ℝ) :
    potential rate (margin - 1) ≤ potential rate margin + weight rate margin + rate / 2 := by
  simpa using potential_le_quadratic hrate margin (margin - 1)

/-- At a nonpositive margin a unit threshold increase costs exactly one, with no remainder. -/
theorem potential_sub_one_of_nonpos (rate : ℝ) {margin : ℝ} (hmargin : margin ≤ 0) :
    potential rate (margin - 1) = potential rate margin + 1 := by
  rw [potential_of_nonpos rate (by linarith), potential_of_nonpos rate hmargin]
  ring

end Cslib.Crypto.Pseudoentropy.Boosting
