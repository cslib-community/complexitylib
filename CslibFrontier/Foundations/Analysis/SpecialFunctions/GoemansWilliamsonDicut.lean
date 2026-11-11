/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Goemans–Williamson MAX-DICUT constant

The Goemans–Williamson approximation constant for MAX-DICUT is
`β = inf_{0 ≤ θ < arccos (-1 / 3)} (2 / π) · (2π - 3θ) / (1 + 3 cos θ)`
[GoemansWilliamson1995, Section 7.3]. Goemans and Williamson show `β > 0.79607` and prove
[GoemansWilliamson1995, Lemma 7.3.2]: for all `(a, b, c)` in the spherical-triangle angle set
`S = {(a, b, c) ∈ [0, π]³ | a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ a + b + c ≤ 2π}`,
`1 - (a + b + c) / (2π) ≥ (β / 4) · (1 + cos a + cos b + cos c)`.

Here `β` is `Real.goemansWilliamsonDicutConstant`. The bounds `0.79607 < β < 0.79608` use the
degree-ten Taylor bounds `Real.cos_bound_ten` and `Real.sin_bound_ten` at `θ₀ = π / 2 - 0.6439956`
(and at `0.8`, `1.0` for the boundary case of Lemma 7.3.2), together with Mathlib's twenty-digit
bounds on `π`. For the interior case of Lemma 7.3.2, `cos x ≥ 0` follows directly from the
midpoint identity `g(x + δ) + g(x - δ) - 2 g(x) = (β / 2) (1 - cos δ) cos x ≥ 0`, without a
Hessian calculation.

## Main definitions

* `Real.goemansWilliamsonDicutConstant`: the constant `β`.
* `Real.DicutAngleSet`: the spherical-triangle angle polytope `S ⊆ ℝ × ℝ × ℝ`.

## Main results

* `Real.goemansWilliamsonDicutConstant_nonneg`: `0 ≤ β`.
* `Real.goemansWilliamsonDicutConstant_mul_one_add_three_cos_le`:
  `β · (1 + 3 cos θ) ≤ (2 / π) · (2π - 3θ)` for `0 ≤ θ < arccos (-1 / 3)`.
* `Real.lt_goemansWilliamsonDicutConstant`: `0.79607 < β` [GoemansWilliamson1995, Section 7.3].
* `Real.goemansWilliamsonDicutConstant_lt`: `β < 0.79608`.
* `Real.goemansWilliamsonDicutConstant_mul_add_cos_le`:
  `(β / 4) · (1 + cos a + cos b + cos c) ≤ 1 - (a + b + c) / (2π)` on `DicutAngleSet`
  [GoemansWilliamson1995, Lemma 7.3.2].

## References

* [GoemansWilliamson1995]
-/

public section

open Set

namespace Real

private theorem pi_div_two_lt_arccos_neg_third : π / 2 < arccos (-1 / 3) :=
  pi_div_two_lt_arccos.2 (by norm_num)

private theorem arccos_neg_third_lt_two_pi_div_three : arccos (-1 / 3) < 2 * π / 3 := by
  have hcos : cos (2 * π / 3) = -1 / 2 := by
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
    ring
  calc arccos (-1 / 3) < arccos (-1 / 2) :=
        arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
    _ = 2 * π / 3 := by
      rw [← hcos, arccos_cos (by positivity) (by linarith [pi_pos])]

private theorem one_add_three_cos_pos {θ : ℝ} (h0 : 0 ≤ θ) (hθ : θ < arccos (-1 / 3)) :
    0 < 1 + 3 * cos θ := by
  have hlt := cos_lt_cos_of_nonneg_of_le_pi h0 (arccos_le_pi _) hθ
  rw [cos_arccos (by norm_num) (by norm_num)] at hlt
  linarith

/-- **The Goemans–Williamson MAX-DICUT constant**
`β = inf_{0 ≤ θ < arccos (-1 / 3)} (2 / π) · (2π - 3θ) / (1 + 3 cos θ)`
[GoemansWilliamson1995, Section 7.3]. The minimum is attained near `θ ≈ 0.92680`, where
`β ≈ 0.79607015`. -/
noncomputable def goemansWilliamsonDicutConstant : ℝ :=
  ⨅ θ : Ico (0 : ℝ) (arccos (-1 / 3)), 2 / π * (2 * π - 3 * θ) / (1 + 3 * cos θ)

private theorem dicut_term_nonneg (θ : Ico (0 : ℝ) (arccos (-1 / 3))) :
    0 ≤ 2 / π * (2 * π - 3 * (θ : ℝ)) / (1 + 3 * cos θ) := by
  have hnum : 0 ≤ 2 * π - 3 * (θ : ℝ) := by
    linarith [θ.2.2.trans arccos_neg_third_lt_two_pi_div_three]
  exact div_nonneg (mul_nonneg (div_nonneg zero_le_two pi_pos.le) hnum)
    (one_add_three_cos_pos θ.2.1 θ.2.2).le

private theorem dicut_bddBelow :
    BddBelow (range fun θ : Ico (0 : ℝ) (arccos (-1 / 3)) =>
      2 / π * (2 * π - 3 * (θ : ℝ)) / (1 + 3 * cos θ)) :=
  ⟨0, by rintro _ ⟨θ, rfl⟩; exact dicut_term_nonneg θ⟩

/-- The Goemans–Williamson MAX-DICUT constant is nonnegative. -/
theorem goemansWilliamsonDicutConstant_nonneg : 0 ≤ goemansWilliamsonDicutConstant :=
  Real.iInf_nonneg dicut_term_nonneg

/-- Defining inequality of `goemansWilliamsonDicutConstant`:
`β · (1 + 3 cos θ) ≤ (2 / π) · (2π - 3θ)` for `0 ≤ θ < arccos (-1 / 3)`. -/
theorem goemansWilliamsonDicutConstant_mul_one_add_three_cos_le {θ : ℝ} (h0 : 0 ≤ θ)
    (hθ : θ < arccos (-1 / 3)) :
    goemansWilliamsonDicutConstant * (1 + 3 * cos θ) ≤ 2 / π * (2 * π - 3 * θ) := by
  rw [← le_div_iff₀ (one_add_three_cos_pos h0 hθ)]
  exact ciInf_le dicut_bddBelow (⟨θ, h0, hθ⟩ : Ico (0 : ℝ) (arccos (-1 / 3)))

/-! ### Numerical bounds `0.79607 < β < 0.79608` -/

/-- Taylor interval for `cos x` on `[0, 1]` from `Real.cos_bound_ten`. -/
private theorem cos_interval_ten {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let p := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
    let e := x ^ 10 * (11 / 36288000)
    p - e ≤ cos x ∧ cos x ≤ p + e := by
  have h := cos_bound_ten (x := x) (by rwa [abs_of_nonneg hx0])
  rw [abs_of_nonneg hx0, abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Taylor interval for `sin x` on `[0, 1]` from `Real.sin_bound_ten`. -/
private theorem sin_interval_ten {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let p := x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880
    let e := x ^ 10 * (11 / 36288000)
    p - e ≤ sin x ∧ sin x ≤ p + e := by
  have h := sin_bound_ten (x := x) (by rwa [abs_of_nonneg hx0])
  rw [abs_of_nonneg hx0, abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private noncomputable def dicutD0 : ℝ := 6439956 / 10000000

private theorem cos_dicutD0_bounds :
    (7997032070 : ℝ) / 10000000000 ≤ cos dicutD0 ∧
      cos dicutD0 ≤ 7997032150 / 10000000000 := by
  have h := cos_interval_ten (x := dicutD0) (by norm_num [dicutD0]) (by norm_num [dicutD0])
  dsimp only [dicutD0] at h ⊢
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]

private theorem sin_dicutD0_bounds :
    (6003955160 : ℝ) / 10000000000 ≤ sin dicutD0 ∧
      sin dicutD0 ≤ 6003955240 / 10000000000 := by
  have h := sin_interval_ten (x := dicutD0) (by norm_num [dicutD0]) (by norm_num [dicutD0])
  dsimp only [dicutD0] at h ⊢
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]

private theorem dicut_theta0_mem :
    π / 2 - dicutD0 ∈ Ico (0 : ℝ) (arccos (-1 / 3)) := by
  have hplo := pi_gt_d20
  have hphi := pi_lt_d20
  refine ⟨?_, ?_⟩
  · dsimp only [dicutD0]
    linarith
  · have : 0 < dicutD0 := by norm_num [dicutD0]
    linarith [pi_div_two_lt_arccos_neg_third]

/-- The Goemans–Williamson MAX-DICUT constant is strictly less than `0.79608`. -/
theorem goemansWilliamsonDicutConstant_lt : goemansWilliamsonDicutConstant < 0.79608 := by
  set θ₀ := π / 2 - dicutD0
  refine lt_of_le_of_lt (ciInf_le dicut_bddBelow ⟨θ₀, dicut_theta0_mem⟩) ?_
  have hcos : cos θ₀ = sin dicutD0 := cos_pi_div_two_sub dicutD0
  rw [hcos]
  obtain ⟨hs1, hs2⟩ := sin_dicutD0_bounds
  have hden : 0 < 1 + 3 * sin dicutD0 := by linarith
  have hplo := pi_gt_d20
  have hphi := pi_lt_d20
  have hpi := pi_pos
  rw [div_lt_iff₀ hden, show (2 / π * (2 * π - 3 * θ₀) : ℝ) = 2 * (2 * π - 3 * θ₀) / π by ring,
    div_lt_iff₀ hpi]
  dsimp only [θ₀, dicutD0] at hs1 hs2 ⊢
  nlinarith

/-- Lower bound for `c₀ = 0.79607001` against the defining expression on `[0, π / 2]`. -/
private theorem dicut_lower_first {θ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ π / 2) :
    (79607001 / 100000000 : ℝ) * (1 + 3 * cos θ) ≤ 2 / π * (2 * π - 3 * θ) := by
  set θ₀ := π / 2 - dicutD0
  have hplo := pi_gt_d20
  have hphi := pi_lt_d20
  have hpi := pi_pos
  have hθ0 : θ₀ ∈ Icc (-(π / 2)) (π / 2) := by
    dsimp only [θ₀, dicutD0]
    constructor <;> linarith
  have hθ' : θ ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith, hθ⟩
  have htan := cos_le_cos_sub_sin_mul hθ' hθ0
  rw [cos_pi_div_two_sub, sin_pi_div_two_sub] at htan
  obtain ⟨hs1, hs2⟩ := sin_dicutD0_bounds
  obtain ⟨hc1, hc2⟩ := cos_dicutD0_bounds
  set c₀ : ℝ := 79607001 / 100000000
  have hlin : (c₀ * π / 2) * (1 + 3 * cos θ) ≤
      (c₀ * π / 2) * (1 + 3 * (sin dicutD0 - cos dicutD0 * (θ - θ₀))) := by
    refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hA : (58 / 100000000 : ℝ) ≤
      2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0) := by
    dsimp only [c₀, θ₀, dicutD0] at hs1 hs2 ⊢
    nlinarith
  have hB1 : (-16 / 100000000 : ℝ) ≤ -3 + 3 * (c₀ * π / 2) * cos dicutD0 := by
    dsimp only [c₀, dicutD0] at hc1 hc2 ⊢
    nlinarith
  have hB2 : -3 + 3 * (c₀ * π / 2) * cos dicutD0 ≤ 0 := by
    dsimp only [c₀, dicutD0] at hc1 hc2 ⊢
    nlinarith
  have hzero : 0 ≤ (2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) -
      (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * θ₀ := by
    dsimp only [θ₀, dicutD0] at hA hB1 hB2 ⊢
    nlinarith
  have hhalf : 0 ≤ (2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) +
      (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * dicutD0 := by
    dsimp only [dicutD0] at hA hB1 hB2 ⊢
    nlinarith
  have hconvex : 0 ≤ (π / 2) * ((2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) +
      (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * (θ - θ₀)) := by
    have h1 : 0 ≤ (π / 2 - θ) *
        ((2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) -
          (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * θ₀) :=
      mul_nonneg (by linarith) hzero
    have h2 : 0 ≤ θ *
        ((2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) +
          (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * dicutD0) :=
      mul_nonneg h0 hhalf
    have hid : (π / 2) * ((2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) +
        (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * (θ - θ₀)) =
        (π / 2 - θ) * ((2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) -
          (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * θ₀) +
        θ * ((2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) +
          (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * dicutD0) := by
      dsimp only [θ₀]
      ring
    linarith
  have hcomb : (c₀ * π / 2) * (1 + 3 * (sin dicutD0 - cos dicutD0 * (θ - θ₀))) ≤ 2 * π - 3 * θ := by
    have hdiff : (2 * π - 3 * θ) -
        (c₀ * π / 2) * (1 + 3 * (sin dicutD0 - cos dicutD0 * (θ - θ₀))) =
        (2 * π - 3 * θ₀ - (c₀ * π / 2) * (1 + 3 * sin dicutD0)) +
        (-3 + 3 * (c₀ * π / 2) * cos dicutD0) * (θ - θ₀) := by ring
    have hnn : 0 ≤ (2 * π - 3 * θ) -
        (c₀ * π / 2) * (1 + 3 * (sin dicutD0 - cos dicutD0 * (θ - θ₀))) := by
      rw [hdiff]
      exact nonneg_of_mul_nonneg_right hconvex (by positivity)
    linarith
  have hrew : c₀ * (1 + 3 * cos θ) * π = 2 * (c₀ * π / 2 * (1 + 3 * cos θ)) := by ring
  rw [show (2 / π * (2 * π - 3 * θ) : ℝ) = 2 * (2 * π - 3 * θ) / π by ring, le_div_iff₀ hpi, hrew]
  linarith

/-- Lower bound for `c₀ = 0.79607001` against the defining expression on `[π / 2, 2π / 3)`. -/
private theorem dicut_lower_second {θ : ℝ} (hθ : π / 2 ≤ θ) (hθ2 : θ < 2 * π / 3) :
    (79607001 / 100000000 : ℝ) * (1 + 3 * cos θ) ≤ 2 / π * (2 * π - 3 * θ) := by
  set c₀ : ℝ := 79607001 / 100000000
  set u := θ - π / 2
  have hu0 : 0 ≤ u := sub_nonneg.2 hθ
  have hu1 : u < π / 6 := by dsimp only [u]; linarith
  have hsin : u - u ^ 3 / 6 ≤ sin u := by
    rcases hu0.eq_or_lt with h | h
    · rw [← h]; norm_num
    · exact (sin_gt_sub_cube h).le
  have hcos : -cos θ = sin u := by
    rw [show θ = u + π / 2 by dsimp only [u]; ring, cos_add_pi_div_two, neg_neg]
  have hplo := pi_gt_d20
  have hphi := pi_lt_d20
  have hpi := pi_pos
  have hu_sq : u ^ 2 ≤ (π / 6) ^ 2 := by nlinarith
  have hsin_lin : u * (1 - (π / 6) ^ 2 / 6) ≤ sin u := by nlinarith
  have hmain : (c₀ * π / 2) * (1 - 3 * sin u) ≤ 2 * π - 3 * θ := by
    have hcoeff : 3 ≤ 3 * (c₀ * π / 2) * (1 - (π / 6) ^ 2 / 6) := by
      dsimp only [c₀]
      nlinarith
    have h1 : 3 * u ≤ 3 * (c₀ * π / 2) * sin u := by
      calc 3 * u ≤ (3 * (c₀ * π / 2) * (1 - (π / 6) ^ 2 / 6)) * u := by nlinarith
        _ = 3 * (c₀ * π / 2) * (u * (1 - (π / 6) ^ 2 / 6)) := by ring
        _ ≤ 3 * (c₀ * π / 2) * sin u := by
          refine mul_le_mul_of_nonneg_left hsin_lin (by positivity)
    have hbase : c₀ * π / 2 ≤ π / 2 := by
      dsimp only [c₀]
      nlinarith
    have hθ_eq : 2 * π - 3 * θ = π / 2 - 3 * u := by dsimp only [u]; ring
    linarith
  have hcos' : cos θ = -sin u := by linarith
  have hrew : c₀ * (1 + 3 * -sin u) * π = 2 * ((c₀ * π / 2) * (1 - 3 * sin u)) := by ring
  rw [hcos', show (2 / π * (2 * π - 3 * θ) : ℝ) = 2 * (2 * π - 3 * θ) / π by ring, le_div_iff₀ hpi,
    hrew]
  linarith

/-- **Goemans–Williamson MAX-DICUT constant bound.**
`goemansWilliamsonDicutConstant > 0.79607` [GoemansWilliamson1995, Section 7.3]. -/
theorem lt_goemansWilliamsonDicutConstant :
    (0.79607 : ℝ) < goemansWilliamsonDicutConstant := by
  have : Nonempty (Ico (0 : ℝ) (arccos (-1 / 3))) :=
    ⟨⟨0, le_rfl, (div_pos pi_pos zero_lt_two).trans pi_div_two_lt_arccos_neg_third⟩⟩
  refine lt_of_lt_of_le (by norm_num : (0.79607 : ℝ) < 79607001 / 100000000) ?_
  refine le_ciInf fun θ => ?_
  rw [le_div_iff₀ (one_add_three_cos_pos θ.2.1 θ.2.2)]
  rcases le_or_gt (θ : ℝ) (π / 2) with h | h
  · exact dicut_lower_first θ.2.1 h
  · exact dicut_lower_second h.le (θ.2.2.trans arccos_neg_third_lt_two_pi_div_three)

/-! ### Lemma 7.3.2: inequality over the spherical-triangle angle set -/

/-- The spherical-triangle angle polytope
`S = {(a, b, c) ∈ [0, π]³ | a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ a + b + c ≤ 2π}`
of [GoemansWilliamson1995, Lemma 7.3.2]. -/
def DicutAngleSet : Set (ℝ × ℝ × ℝ) :=
  {p | match p with
    | (a, b, c) =>
      0 ≤ a ∧ a ≤ π ∧ 0 ≤ b ∧ b ≤ π ∧ 0 ≤ c ∧ c ≤ π ∧
        a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ a + b + c ≤ 2 * π}

/-- Membership characterization for `Real.DicutAngleSet`. -/
theorem mem_dicutAngleSet_iff {a b c : ℝ} :
    (a, b, c) ∈ DicutAngleSet ↔
      0 ≤ a ∧ a ≤ π ∧ 0 ≤ b ∧ b ≤ π ∧ 0 ≤ c ∧ c ≤ π ∧
        a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ a + b + c ≤ 2 * π :=
  Iff.rfl

private noncomputable def dicutObj (p : ℝ × ℝ × ℝ) : ℝ :=
  1 - (p.1 + p.2.1 + p.2.2) / (2 * π) -
    goemansWilliamsonDicutConstant / 4 * (1 + cos p.1 + cos p.2.1 + cos p.2.2)

private theorem dicutObj_perm12 (a b c : ℝ) : dicutObj (b, a, c) = dicutObj (a, b, c) := by
  simp only [dicutObj]
  ring

private theorem dicutObj_perm13 (a b c : ℝ) : dicutObj (c, b, a) = dicutObj (a, b, c) := by
  simp only [dicutObj]
  ring

private theorem mem_dicutAngleSet_perm12 {a b c : ℝ} (h : (a, b, c) ∈ DicutAngleSet) :
    (b, a, c) ∈ DicutAngleSet := by
  rw [mem_dicutAngleSet_iff] at h ⊢
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h3, h4, h1, h2, h5, h6, h8, h7, by linarith, by linarith⟩

private theorem mem_dicutAngleSet_perm13 {a b c : ℝ} (h : (a, b, c) ∈ DicutAngleSet) :
    (c, b, a) ∈ DicutAngleSet := by
  rw [mem_dicutAngleSet_iff] at h ⊢
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h5, h6, h3, h4, h1, h2, by linarith, by linarith, by linarith, by linarith⟩

private theorem isCompact_dicutAngleSet : IsCompact DicutAngleSet := by
  have hsub : DicutAngleSet ⊆ Icc (0 : ℝ) π ×ˢ (Icc (0 : ℝ) π ×ˢ Icc (0 : ℝ) π) := by
    rintro ⟨a, b, c⟩ ⟨h1, h2, h3, h4, h5, h6, _⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
  have hclosed : IsClosed DicutAngleSet := by
    have hset : DicutAngleSet = {p : ℝ × ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ π ∧ 0 ≤ p.2.1 ∧
        p.2.1 ≤ π ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ π ∧ p.1 ≤ p.2.1 + p.2.2 ∧
        p.2.1 ≤ p.1 + p.2.2 ∧ p.2.2 ≤ p.1 + p.2.1 ∧ p.1 + p.2.1 + p.2.2 ≤ 2 * π} := by
      ext ⟨a, b, c⟩
      rfl
    rw [hset]
    simp only [ofPred_and]
    repeat' refine IsClosed.inter ?_ ?_
    all_goals exact isClosed_le (by fun_prop) (by fun_prop)
  exact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset hclosed hsub

private theorem one_add_cos_add_cos_add_cos_add (a b : ℝ) :
    1 + cos a + cos b + cos (a + b) =
      2 * cos ((a + b) / 2) * (cos ((a + b) / 2) + cos ((a - b) / 2)) := by
  have h1 : cos a + cos b = 2 * cos ((a + b) / 2) * cos ((a - b) / 2) := cos_add_cos a b
  have h2 : 1 + cos (a + b) = 2 * cos ((a + b) / 2) ^ 2 := by
    nth_rw 1 [show a + b = 2 * ((a + b) / 2) by ring]
    rw [cos_two_mul]
    ring
  linarith

/-- Case (1) of Lemma 7.3.2: `a + b + c = 2π`. -/
private theorem dicutObj_nonneg_of_sum_eq {a b c : ℝ} (hmem : (a, b, c) ∈ DicutAngleSet)
    (hsum : a + b + c = 2 * π) : 0 ≤ dicutObj (a, b, c) := by
  rw [mem_dicutAngleSet_iff] at hmem
  rcases hmem with ⟨_, _, _, _, _, h6, h7, h8, _, _⟩
  have hc : c = 2 * π - (a + b) := by linarith
  have htrig : 1 + cos a + cos b + cos c =
      2 * cos ((a + b) / 2) * (cos ((a + b) / 2) + cos ((a - b) / 2)) := by
    rw [hc, cos_two_pi_sub, one_add_cos_add_cos_add_cos_add]
  have hpi2 : π / 2 ≤ (a + b) / 2 := by linarith
  have hpi : (a + b) / 2 ≤ π + π / 2 := by linarith [pi_pos]
  have hcos_le : cos ((a + b) / 2) ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hpi2 hpi
  have hdiff1 : |a - b| ≤ c := abs_le.2 ⟨by linarith, by linarith⟩
  have hdiff2 : |(a - b) / 2| ≤ π - (a + b) / 2 := by
    rw [abs_div, abs_two]
    linarith
  have hcos_sum : 0 ≤ cos ((a + b) / 2) + cos ((a - b) / 2) := by
    rw [← cos_abs ((a - b) / 2)]
    have hmon := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [pi_pos]) hdiff2
    rw [cos_pi_sub] at hmon
    linarith
  have hprod : 1 + cos a + cos b + cos c ≤ 0 := by
    rw [htrig]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hcos_sum
  have hβ := goemansWilliamsonDicutConstant_nonneg
  have hleft : 1 - (a + b + c) / (2 * π) = 0 := by
    rw [hsum, div_self (by positivity), sub_self]
  dsimp only [dicutObj]
  rw [hleft, zero_sub]
  exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hβ (by norm_num)) hprod)

private theorem dicut_case2_tangent {u u₀ lo hi s_hi c_lo c_hi : ℝ}
    (hu0 : 0 ≤ u₀) (hu0_pi : u₀ ≤ π / 2) (hu_0 : 0 ≤ u) (hu_pi : u ≤ π / 2)
    (hlo : lo ≤ u) (hhi : u ≤ hi) (hlo_u0 : lo < u₀) (hu0_hi : u₀ < hi)
    (hs : sin u₀ ≤ s_hi) (hc1 : c_lo ≤ cos u₀) (hc2 : cos u₀ ≤ c_hi)
    (h_end_lo : (0.39804 : ℝ) * (s_hi + c_lo * (lo - u₀)) *
        (1 + (s_hi + c_lo * (lo - u₀))) ≤ 2 * lo / π)
    (h_end_mid : (0.39804 : ℝ) * s_hi * (1 + s_hi) ≤ 2 * u₀ / π)
    (h_end_hi : (0.39804 : ℝ) * (s_hi + c_hi * (hi - u₀)) *
        (1 + (s_hi + c_hi * (hi - u₀))) ≤ 2 * hi / π) :
    (0.39804 : ℝ) * sin u * (1 + sin u) ≤ 2 * u / π := by
  have htan : sin u ≤ sin u₀ + cos u₀ * (u - u₀) := by
    have h := cos_le_cos_sub_sin_mul
      (x := π / 2 - u) (x₀ := π / 2 - u₀)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    rw [cos_pi_div_two_sub, cos_pi_div_two_sub, sin_pi_div_two_sub] at h
    linarith
  have hsin0 : 0 ≤ sin u := sin_nonneg_of_nonneg_of_le_pi hu_0 (by linarith)
  have hquad : ∀ {a b slope : ℝ}, a < b → a ≤ u → u ≤ b →
      sin u ≤ s_hi + slope * (u - u₀) →
      (0.39804 : ℝ) * (s_hi + slope * (a - u₀)) * (1 + (s_hi + slope * (a - u₀))) ≤ 2 * a / π →
      (0.39804 : ℝ) * (s_hi + slope * (b - u₀)) * (1 + (s_hi + slope * (b - u₀))) ≤ 2 * b / π →
      (0.39804 : ℝ) * sin u * (1 + sin u) ≤ 2 * u / π := by
    intro a b slope hab hau hub hlin ha hb
    have hL : (0.39804 : ℝ) * sin u * (1 + sin u) ≤
        (0.39804 : ℝ) * (s_hi + slope * (u - u₀)) * (1 + (s_hi + slope * (u - u₀))) := by
      nlinarith
    have hsec : 0 ≤ (b - u) * (2 * a / π - (0.39804 : ℝ) * (s_hi + slope * (a - u₀)) *
          (1 + (s_hi + slope * (a - u₀)))) +
        (u - a) * (2 * b / π - (0.39804 : ℝ) * (s_hi + slope * (b - u₀)) *
          (1 + (s_hi + slope * (b - u₀)))) :=
      add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
    have hconv : (b - a) * (2 * u / π - (0.39804 : ℝ) * (s_hi + slope * (u - u₀)) *
          (1 + (s_hi + slope * (u - u₀)))) =
        (b - u) * (2 * a / π - (0.39804 : ℝ) * (s_hi + slope * (a - u₀)) *
          (1 + (s_hi + slope * (a - u₀)))) +
        (u - a) * (2 * b / π - (0.39804 : ℝ) * (s_hi + slope * (b - u₀)) *
          (1 + (s_hi + slope * (b - u₀)))) +
        (0.39804 : ℝ) * slope ^ 2 * (b - a) * (b - u) * (u - a) := by
      have := pi_ne_zero
      field_simp
      ring
    have hsq_nn : 0 ≤ (0.39804 : ℝ) * slope ^ 2 * (b - a) * (b - u) * (u - a) := by
      have : 0 ≤ b - a := by linarith
      have : 0 ≤ b - u := by linarith
      have : 0 ≤ u - a := by linarith
      positivity
    have hprod_nn : 0 ≤ (b - a) * (2 * u / π - (0.39804 : ℝ) * (s_hi + slope * (u - u₀)) *
        (1 + (s_hi + slope * (u - u₀)))) := by linarith
    have hres : 0 ≤ 2 * u / π - (0.39804 : ℝ) * (s_hi + slope * (u - u₀)) *
        (1 + (s_hi + slope * (u - u₀))) :=
      nonneg_of_mul_nonneg_right hprod_nn (by linarith)
    linarith
  rcases le_or_gt u u₀ with hle | hgt
  · refine hquad hlo_u0 hlo hle (by nlinarith) h_end_lo (by simpa using h_end_mid)
  · refine hquad hu0_hi hgt.le hhi (by nlinarith) (by simpa using h_end_mid) h_end_hi

/-- Boundary quadratic bound for Case (2) of Lemma 7.3.2 on `[0, π / 2]`. -/
private theorem dicut_case2_u {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ π / 2) :
    (0.39804 : ℝ) * sin u * (1 + sin u) ≤ 2 * u / π := by
  have hplo := pi_gt_d20
  have hphi := pi_lt_d20
  have hpi := pi_pos
  rcases le_or_gt u 0.59 with h1 | h1
  · have hs : sin u ≤ u := sin_le hu0
    have hsin0 : 0 ≤ sin u := sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith)
    have hp : (0.39804 : ℝ) * sin u * (1 + sin u) ≤ (0.39804 : ℝ) * u * (1 + 0.59) := by
      nlinarith
    have hp2 : (0.39804 : ℝ) * u * (1 + 0.59) ≤ 2 * u / π := by
      rw [le_div_iff₀ hpi]
      nlinarith
    exact hp.trans hp2
  · rcases le_or_gt 1.251 u with h2 | h2
    · have hs1 : sin u ≤ 1 := sin_le_one u
      have hsin0 : 0 ≤ sin u := sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith)
      have hp : (0.39804 : ℝ) * sin u * (1 + sin u) ≤ 0.79608 := by nlinarith
      have hp2 : (0.79608 : ℝ) ≤ 2 * u / π := by rw [le_div_iff₀ hpi]; nlinarith
      exact hp.trans hp2
    · rcases le_or_gt u 0.92 with h3 | h3
      · have hs := sin_interval_ten (x := 0.8) (by norm_num) (by norm_num)
        have hc := cos_interval_ten (x := 0.8) (by norm_num) (by norm_num)
        norm_num at hs hc
        refine dicut_case2_tangent (u₀ := 0.8) (lo := 0.59) (hi := 0.92)
          (s_hi := 717357 / 1000000) (c_lo := 696706 / 1000000) (c_hi := 696708 / 1000000)
          (by norm_num) (by linarith) hu0 hu h1.le h3 (by norm_num) (by norm_num)
          (by linarith [hs.2]) (by linarith [hc.1]) (by linarith [hc.2]) ?_ ?_ ?_
        all_goals rw [le_div_iff₀ hpi]; nlinarith
      · have hs := sin_interval_ten (x := 1) (by norm_num) (by norm_num)
        have hc := cos_interval_ten (x := 1) (by norm_num) (by norm_num)
        norm_num at hs hc
        refine dicut_case2_tangent (u₀ := 1) (lo := 0.92) (hi := 1.251)
          (s_hi := 841472 / 1000000) (c_lo := 540301 / 1000000) (c_hi := 540304 / 1000000)
          (by norm_num) (by linarith) hu0 hu h3.le h2.le (by norm_num) (by norm_num)
          (by linarith [hs.2]) (by linarith [hc.1]) (by linarith [hc.2]) ?_ ?_ ?_
        all_goals rw [le_div_iff₀ hpi]; nlinarith

/-- Case (2) of Lemma 7.3.2: `c = a + b` for `(a, b, c) ∈ DicutAngleSet`. -/
private theorem dicutObj_nonneg_of_add_eq {a b c : ℝ} (hmem : (a, b, c) ∈ DicutAngleSet)
    (heq : c = a + b) : 0 ≤ dicutObj (a, b, c) := by
  rw [mem_dicutAngleSet_iff] at hmem
  rcases hmem with ⟨h1, _, h3, _, _, h6, _⟩
  set x := (a + b) / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx : x ≤ π / 2 := by dsimp only [x]; linarith
  have htrig : 1 + cos a + cos b + cos (a + b) =
      2 * cos x * (cos x + cos ((a - b) / 2)) := by
    simpa [x] using one_add_cos_add_cos_add_cos_add a b
  have hcos_x : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hx⟩
  have hcos_ub : 1 + cos a + cos b + cos c ≤ 2 * cos x * (1 + cos x) := by
    rw [heq, htrig]
    have := cos_le_one ((a - b) / 2)
    nlinarith
  have hβ_lt : goemansWilliamsonDicutConstant ≤ 0.79608 := goemansWilliamsonDicutConstant_lt.le
  have hβ0 : 0 ≤ goemansWilliamsonDicutConstant := goemansWilliamsonDicutConstant_nonneg
  have hprod0 : 0 ≤ cos x * (1 + cos x) := mul_nonneg hcos_x (by linarith)
  have h2 := dicut_case2_u (u := π / 2 - x) (by linarith) (by linarith)
  rw [sin_pi_div_two_sub] at h2
  have hsum : (a + b + c) / (2 * π) = 2 * x / π := by
    rw [heq]
    dsimp only [x]
    ring
  dsimp only [dicutObj]
  rw [hsum]
  have hlin1 : 1 - 2 * x / π = 2 * (π / 2 - x) / π := by
    have := pi_ne_zero
    field_simp
  have hlin2 : goemansWilliamsonDicutConstant / 4 * (1 + cos a + cos b + cos c) ≤
      (0.39804 : ℝ) * cos x * (1 + cos x) := by
    calc goemansWilliamsonDicutConstant / 4 * (1 + cos a + cos b + cos c)
        ≤ goemansWilliamsonDicutConstant / 4 * (2 * cos x * (1 + cos x)) :=
          mul_le_mul_of_nonneg_left hcos_ub (by positivity)
      _ = (goemansWilliamsonDicutConstant / 2) * (cos x * (1 + cos x)) := by ring
      _ ≤ 0.39804 * (cos x * (1 + cos x)) := by nlinarith
      _ = 0.39804 * cos x * (1 + cos x) := by ring
  linarith

private theorem exists_shift_mem_dicutAngleSet {a b c : ℝ} (ha0 : 0 < a) (haπ : a < π)
    (hb0 : 0 ≤ b) (hbπ : b ≤ π) (hc0 : 0 ≤ c) (hcπ : c ≤ π)
    (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b) (h4 : a + b + c < 2 * π) :
    ∃ δ : ℝ, 0 < δ ∧ δ < π ∧ (a + δ, b, c) ∈ DicutAngleSet ∧ (a - δ, b, c) ∈ DicutAngleSet := by
  set δ := min (min (min a (π - a)) (min (b + c - a) (a + c - b)))
    (min (a + b - c) (min (2 * π - (a + b + c)) (π / 2)))
  have hδ0 : 0 < δ := by
    dsimp only [δ]
    simp only [lt_min_iff]
    refine ⟨⟨⟨ha0, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
      ⟨by linarith, ⟨by linarith, by linarith [pi_pos]⟩⟩⟩
  have hδπ : δ < π := by
    have : δ ≤ π / 2 := by
      dsimp only [δ]; exact min_le_of_right_le (min_le_of_right_le (min_le_right _ _))
    linarith [pi_pos]
  have hδ1 : δ ≤ a := by
    dsimp only [δ]; exact min_le_of_left_le (min_le_of_left_le (min_le_left _ _))
  have hδ2 : δ ≤ π - a := by
    dsimp only [δ]; exact min_le_of_left_le (min_le_of_left_le (min_le_right _ _))
  have hδ3 : δ ≤ b + c - a := by
    dsimp only [δ]; exact min_le_of_left_le (min_le_of_right_le (min_le_left _ _))
  have hδ4 : δ ≤ a + c - b := by
    dsimp only [δ]; exact min_le_of_left_le (min_le_of_right_le (min_le_right _ _))
  have hδ5 : δ ≤ a + b - c := by
    dsimp only [δ]; exact min_le_of_right_le (min_le_left _ _)
  have hδ6 : δ ≤ 2 * π - (a + b + c) := by
    dsimp only [δ]; exact min_le_of_right_le (min_le_of_right_le (min_le_left _ _))
  refine ⟨δ, hδ0, hδπ, ?_, ?_⟩ <;> rw [mem_dicutAngleSet_iff]
  · refine ⟨by linarith, by linarith, hb0, hbπ, hc0, hcπ, ?_, ?_, ?_, ?_⟩ <;> linarith
  · refine ⟨by linarith, by linarith, hb0, hbπ, hc0, hcπ, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem cos_nonneg_and_sin_eq_of_isMinOn {a b c : ℝ}
    (hmin : IsMinOn dicutObj DicutAngleSet (a, b, c))
    (ha0 : 0 < a) (haπ : a < π) (hb0 : 0 ≤ b) (hbπ : b ≤ π) (hc0 : 0 ≤ c) (hcπ : c ≤ π)
    (h1 : a < b + c) (h2 : b < a + c) (h3 : c < a + b) (h4 : a + b + c < 2 * π) :
    0 ≤ cos a ∧ sin a = 2 / (goemansWilliamsonDicutConstant * π) := by
  obtain ⟨δ, hδ0, hδπ, hplus, hminus⟩ :=
    exists_shift_mem_dicutAngleSet ha0 haπ hb0 hbπ hc0 hcπ h1 h2 h3 h4
  have hp : dicutObj (a, b, c) ≤ dicutObj (a + δ, b, c) := hmin hplus
  have hm : dicutObj (a, b, c) ≤ dicutObj (a - δ, b, c) := hmin hminus
  have hmid : dicutObj (a + δ, b, c) + dicutObj (a - δ, b, c) - 2 * dicutObj (a, b, c) =
      goemansWilliamsonDicutConstant / 2 * (1 - cos δ) * cos a := by
    simp only [dicutObj, cos_add, cos_sub]
    ring
  have hβpos : 0 < goemansWilliamsonDicutConstant :=
    (by norm_num : (0 : ℝ) < 0.79607).trans lt_goemansWilliamsonDicutConstant
  have hcosδ : 0 < 1 - cos δ := by
    have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hδπ.le hδ0
    rw [cos_zero] at this
    linarith
  have hcos_a : 0 ≤ cos a := by
    have hnn : 0 ≤ goemansWilliamsonDicutConstant / 2 * (1 - cos δ) * cos a := by linarith
    exact nonneg_of_mul_nonneg_right hnn (by positivity)
  rw [mem_dicutAngleSet_iff] at hplus hminus
  have hlocal : IsLocalMin (fun t => dicutObj (t, b, c)) a := by
    refine Filter.Eventually.mono
      (Ioo_mem_nhds (by linarith : a - δ < a) (by linarith : a < a + δ)) ?_
    intro t ht
    refine hmin ?_
    rw [mem_dicutAngleSet_iff]
    refine ⟨by linarith [ht.1, hminus.1], by linarith [ht.2, hplus.2.1],
      hb0, hbπ, hc0, hcπ, ?_, ?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2, hplus.1, hminus.1]
  have hd : HasDerivAt (fun t => dicutObj (t, b, c))
      (-(1 / (2 * π)) + goemansWilliamsonDicutConstant / 4 * sin a) a := by
    have hd1 : HasDerivAt (fun t => 1 - (t + b + c) / (2 * π)) (-(1 / (2 * π))) a := by
      have := ((hasDerivAt_id a).add_const b).add_const c |>.div_const (2 * π) |>.const_sub 1
      simpa using this
    have hd2 : HasDerivAt
        (fun t => goemansWilliamsonDicutConstant / 4 * (1 + cos t + cos b + cos c))
        (-(goemansWilliamsonDicutConstant / 4 * sin a)) a := by
      have := (((hasDerivAt_cos a).const_add 1).add_const (cos b)).add_const (cos c)
        |>.const_mul (goemansWilliamsonDicutConstant / 4)
      simpa [mul_neg] using this
    exact (hd1.sub hd2).congr_deriv (by ring)
  have hz := hlocal.hasDerivAt_eq_zero hd
  refine ⟨hcos_a, ?_⟩
  have hpi := pi_ne_zero
  have hβ0 := hβpos.ne'
  field_simp at hz ⊢
  linarith

/-- **Goemans–Williamson, Lemma 7.3.2.** On the spherical-triangle angle polytope `DicutAngleSet`,
`1 - (a + b + c) / (2π) ≥ (β / 4) · (1 + cos a + cos b + cos c)`
[GoemansWilliamson1995, Lemma 7.3.2]. -/
theorem goemansWilliamsonDicutConstant_mul_add_cos_le {a b c : ℝ}
    (hmem : (a, b, c) ∈ DicutAngleSet) :
    goemansWilliamsonDicutConstant / 4 * (1 + cos a + cos b + cos c) ≤
      1 - (a + b + c) / (2 * π) := by
  suffices h : 0 ≤ dicutObj (a, b, c) by
    dsimp only [dicutObj] at h
    linarith
  have hcont : Continuous dicutObj := by unfold dicutObj; fun_prop
  obtain ⟨⟨m1, m2, m3⟩, hm_mem, hm_min⟩ := isCompact_dicutAngleSet.exists_isMinOn
    ⟨(0, 0, 0), ⟨le_rfl, pi_pos.le, le_rfl, pi_pos.le, le_rfl, pi_pos.le,
      by norm_num, by norm_num, by norm_num, by linarith [pi_pos]⟩⟩ hcont.continuousOn
  refine le_trans ?_ (hm_min hmem)
  have hmem_m : (m1, m2, m3) ∈ DicutAngleSet := hm_mem
  rw [mem_dicutAngleSet_iff] at hm_mem
  rcases hm_mem with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  by_cases hsum : m1 + m2 + m3 = 2 * π
  · exact dicutObj_nonneg_of_sum_eq hmem_m hsum
  by_cases hc_eq : m3 = m1 + m2
  · exact dicutObj_nonneg_of_add_eq hmem_m hc_eq
  by_cases ha_eq : m1 = m2 + m3
  · rw [← dicutObj_perm13 m1 m2 m3]
    exact dicutObj_nonneg_of_add_eq (mem_dicutAngleSet_perm13 hmem_m) (by linarith)
  by_cases hb_eq : m2 = m1 + m3
  · rw [← dicutObj_perm12 m1 m2 m3, ← dicutObj_perm13 m2 m1 m3]
    exact dicutObj_nonneg_of_add_eq (mem_dicutAngleSet_perm13 (mem_dicutAngleSet_perm12 hmem_m))
      (by linarith)
  by_cases hm10 : m1 = 0
  · rw [hm10] at h8 h9
    exact dicutObj_nonneg_of_add_eq hmem_m (by linarith)
  by_cases hm20 : m2 = 0
  · rw [hm20] at h7 h9
    exact dicutObj_nonneg_of_add_eq hmem_m (by linarith)
  by_cases hm30 : m3 = 0
  · rw [hm30] at h7 h8
    rw [← dicutObj_perm13 m1 m2 m3]
    exact dicutObj_nonneg_of_add_eq (mem_dicutAngleSet_perm13 hmem_m) (by linarith)
  by_cases hm1π : m1 = π
  · exact dicutObj_nonneg_of_sum_eq hmem_m (by linarith)
  by_cases hm2π : m2 = π
  · exact dicutObj_nonneg_of_sum_eq hmem_m (by linarith)
  by_cases hm3π : m3 = π
  · exact dicutObj_nonneg_of_sum_eq hmem_m (by linarith)
  -- Interior point `(m1, m2, m3)`.
  have h1s : 0 < m1 := lt_of_le_of_ne h1 (Ne.symm hm10)
  have h2s : m1 < π := lt_of_le_of_ne h2 hm1π
  have h3s : 0 < m2 := lt_of_le_of_ne h3 (Ne.symm hm20)
  have h4s : m2 < π := lt_of_le_of_ne h4 hm2π
  have h5s : 0 < m3 := lt_of_le_of_ne h5 (Ne.symm hm30)
  have h6s : m3 < π := lt_of_le_of_ne h6 hm3π
  have h7s : m1 < m2 + m3 := lt_of_le_of_ne h7 ha_eq
  have h8s : m2 < m1 + m3 := lt_of_le_of_ne h8 hb_eq
  have h9s : m3 < m1 + m2 := lt_of_le_of_ne h9 hc_eq
  have h10s : m1 + m2 + m3 < 2 * π := lt_of_le_of_ne h10 hsum
  obtain ⟨hca, hsa⟩ := cos_nonneg_and_sin_eq_of_isMinOn hm_min h1s h2s h3 h4 h5 h6 h7s h8s h9s h10s
  have hm_min12 : IsMinOn dicutObj DicutAngleSet (m2, m1, m3) := fun q hq => by
    rw [dicutObj_perm12]
    exact hm_min hq
  obtain ⟨hcb, hsb⟩ := cos_nonneg_and_sin_eq_of_isMinOn hm_min12 h3s h4s h1 h2 h5 h6 h8s h7s
    (by linarith) (by linarith)
  have hm_min13 : IsMinOn dicutObj DicutAngleSet (m3, m2, m1) := fun q hq => by
    rw [dicutObj_perm13]
    exact hm_min hq
  obtain ⟨hcc, hsc⟩ := cos_nonneg_and_sin_eq_of_isMinOn hm_min13 h5s h6s h3 h4 h1 h2
    (by linarith) (by linarith) (by linarith) (by linarith)
  have le_pi2 : ∀ {t : ℝ}, 0 ≤ t → t ≤ π → 0 ≤ cos t → t ≤ π / 2 := by
    intro t ht0 htπ hct
    by_contra hlt
    push Not at hlt
    have := cos_lt_cos_of_nonneg_of_le_pi (by positivity) htπ hlt
    rw [cos_pi_div_two] at this
    linarith
  have ha_le : m1 ≤ π / 2 := le_pi2 h1 h2 hca
  have hb_le : m2 ≤ π / 2 := le_pi2 h3 h4 hcb
  have hc_le : m3 ≤ π / 2 := le_pi2 h5 h6 hcc
  have hab : m1 = m2 := strictMonoOn_sin.injOn ⟨by linarith [pi_pos], ha_le⟩
    ⟨by linarith [pi_pos], hb_le⟩ (hsa.trans hsb.symm)
  have hac : m1 = m3 := strictMonoOn_sin.injOn ⟨by linarith [pi_pos], ha_le⟩
    ⟨by linarith [pi_pos], hc_le⟩ (hsa.trans hsc.symm)
  rw [← hab, ← hac]
  have hdef := goemansWilliamsonDicutConstant_mul_one_add_three_cos_le h1
    (ha_le.trans_lt pi_div_two_lt_arccos_neg_third)
  have hpi := pi_ne_zero
  dsimp only [dicutObj]
  have hrew1 : 1 - (m1 + m1 + m1) / (2 * π) = (2 / π * (2 * π - 3 * m1)) / 4 := by
    field_simp
    ring
  have hrew2 : goemansWilliamsonDicutConstant / 4 * (1 + cos m1 + cos m1 + cos m1) =
      (goemansWilliamsonDicutConstant * (1 + 3 * cos m1)) / 4 := by
    ring
  rw [hrew1, hrew2]
  linarith

end Real
