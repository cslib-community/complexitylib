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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Goemans–Williamson constant

The Goemans–Williamson constant is
`α = min_{0 < θ ≤ π} (2 / π) · θ / (1 - cos θ)`
[GoemansWilliamson1995, Section 3]. It is the approximation ratio of random-hyperplane rounding
for MAX-CUT: the probability `arccos y / π` that a uniformly random hyperplane separates two unit
vectors with inner product `y` is at least `α` times the contribution `(1 - y) / 2` of the pair to
the semidefinite relaxation [GoemansWilliamson1995, Lemma 3.4]. Its value is
`α ≈ 0.878567`; Goemans and Williamson show `α > 0.87856` [GoemansWilliamson1995, Lemma 3.5].

Here `α` is `Real.goemansWilliamsonConstant`, defined as an infimum over `θ ∈ (0, π]`. The bounds
`0.87856 < α < 0.87857` follow the source's proof. On `(0, π / 2]` the ratio is at least `1`,
because `1 - cos θ ≤ 2θ / π` there. On `[π / 2, π]`, the concave function `1 - cos θ` lies below
its tangent line at `θ₀ = π - 0.810474 ≈ 2.331119`, and that line lies below `θ · sin θ₀`. The
needed values of `cos` and `sin` at `0.810474` come from degree-ten Taylor bounds
(`Real.cos_bound_ten`, `Real.sin_bound_ten`) and the six-digit bounds on `π` in Mathlib, with
explicit rational arithmetic.

## Main definitions

* `Real.goemansWilliamsonConstant`: the constant `α`.

## Main results

* `Real.goemansWilliamsonConstant_mul_one_sub_cos_le`: `α · (1 - cos θ) ≤ (2 / π) · θ` for
  `0 ≤ θ ≤ π`.
* `Real.goemansWilliamsonConstant_mul_le_arccos`: `α · (1 - y) / 2 ≤ arccos y / π` for
  `-1 ≤ y ≤ 1` [GoemansWilliamson1995, Lemma 3.4].
* `Real.lt_goemansWilliamsonConstant`: `0.87856 < α` [GoemansWilliamson1995, Lemma 3.5].
* `Real.goemansWilliamsonConstant_lt`: `α < 0.87857`, so `α = 0.87856…` to five decimal digits.

## References

* [GoemansWilliamson1995]
-/

public section

open Set

namespace Real

/-- `1 - cos θ` is positive on `(0, π]`. -/
private theorem one_sub_cos_pos_of_mem_Ioc {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ π) :
    0 < 1 - cos θ := by
  have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ h0
  rw [cos_zero] at this
  linarith

/-- **The Goemans–Williamson constant** `α = inf_{0 < θ ≤ π} (2 / π) · θ / (1 - cos θ)`
[GoemansWilliamson1995, Section 3]. The infimum is attained near `θ ≈ 2.33112`, where
`α ≈ 0.878567`. -/
noncomputable def goemansWilliamsonConstant : ℝ :=
  ⨅ θ : Ioc (0 : ℝ) π, 2 / π * θ / (1 - cos θ)

private theorem gw_term_nonneg (θ : Ioc (0 : ℝ) π) : 0 ≤ 2 / π * (θ : ℝ) / (1 - cos θ) :=
  div_nonneg (mul_nonneg (div_nonneg zero_le_two pi_pos.le) θ.2.1.le)
    (one_sub_cos_pos_of_mem_Ioc θ.2.1 θ.2.2).le

private theorem gw_bddBelow :
    BddBelow (range fun θ : Ioc (0 : ℝ) π => 2 / π * (θ : ℝ) / (1 - cos θ)) :=
  ⟨0, by rintro _ ⟨θ, rfl⟩; exact gw_term_nonneg θ⟩

/-- The Goemans–Williamson constant is nonnegative. -/
theorem goemansWilliamsonConstant_nonneg : 0 ≤ goemansWilliamsonConstant :=
  Real.iInf_nonneg gw_term_nonneg

/-- The defining inequality of the Goemans–Williamson constant, multiplied out:
`α · (1 - cos θ) ≤ (2 / π) · θ` for `0 ≤ θ ≤ π`. -/
theorem goemansWilliamsonConstant_mul_one_sub_cos_le {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    goemansWilliamsonConstant * (1 - cos θ) ≤ 2 / π * θ := by
  rcases h0.eq_or_lt with rfl | h0
  · simp
  rw [← le_div_iff₀ (one_sub_cos_pos_of_mem_Ioc h0 hπ)]
  exact ciInf_le gw_bddBelow (⟨θ, h0, hπ⟩ : Ioc (0 : ℝ) π)

/-- **Goemans–Williamson, Lemma 3.4.** For `-1 ≤ y ≤ 1`,
`α · (1 - y) / 2 ≤ arccos y / π`: a random hyperplane separates two unit vectors with inner
product `y` with probability at least `α` times their contribution to the MAX-CUT semidefinite
relaxation [GoemansWilliamson1995, Lemma 3.4]. -/
theorem goemansWilliamsonConstant_mul_le_arccos {y : ℝ} (hy : -1 ≤ y) (hy1 : y ≤ 1) :
    goemansWilliamsonConstant * ((1 - y) / 2) ≤ arccos y / π := by
  have h := goemansWilliamsonConstant_mul_one_sub_cos_le (arccos_nonneg y) (arccos_le_pi y)
  rw [cos_arccos hy hy1] at h
  have := pi_pos
  rw [le_div_iff₀ this]
  field_simp at h ⊢
  linarith

/-- Rational bounds on `cos 0.810474`, from the degree-eight Taylor polynomial. -/
private theorem cos_x0_bounds :
    (3445775199 / 5000000000 : ℝ) ≤ cos (810474 / 1000000) ∧
      cos (810474 / 1000000) ≤ 344577557 / 500000000 := by
  have h := cos_bound_ten (x := 810474 / 1000000) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 810474 / 1000000), abs_le] at h
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]

/-- Rational bounds on `sin 0.810474`, from the degree-nine Taylor polynomial. -/
private theorem sin_x0_bounds :
    (3623069403 / 5000000000 : ℝ) ≤ sin (810474 / 1000000) ∧
      sin (810474 / 1000000) ≤ 1811534887 / 2500000000 := by
  have h := sin_bound_ten (x := 810474 / 1000000) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 810474 / 1000000), abs_le] at h
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]

/-- The pointwise form of Lemma 3.5 with the slightly larger constant `0.878562`: on `(0, π / 2]`
use `1 - cos θ ≤ 2θ / π`; on `[π / 2, π]` use the tangent line of `1 - cos` at
`θ₀ = π - 0.810474`, which has negative intercept, so `1 - cos θ ≤ θ · sin θ₀`. -/
private theorem gw_lower_aux {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ π) :
    (878562 / 1000000 : ℝ) * (1 - cos θ) ≤ 2 / π * θ := by
  have hpi := pi_pos
  rcases le_or_gt θ (π / 2) with hθ | hθ
  · have := one_sub_mul_le_cos h0.le hθ
    have h2 : 0 ≤ 2 / π * θ := by positivity
    nlinarith
  · obtain ⟨hc1, hc2⟩ := cos_x0_bounds
    obtain ⟨hs1, hs2⟩ := sin_x0_bounds
    generalize hx : (810474 / 1000000 : ℝ) = x₀ at hc1 hc2 hs1 hs2
    have hplo := pi_gt_d6
    have hphi := pi_lt_d6
    norm_num at hplo hphi
    have ht := cos_le_cos_sub_sin_mul (x := π - θ) (x₀ := x₀)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    rw [cos_pi_sub] at ht
    have hs0 : 0 ≤ sin x₀ := le_trans (by norm_num) hs1
    -- the tangent line at `π - x₀` has negative intercept
    have hK : 1 + cos x₀ - (π - x₀) * sin x₀ ≤ 0 := by
      have := mul_le_mul (show (3141592 / 1000000 : ℝ) - x₀ ≤ π - x₀ by linarith) hs1
        (by norm_num) (by linarith)
      linarith
    have h1 : 1 - cos θ ≤ θ * sin x₀ := by nlinarith
    have hb : (878562 / 1000000 : ℝ) * π * sin x₀ ≤ 2 := by
      have := mul_le_mul (show (878562 / 1000000 : ℝ) * π ≤ 878562 / 1000000 * 3141593 / 1000000
        by linarith) hs2 hs0 (by positivity)
      linarith
    rw [show 2 / π * θ = 2 * θ / π by ring, le_div_iff₀ hpi]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 878562 / 1000000 * π),
      mul_le_mul_of_nonneg_left hb h0.le]

/-- **Goemans–Williamson, Lemma 3.5.** The Goemans–Williamson constant exceeds `0.87856`
[GoemansWilliamson1995, Lemma 3.5]. -/
theorem lt_goemansWilliamsonConstant : (0.87856 : ℝ) < goemansWilliamsonConstant := by
  have : Nonempty (Ioc (0 : ℝ) π) := ⟨⟨π, pi_pos, le_rfl⟩⟩
  refine lt_of_lt_of_le (by norm_num : (0.87856 : ℝ) < 878562 / 1000000) ?_
  refine le_ciInf fun θ => ?_
  rw [le_div_iff₀ (one_sub_cos_pos_of_mem_Ioc θ.2.1 θ.2.2)]
  exact gw_lower_aux θ.2.1 θ.2.2

/-- The Goemans–Williamson constant is below `0.87857`, witnessed by `θ = π - 0.810474`. With
`Real.lt_goemansWilliamsonConstant`, this pins down the first five decimal digits. -/
theorem goemansWilliamsonConstant_lt : goemansWilliamsonConstant < 0.87857 := by
  have hplo := pi_gt_d6
  have hphi := pi_lt_d6
  norm_num at hplo hphi
  have hpi := pi_pos
  obtain ⟨hc1, hc2⟩ := cos_x0_bounds
  generalize hx : (810474 / 1000000 : ℝ) = x₀ at hc1 hc2
  have h0 : 0 < π - x₀ := by linarith
  have h1 : π - x₀ ≤ π := by linarith
  refine lt_of_le_of_lt (ciInf_le gw_bddBelow (⟨π - x₀, h0, h1⟩ : Ioc (0 : ℝ) π)) ?_
  simp only [cos_pi_sub]
  rw [div_lt_iff₀ (by linarith), show 2 / π * (π - x₀) = 2 * (π - x₀) / π by ring,
    div_lt_iff₀ hpi]
  norm_num
  nlinarith

end Real
