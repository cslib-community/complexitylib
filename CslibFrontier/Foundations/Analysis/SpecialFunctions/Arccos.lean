/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean` and
-- `Mathlib/Analysis/Convex/SpecificFunctions/Deriv.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The half-angle formula and concavity of `arccos`

For `-1 < x`, the angle `θ = arccos x` satisfies `tan (θ / 2) = √(1 - x) / √(1 + x)`, so
`arccos x = 2 arctan (√(1 - x) / √(1 + x))` (`Real.arccos_eq_two_mul_arctan`). The derivative
`-1 / √(1 - x ^ 2)` of `arccos` is strictly decreasing on `(0, 1)`, so `arccos` is strictly
concave on `[0, 1]` (`strictConcaveOn_arccos_Icc`). By Jensen's inequality, arguments in `[0, 1]`
with average at least `x₀` have `arccos`-sum at most their number times `arccos x₀`
(`Real.sum_arccos_le_card_mul_arccos`).

## Main results

* `Real.arccos_eq_two_mul_arctan`: the half-angle formula for `arccos`.
* `strictConcaveOn_arccos_Icc`: `arccos` is strictly concave on `[0, 1]`.
* `Real.sum_arccos_le_card_mul_arccos`: Jensen's inequality for `arccos` on `[0, 1]`.
-/

public section

open Set

namespace Real

/-- **The half-angle formula for `arccos`**: `arccos x = 2 arctan (√(1 - x) / √(1 + x))` for
`-1 < x`. For `1 ≤ x` both sides vanish. -/
theorem arccos_eq_two_mul_arctan {x : ℝ} (hx : -1 < x) :
    arccos x = 2 * arctan (√(1 - x) / √(1 + x)) := by
  rcases le_or_gt 1 x with h1 | h1
  · rw [arccos_of_one_le h1, sqrt_eq_zero_of_nonpos (by linarith), zero_div, arctan_zero,
      mul_zero]
  set y := √(1 - x) / √(1 + x) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy2 : y ^ 2 = (1 - x) / (1 + x) := by
    rw [hy, div_pow, sq_sqrt (by linarith), sq_sqrt (by linarith)]
  have hcos : cos (2 * arctan y) = x := by
    have : 0 < 1 + x := by linarith
    rw [cos_two_mul, cos_sq_arctan, hy2]
    field_simp
    ring
  rw [← hcos, arccos_cos (by positivity [arctan_nonneg.2 hy0])
    (by linarith [arctan_lt_pi_div_two y])]

end Real

open Real in
/-- `arccos` is strictly concave on `[0, 1]`: its derivative `-1 / √(1 - x ^ 2)` is strictly
decreasing on `(0, 1)`. -/
theorem strictConcaveOn_arccos_Icc : StrictConcaveOn ℝ (Icc 0 1) arccos := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 1) continuous_arccos.continuousOn ?_
  rw [interior_Icc, deriv_arccos]
  intro a ha b hb hab
  have hb' : 0 < 1 - b ^ 2 := by nlinarith [hb.1, hb.2]
  exact neg_lt_neg (one_div_lt_one_div_of_lt (sqrt_pos.2 hb')
    (sqrt_lt_sqrt hb'.le (by nlinarith [ha.1])))

namespace Real

/-- **Jensen's inequality for `arccos`.** If finitely many arguments in `[0, 1]` have average at
least `x₀`, their `arccos`-sum is at most their number times `arccos x₀`. -/
theorem sum_arccos_le_card_mul_arccos {ι : Type*} (s : Finset ι) {x : ι → ℝ} {x₀ : ℝ}
    (hx : ∀ i ∈ s, x i ∈ Icc 0 1) (hsum : s.card * x₀ ≤ ∑ i ∈ s, x i) :
    ∑ i ∈ s, arccos (x i) ≤ s.card * arccos x₀ := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
  have h := strictConcaveOn_arccos_Icc.concaveOn.le_map_sum (t := s)
    (w := fun _ => (s.card : ℝ)⁻¹) (p := x) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hn.ne']) hx
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have hmono : arccos ((s.card : ℝ)⁻¹ * ∑ i ∈ s, x i) ≤ arccos x₀ :=
    arccos_le_arccos ((le_inv_mul_iff₀ hn).2 hsum)
  exact (inv_mul_le_iff₀ hn).1 (h.trans hmono)

end Real
