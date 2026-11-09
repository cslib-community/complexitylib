/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Superquadratic sensitivity separation: profile arithmetic

Arithmetic reducing the four raw recurrences for the side sensitivities `s₀, s₁` and the joint
sensitivities `j₀, j₁` of consecutive recursive levels to two scalar recurrences. Each pair is
normalized by `normalizedMax`, which divides the zero-side value by `M ^ n` and the one-side value
by `M ^ (n + 1)`; the normalized side and joint maxima `u, v` then satisfy
`u' ≤ (1 + ε) * u + 3 * v` and `v' ≤ ε * u + 3 * v`.

## Main definitions

* `normalizedMax`: the maximum `max (s₀ / M ^ n) (s₁ / M ^ (n + 1))`.

## Main results

* `normalizedMax_le`: `normalizedMax M n s₀ s₁ ≤ u` whenever `s₀ ≤ u * M ^ n` and
  `s₁ ≤ u * M ^ (n + 1)`.
* `raw_profiles_step`: the one-step bound for the four raw recurrences in unnormalized form.
* `normalized_profiles_step`: the four raw recurrences imply the two normalized scalar recurrences.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/ProfileArithmetic.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- Maximum of the two sensitivity bounds after their level-dependent normalization. -/
def normalizedMax (M : ℝ) (n : ℕ) (s₀ s₁ : ℝ) : ℝ :=
  max (s₀ / M ^ n) (s₁ / M ^ (n + 1))

/-- For `0 < M` and `0 ≤ s₀`, the normalized maximum is nonnegative. -/
private theorem normalizedMax_nonneg {M s₀ s₁ : ℝ} {n : ℕ}
    (hM : 0 < M) (hs₀ : 0 ≤ s₀) : 0 ≤ normalizedMax M n s₀ s₁ :=
  (div_nonneg hs₀ (pow_pos hM n).le).trans (le_max_left _ _)

/-- For `0 < M`, `s₀ ≤ normalizedMax M n s₀ s₁ * M ^ n`. -/
theorem le_normalizedMax_zero {M s₀ s₁ : ℝ} {n : ℕ} (hM : 0 < M) :
    s₀ ≤ normalizedMax M n s₀ s₁ * M ^ n :=
  (div_le_iff₀ (pow_pos hM n)).mp (le_max_left _ _)

/-- For `0 < M`, `s₁ ≤ normalizedMax M n s₀ s₁ * M ^ (n + 1)`. -/
theorem le_normalizedMax_one {M s₀ s₁ : ℝ} {n : ℕ} (hM : 0 < M) :
    s₁ ≤ normalizedMax M n s₀ s₁ * M ^ (n + 1) :=
  (div_le_iff₀ (pow_pos hM (n + 1))).mp (le_max_right _ _)

/-- For `0 < M`, if `s₀ ≤ u * M ^ n` and `s₁ ≤ u * M ^ (n + 1)`, then
`normalizedMax M n s₀ s₁ ≤ u`. -/
theorem normalizedMax_le {M s₀ s₁ u : ℝ} {n : ℕ} (hM : 0 < M)
    (h₀ : s₀ ≤ u * M ^ n) (h₁ : s₁ ≤ u * M ^ (n + 1)) :
    normalizedMax M n s₀ s₁ ≤ u :=
  max_le ((div_le_iff₀ (pow_pos hM n)).mpr h₀)
    ((div_le_iff₀ (pow_pos hM (n + 1))).mpr h₁)

/-- Unnormalized one-step bound: suppose `s₀ ≤ u * p`, `s₁ ≤ u * (p * M)`, `j₀ ≤ v * p`,
`j₁ ≤ v * (p * M)`, `r ≤ ε * M` and `16 ≤ ε * M`, and that the primed quantities satisfy the four
raw recurrences. Then `s₀'` and `s₁'` are at most `((1 + ε) * u + 3 * v)` times `p * M` and
`p * M * M` respectively, and `j₀'` and `j₁'` are at most `(ε * u + 3 * v)` times `p * M` and
`p * M * M` respectively. -/
theorem raw_profiles_step {M r ε u v p : ℝ}
    (hM : 0 < M) (hp : 0 ≤ p) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : 0 ≤ r) (hεr : r ≤ ε * M) (hεt : 16 ≤ ε * M)
    {s₀ s₁ j₀ j₁ s₀' s₁' j₀' j₁' : ℝ}
    (hs₀ : s₀ ≤ u * p) (hs₁ : s₁ ≤ u * (p * M))
    (hj₀ : j₀ ≤ v * p) (hj₁ : j₁ ≤ v * (p * M))
    (hS₀ : s₀' ≤ 16 * s₀ + s₁ + 3 * j₁)
    (hS₁ : s₁' ≤ M ^ 2 * s₀ + r * s₁)
    (hJ₀ : j₀' ≤ 16 * s₀ + 3 * j₁)
    (hJ₁ : j₁' ≤ M ^ 2 * j₀ + r * s₁) :
    s₀' ≤ ((1 + ε) * u + 3 * v) * (p * M) ∧
    s₁' ≤ ((1 + ε) * u + 3 * v) * (p * M * M) ∧
    j₀' ≤ (ε * u + 3 * v) * (p * M) ∧
    j₁' ≤ (ε * u + 3 * v) * (p * M * M) := by
  have hup : 0 ≤ u * p := mul_nonneg hu hp
  have hupM : 0 ≤ u * (p * M) := mul_nonneg hu (mul_nonneg hp hM.le)
  have hvpMM : 0 ≤ v * (p * M * M) := by positivity
  have ht := mul_le_mul_of_nonneg_right hεt hup
  have hr' := mul_le_mul_of_nonneg_right hεr hupM
  have a₀ := mul_le_mul_of_nonneg_left hs₀ (show (0 : ℝ) ≤ 16 by norm_num)
  have a₁ := mul_le_mul_of_nonneg_left hs₀ (sq_nonneg M)
  have b₀ := mul_le_mul_of_nonneg_left hj₀ (sq_nonneg M)
  have b₁ := mul_le_mul_of_nonneg_left hj₁ (show (0 : ℝ) ≤ 3 by norm_num)
  have c₁ := mul_le_mul_of_nonneg_left hs₁ hr
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- If `r / M ≤ ε`, `16 / M ≤ ε`, `s₀, j₀ ≥ 0` and the primed quantities satisfy the four raw
recurrences, then the normalized side maximum at level `n + 1` is at most `(1 + ε) * u + 3 * v` and
the normalized joint maximum at most `ε * u + 3 * v`, where `u = normalizedMax M n s₀ s₁` and
`v = normalizedMax M n j₀ j₁`. -/
theorem normalized_profiles_step {M r ε : ℝ} {n : ℕ}
    (hM : 0 < M) (hr : 0 ≤ r) (hεr : r / M ≤ ε) (hεt : 16 / M ≤ ε)
    {s₀ s₁ j₀ j₁ s₀' s₁' j₀' j₁' : ℝ} (hs₀ : 0 ≤ s₀) (hj₀ : 0 ≤ j₀)
    (hS₀ : s₀' ≤ 16 * s₀ + s₁ + 3 * j₁)
    (hS₁ : s₁' ≤ M ^ 2 * s₀ + r * s₁)
    (hJ₀ : j₀' ≤ 16 * s₀ + 3 * j₁)
    (hJ₁ : j₁' ≤ M ^ 2 * j₀ + r * s₁) :
    normalizedMax M (n + 1) s₀' s₁' ≤
      (1 + ε) * normalizedMax M n s₀ s₁ + 3 * normalizedMax M n j₀ j₁ ∧
    normalizedMax M (n + 1) j₀' j₁' ≤
      ε * normalizedMax M n s₀ s₁ + 3 * normalizedMax M n j₀ j₁ := by
  have hs₁b := le_normalizedMax_one (s₀ := s₀) (s₁ := s₁) (n := n) hM
  have hj₁b := le_normalizedMax_one (s₀ := j₀) (s₁ := j₁) (n := n) hM
  rw [pow_succ] at hs₁b hj₁b
  obtain ⟨a, b, c, d⟩ := raw_profiles_step hM (pow_pos hM n).le
    (normalizedMax_nonneg hM hs₀) (normalizedMax_nonneg hM hj₀) hr
    ((div_le_iff₀ hM).mp hεr) ((div_le_iff₀ hM).mp hεt)
    (le_normalizedMax_zero hM) hs₁b (le_normalizedMax_zero hM) hj₁b
    hS₀ hS₁ hJ₀ hJ₁
  constructor
  · apply normalizedMax_le hM <;> simpa only [pow_succ] using (by assumption)
  · apply normalizedMax_le hM <;> simpa only [pow_succ] using (by assumption)

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
