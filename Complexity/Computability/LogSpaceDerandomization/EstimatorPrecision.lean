/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Precision pays for scale and source changes

This module proves the precision calculation in [OpenAI2026LogSpace, Section 7.4, p. 38].
A task with budget `M`, rank `i`, endpoint rate `a`, and source rate `u` has precision
`M / K + (log₂ a + log₂ u) / 2 - A * i`. This is the source's formula with the two logarithms of
inverse rates rewritten. Subtracting two task precisions gives the exact budget, rate, and rank
contributions; budget-zero tasks with rates in `(0, 1]` are inactive when `A ≥ 0`.

For a moment exponent `s > 2`, the norm costs of coarse and fine bins have exponents `1/s` and
`(s-1)/s`. The half-logarithmic precision weight leaves the positive margin `1/2 - 1/s` in both
directions. The same weight pays for source release when the child source rate is at least the
parent source rate. In particular the margin is `1/4` for the fourth-moment route of issue #1721,
and `3/8` for the pinned preprint's exponent eight.

The theorems establish the scalar precision and scale/domain compensation calculation. They do
not choose the global precision constant or walk length, construct an additive sampler, or assert
its recursive error bound.

## Main definitions

* `Cslib.LogSpaceEstimation.precision`: implicit task precision.
* `Cslib.LogSpaceEstimation.scaleMargin`: the margin left by the half-logarithmic weight.
* `Cslib.LogSpaceEstimation.binNormCost`: the coarse/fine norm cost at a logarithmic scale offset.

## Main results

* `Cslib.LogSpaceEstimation.precision_child_sub`: the exact child-precision difference.
* `Cslib.LogSpaceEstimation.precision_zero_nonpos`: the inactive zero-budget case.
* `Cslib.LogSpaceEstimation.binNormCost_mul_accuracy`: geometric scale compensation.
* `Cslib.LogSpaceEstimation.source_cost_mul_accuracy_le_one`: source-domain compensation.
* `Cslib.LogSpaceEstimation.child_cost_mul_accuracy_le`: compensation for an actual child task.
* `Cslib.LogSpaceEstimation.child_cost_mul_accuracy_le_of_rate_le`: the correction-child case.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 7.4, p. 38, equations (7.8)–(7.10), labelled `est-precision`, `est-child-precision`,
  and `est-scale-slack`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.LogSpaceEstimation

/-- Implicit precision at budget `M` and dependency rank `i`. Rates are positive in applications. -/
@[expose] noncomputable def precision (K A : ℝ) (M i : ℕ) (a u : ℝ) : ℝ :=
  M / K + (Real.logb 2 a + Real.logb 2 u) / 2 - A * i

/-- The equivalent convention written using inverse rates in the source. -/
theorem precision_eq_inv_rates (K A : ℝ) (M i : ℕ) (a u : ℝ) :
    precision K A M i a u = M / K - Real.logb 2 (1 / a) / 2 -
      Real.logb 2 (1 / u) / 2 - A * i := by
  simp only [precision, one_div, Real.logb_inv]
  ring

/-- Dyadic rates give the affine formula without logarithms. The offsets can be real, so this
also covers exact powers of two outside the discrete hierarchy. -/
theorem precision_dyadic_rates (K A : ℝ) (M i : ℕ) (α υ : ℝ) :
    precision K A M i ((2 : ℝ) ^ (-α)) ((2 : ℝ) ^ (-υ)) =
      M / K - (α + υ) / 2 - A * i := by
  simp only [precision, Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  ring

/-- The exact child-precision identity, before imposing any rank decrease or budget cutoff. -/
theorem precision_child_sub (K A : ℝ) (M m i i' : ℕ) {a a' u u' : ℝ}
    (ha : 0 < a) (ha' : 0 < a') (hu : 0 < u) (hu' : 0 < u') :
    precision K A m i' a' u' - precision K A M i a u =
      -((M : ℝ) - m) / K + Real.logb 2 (a' / a) / 2 + Real.logb 2 (u' / u) / 2 +
        A * ((i : ℝ) - i') := by
  rw [Real.logb_div ha'.ne' ha.ne', Real.logb_div hu'.ne' hu.ne']
  unfold precision
  ring

/-- Increasing the integer budget cannot decrease precision for a positive precision constant. -/
theorem precision_mono_budget {K A a u : ℝ} (hK : 0 < K) (i : ℕ) :
    Monotone fun M => precision K A M i a u := by
  intro M m hMm
  have hdiv := div_le_div_of_nonneg_right (show (M : ℝ) ≤ m by exact_mod_cast hMm) hK.le
  unfold precision
  linarith

/-- Budget-zero tasks at rates in `(0, 1]` are inactive. -/
theorem precision_zero_nonpos {K A a u : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (ha1 : a ≤ 1)
    (hu : 0 < u) (hu1 : u ≤ 1) (i : ℕ) : precision K A 0 i a u ≤ 0 := by
  have hla := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) ha.le ha1
  have hlu := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hu.le hu1
  have hi : 0 ≤ A * (i : ℝ) := mul_nonneg hA (Nat.cast_nonneg _)
  simp only [precision, Nat.cast_zero, zero_div, zero_add]
  linarith

/-- The geometric margin from the half-logarithmic precision weight at moment exponent `s`. -/
@[expose] noncomputable def scaleMargin (s : ℝ) : ℝ := 1 / 2 - 1 / s

theorem scaleMargin_pos {s : ℝ} (hs : 2 < s) : 0 < scaleMargin s := by
  have hs0 : 0 < s := by linarith
  unfold scaleMargin
  apply sub_pos.mpr
  apply (div_lt_iff₀ hs0).2
  linarith

@[simp]
theorem scaleMargin_four : scaleMargin 4 = 1 / 4 := by norm_num [scaleMargin]

@[simp]
theorem scaleMargin_eight : scaleMargin 8 = 3 / 8 := by norm_num [scaleMargin]

/-- Norm cost for a bin with rate ratio `2 ^ h`: coarse exponent `1/s`, fine exponent `(s-1)/s`.
This names the costs supplied by the separate scale/domain norm comparisons. -/
@[expose] noncomputable def binNormCost (s h : ℝ) : ℝ :=
  (2 : ℝ) ^ (if 0 ≤ h then h / s else (s - 1) * h / s)

theorem binNormCost_pos (s h : ℝ) : 0 < binNormCost s h :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The same positive margin controls both coarse and fine scales. This is an exact identity. -/
theorem binNormCost_mul_accuracy {s : ℝ} (hs : s ≠ 0) (h : ℝ) :
    binNormCost s h * (2 : ℝ) ^ (-h / 2) = (2 : ℝ) ^ (-scaleMargin s * |h|) := by
  rw [binNormCost, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  split_ifs with hh
  · rw [abs_of_nonneg hh]
    unfold scaleMargin
    ring
  · rw [abs_of_neg (lt_of_not_ge hh)]
    unfold scaleMargin
    field_simp
    ring

/-- The half-logarithmic source precision weight cancels more than the source-release cost. -/
theorem source_cost_mul_accuracy {s r : ℝ} (hr : 0 < r) :
    r ^ (1 / s) * r ^ (-(1 / 2 : ℝ)) = r ^ (-scaleMargin s) := by
  rw [← Real.rpow_add hr]
  congr 1
  unfold scaleMargin
  ring

/-- Resetting the source to a broader rate costs at most one after its precision gain, for every
moment exponent strictly above two. -/
theorem source_cost_mul_accuracy_le_one {s r : ℝ} (hs : 2 < s) (hr : 1 ≤ r) :
    r ^ (1 / s) * r ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  rw [source_cost_mul_accuracy (lt_of_lt_of_le zero_lt_one hr)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hr (neg_nonpos.mpr (scaleMargin_pos hs).le)

/-- The scale cost, source cost and actual child accuracy split into the parent accuracy, the
budget/rank payment and two explicit geometric margins. This identity uses no independence or
probabilistic assumptions. -/
theorem child_cost_mul_accuracy {s K A a a' u u' : ℝ} (hs : s ≠ 0)
    (M m i i' : ℕ) (ha : 0 < a) (ha' : 0 < a') (hu : 0 < u) (hu' : 0 < u') :
    binNormCost s (Real.logb 2 (a' / a)) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / s) *
        (2 : ℝ) ^ (-precision K A m i' a' u') =
      (2 : ℝ) ^ (-precision K A M i a u + ((M : ℝ) - m) / K -
        A * ((i : ℝ) - i')) *
        (2 : ℝ) ^ (-scaleMargin s * |Real.logb 2 (a' / a)|) *
        (2 : ℝ) ^ (-scaleMargin s * Real.logb 2 (u' / u)) := by
  have hp := precision_child_sub K A M m i i' ha ha' hu hu'
  have he : -precision K A m i' a' u' =
      -Real.logb 2 (a' / a) / 2 + (-Real.logb 2 (u' / u) / 2 +
        (-precision K A M i a u + ((M : ℝ) - m) / K - A * ((i : ℝ) - i'))) := by
    simp only [neg_div] at hp ⊢
    linarith
  rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hg : (2 : ℝ) ^ (Real.logb 2 (u' / u) / s) *
      (2 : ℝ) ^ (-Real.logb 2 (u' / u) / 2) =
      (2 : ℝ) ^ (-scaleMargin s * Real.logb 2 (u' / u)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    unfold scaleMargin
    ring
  calc
    _ = (binNormCost s (Real.logb 2 (a' / a)) * (2 : ℝ) ^ (-Real.logb 2 (a' / a) / 2)) *
        ((2 : ℝ) ^ (Real.logb 2 (u' / u) / s) *
          (2 : ℝ) ^ (-Real.logb 2 (u' / u) / 2)) *
        (2 : ℝ) ^ (-precision K A M i a u + ((M : ℝ) - m) / K -
          A * ((i : ℝ) - i')) := by ring
    _ = _ := by rw [binNormCost_mul_accuracy hs, hg]; ring

/-- A dependency rank decrease pays one rank unit. Broadening the source costs no additional
factor, and both directions of the endpoint scale retain the positive geometric margin. -/
theorem child_cost_mul_accuracy_le {s K A a a' u u' : ℝ} (hs : 2 < s) (hA : 0 ≤ A)
    (M m i i' : ℕ) (hi : i' + 1 ≤ i) (ha : 0 < a) (ha' : 0 < a')
    (hu : 0 < u) (huu' : u ≤ u') :
    binNormCost s (Real.logb 2 (a' / a)) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / s) *
        (2 : ℝ) ^ (-precision K A m i' a' u') ≤
      (2 : ℝ) ^ (-precision K A M i a u - A + ((M : ℝ) - m) / K) *
        (2 : ℝ) ^ (-scaleMargin s * |Real.logb 2 (a' / a)|) := by
  have hs0 : 0 < s := by linarith
  have hi' : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hi
  have hAi : A ≤ A * ((i : ℝ) - i') := by nlinarith
  have hlog : 0 ≤ Real.logb 2 (u' / u) :=
    Real.logb_nonneg (by norm_num) ((le_div_iff₀ hu).2 (by simpa using huu'))
  have hsource : (2 : ℝ) ^ (-scaleMargin s * Real.logb 2 (u' / u)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (scaleMargin_pos hs).le) hlog)
  have hrank : (2 : ℝ) ^ (-precision K A M i a u + ((M : ℝ) - m) / K -
      A * ((i : ℝ) - i')) ≤
      (2 : ℝ) ^ (-precision K A M i a u - A + ((M : ℝ) - m) / K) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [child_cost_mul_accuracy hs0.ne' M m i i' ha ha' hu (hu.trans_le huu')]
  calc
    _ ≤ (2 : ℝ) ^ (-precision K A M i a u + ((M : ℝ) - m) / K -
          A * ((i : ℝ) - i')) *
        (2 : ℝ) ^ (-scaleMargin s * |Real.logb 2 (a' / a)|) := by
      exact mul_le_of_le_one_right (by positivity) hsource
    _ ≤ _ := mul_le_mul_of_nonneg_right hrank (by positivity)

/-- A child rate only needs to dominate a fixed multiple of the bin rate. The resulting constant
is exactly `2 ^ (-log₂ c / 2)`; the geometric decay is still measured at the actual bin offset.
This is the form needed when a correction child uses the broad stage rate rather than the bin. -/
theorem child_cost_mul_accuracy_le_of_rate_le {s K A a a' b c u u' : ℝ}
    (hs : 2 < s) (hA : 0 ≤ A) (M m i i' : ℕ) (hi : i' + 1 ≤ i)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hba' : c * b ≤ a')
    (hu : 0 < u) (huu' : u ≤ u') :
    binNormCost s (Real.logb 2 (b / a)) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / s) *
        (2 : ℝ) ^ (-precision K A m i' a' u') ≤
      (2 : ℝ) ^ (-Real.logb 2 c / 2) *
        ((2 : ℝ) ^ (-precision K A M i a u - A + ((M : ℝ) - m) / K) *
          (2 : ℝ) ^ (-scaleMargin s * |Real.logb 2 (b / a)|)) := by
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos hc hb) hba'
  rw [Real.logb_mul hc.ne' hb.ne'] at hlog
  have hp : -precision K A m i' a' u' ≤
      -precision K A m i' b u' + (-Real.logb 2 c / 2) := by
    unfold precision
    linarith
  have hacc := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hacc
  have hparent := child_cost_mul_accuracy_le (K := K) hs hA M m i i' hi ha hb hu huu'
  calc
    _ ≤ binNormCost s (Real.logb 2 (b / a)) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / s) *
        ((2 : ℝ) ^ (-precision K A m i' b u') * (2 : ℝ) ^ (-Real.logb 2 c / 2)) :=
      mul_le_mul_of_nonneg_left hacc (mul_nonneg (binNormCost_pos _ _).le (by positivity))
    _ = (2 : ℝ) ^ (-Real.logb 2 c / 2) *
        (binNormCost s (Real.logb 2 (b / a)) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / s) *
          (2 : ℝ) ^ (-precision K A m i' b u')) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hparent (by positivity)

end Cslib.LogSpaceEstimation
