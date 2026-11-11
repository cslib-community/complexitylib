/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, geometric sums)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum

/-!
# Sums of powers of the distance to a real number

For `0 < q ≤ 1 / 2` and a real `x` between the integers `i₀` and `i₀ + 1`, the sum of
`q ^ |i - x|` over the natural numbers `i < N` is two geometric sums, one on each side of `x`.
It is therefore at most `(1 + 2 q) (q ^ (x - i₀) + q ^ (i₀ + 1 - x))`. This is the
nearest-integer bound of [OpenAI, §3][OpenAI2026DepthFive].

## Main results

* `Real.sum_range_rpow_abs_sub_le`: the bound by the two terms nearest to `x`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §3 (unrefereed preprint)
-/

public section

namespace Real

open Finset

/-- The sum of `q ^ |i - x|` over `i < N` is at most `1 + 2 q` times the sum of the two terms
on either side of `x`. -/
theorem sum_range_rpow_abs_sub_le {q x : ℝ} (hq : 0 < q) (hq' : q ≤ 1 / 2) (N : ℕ) {i₀ : ℕ}
    (h₀ : i₀ ≤ x) (h₁ : x ≤ i₀ + 1) :
    ∑ i ∈ range N, q ^ |(i : ℝ) - x| ≤ (1 + 2 * q) * (q ^ (x - i₀) + q ^ (i₀ + 1 - x)) := by
  have hgeom (M : ℕ) : ∑ t ∈ range M, q ^ t ≤ 1 + 2 * q := by
    have h := mul_neg_geom_sum q M
    nlinarith [pow_nonneg hq.le M, sum_nonneg fun t (_ : t ∈ range M) => pow_nonneg hq.le t]
  calc ∑ i ∈ range N, q ^ |(i : ℝ) - x|
      ≤ ∑ i ∈ range (i₀ + 1 + N), q ^ |(i : ℝ) - x| :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by lia)) fun _ _ _ => rpow_nonneg hq.le _
    _ = q ^ (x - i₀) * ∑ t ∈ range (i₀ + 1), q ^ t +
          q ^ (i₀ + 1 - x) * ∑ t ∈ range N, q ^ t := by
        rw [sum_range_add, ← sum_range_reflect (fun i : ℕ => q ^ |(i : ℝ) - x|), mul_sum, mul_sum]
        congr 1 <;> refine sum_congr rfl fun t ht => ?_
        · have ht : t ≤ i₀ := Nat.lt_succ_iff.1 (mem_range.1 ht)
          rw [← rpow_natCast, ← rpow_add hq, show i₀ + 1 - 1 - t = i₀ - t by lia,
            Nat.cast_sub ht, abs_of_nonpos (by linarith [t.cast_nonneg (α := ℝ)])]
          congr 1
          ring
        · rw [← rpow_natCast, ← rpow_add hq, abs_of_nonneg (by push_cast; linarith)]
          congr 1
          push_cast
          ring
    _ ≤ q ^ (x - i₀) * (1 + 2 * q) + q ^ (i₀ + 1 - x) * (1 + 2 * q) := by
        gcongr <;> exact hgeom _
    _ = _ := by ring

end Real
