/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Strict bounds for finite geometric tails

## Main results

* `geom_sum_Ico_lt_of_lt_one`: the strict bound for `∑ i ∈ Ico m n, x ^ i` when `0 < x < 1`.

## References

Adapted selectively from
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

/-- For `0 < x < 1`, `∑ i ∈ Ico m n, x ^ i < x ^ m / (1 - x)`. Mathlib's
`geom_sum_Ico_le_of_lt_one` has `≤`, for `0 ≤ x`. -/
theorem geom_sum_Ico_lt_of_lt_one {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x : K} (hx : 0 < x) (hx1 : x < 1) (m n : ℕ) :
    ∑ i ∈ Finset.Ico m n, x ^ i < x ^ m / (1 - x) := by
  have hpos : 0 < 1 - x := sub_pos.2 hx1
  rcases le_total m n with hmn | hnm
  · rw [geom_sum_Ico' hx1.ne hmn]
    exact div_lt_div_of_pos_right (sub_lt_self _ (pow_pos hx n)) hpos
  · rw [Finset.Ico_eq_empty_of_le hnm, Finset.sum_empty]
    exact div_pos (pow_pos hx m) hpos
