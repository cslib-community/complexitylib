/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Magnitudes of finite sums and products

## Main results

* `Finset.abs_sum_mul_le`: bounded signed linear combinations.
* `Finset.abs_prod_le_one`: products of coefficients bounded by one.

## References

Adapted selectively from
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

namespace Finset

variable {ι R : Type*}

/-- If `|f i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, f i| ≤ s.card * A`. -/
theorem abs_sum_le_card_mul [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {f : ι → R}
    {A : R} (h : ∀ i ∈ s, |f i| ≤ A) : |∑ i ∈ s, f i| ≤ s.card * A :=
  (abs_sum_le_sum_abs f s).trans ((sum_le_card_nsmul s _ A h).trans_eq (nsmul_eq_mul _ _))

/-- If `|c i| ≤ 1` and `|a i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, c i * a i| ≤ s.card * A`. -/
theorem abs_sum_mul_le [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {c a : ι → R}
    {A : R} (hc : ∀ i ∈ s, |c i| ≤ 1) (ha : ∀ i ∈ s, |a i| ≤ A) :
    |∑ i ∈ s, c i * a i| ≤ s.card * A :=
  abs_sum_le_card_mul s fun i hi =>
    (abs_mul (c i) (a i)).trans_le
      ((mul_le_of_le_one_left (abs_nonneg _) (hc i hi)).trans (ha i hi))

/-- If `|f i| ≤ 1` for all `i ∈ s`, then `|∏ i ∈ s, f i| ≤ 1`. -/
theorem abs_prod_le_one [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι)
    {f : ι → R} (h : ∀ i ∈ s, |f i| ≤ 1) : |∏ i ∈ s, f i| ≤ 1 :=
  (abs_prod s f).trans_le (prod_le_one₀ (fun _ _ => abs_nonneg _) h)


end Finset
