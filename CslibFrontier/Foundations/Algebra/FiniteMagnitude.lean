/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Magnitudes of finite sums and products

## Main results

* `Finset.abs_sum_mul_le`: bounded signed linear combinations.
* `Finset.sum_mul_le_of_card_support_le`: sums of bounded products with few nonzero factors.
* `Finset.abs_prod_le_one`: products of coefficients bounded by one.
* `List.abs_sum_map_le`: a sum of at most unit integers is bounded by the list length.

## References

Adapted selectively from
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.

`List.abs_sum_map_le` is moved from Samuel Schlesinger's AMS sketch
(`CslibFrontier.Computability.Streaming.AMS`).
-/

public section

namespace Finset

variable {ι R : Type*}

/-- If `|f i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, f i| ≤ s.card * A`. -/
theorem abs_sum_le_card_mul [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {f : ι → R}
    {A : R} (h : ∀ i ∈ s, |f i| ≤ A) : |∑ i ∈ s, f i| ≤ s.card * A :=
  (abs_sum_le_sum_abs f s).trans ((sum_le_card_nsmul s _ A h).trans_eq (nsmul_eq_mul _ _))

/-- A sum of products `A i * D i` over `s` in which at most `K` of the factors `A i` are nonzero,
each at most `CA`, and every `D i` lies in `[0, CD]`, is at most `K * CA * CD`. -/
theorem sum_mul_le_of_card_support_le [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [DecidableEq R] (s : Finset ι) {A D : ι → R} {CA CD : R} {K : ℕ} (hCA : 0 ≤ CA)
    (hCD : 0 ≤ CD) (hA : ∀ i ∈ s, A i ≤ CA) (hD0 : ∀ i ∈ s, 0 ≤ D i)
    (hD : ∀ i ∈ s, D i ≤ CD) (hK : #{i ∈ s | A i ≠ 0} ≤ K) :
    ∑ i ∈ s, A i * D i ≤ K * CA * CD := by
  calc
    _ = ∑ i ∈ s with A i ≠ 0, A i * D i :=
      (sum_filter_of_ne fun _ _ h => left_ne_zero_of_mul h).symm
    _ ≤ #{i ∈ s | A i ≠ 0} • (CA * CD) := sum_le_card_nsmul _ _ _ fun i hi => by
      have hi := (mem_filter.mp hi).1
      exact mul_le_mul (hA i hi) (hD i hi) (hD0 i hi) hCA
    _ ≤ K * CA * CD := by
      rw [nsmul_eq_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (Nat.mono_cast hK) (mul_nonneg hCA hCD)

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

namespace List

/-- A sum of at most unit integers is bounded by the number of terms. -/
theorem abs_sum_map_le {α : Type*} {f : α → ℤ} (hf : ∀ a, |f a| ≤ 1) (s : List α) :
    |(s.map f).sum| ≤ s.length := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    exact (abs_add_le _ _).trans (by linarith [hf a])

end List
