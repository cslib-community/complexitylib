/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Int/Radix.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Vanishing of bounded signed radix sums

A polynomial/radix expansion `∑ k < n, a k * K ^ k = 0` with integer coefficients strictly bounded
in magnitude by the radix `K` has all coefficients equal to zero.

## Main results

* `Int.eq_zero_of_sum_mul_pow_eq_zero`: unique zero representation for signed digits with
  `|a k| < K`.
-/

public section

namespace Int

/-- If every integer coefficient `a k` (`k < n`) has `|a k| < K`, then
`∑ k ∈ Finset.range n, a k * K ^ k = 0` forces every `a k` to be `0`. -/
theorem eq_zero_of_sum_mul_pow_eq_zero :
    ∀ {n : ℕ} {K : ℤ} {a : ℕ → ℤ},
      (∀ k < n, |a k| < K) → ∑ k ∈ Finset.range n, a k * K ^ k = 0 → ∀ k < n, a k = 0
  | 0, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, K, a, ha, hsum, k, hk => by
    have hK : 0 < K := lt_of_le_of_lt (abs_nonneg (a 0)) (ha 0 (Nat.zero_lt_succ n))
    have hsplit : ∑ i ∈ Finset.range (n + 1), a i * K ^ i =
        K * ∑ i ∈ Finset.range n, a (i + 1) * K ^ i + a 0 := by
      rw [Finset.sum_range_succ', pow_zero, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ']
      ring
    have ha0_dvd : K ∣ a 0 :=
      ⟨-(∑ i ∈ Finset.range n, a (i + 1) * K ^ i), by linarith [hsum, hsplit]⟩
    have ha0 : a 0 = 0 := by
      by_contra hne
      have hle : K ≤ |a 0| := Int.le_of_dvd (abs_pos.2 hne)
        ((Int.natCast_natAbs (a 0)).symm ▸ Int.dvd_natAbs.2 ha0_dvd)
      exact absurd (ha 0 (Nat.zero_lt_succ n)) (not_lt.2 hle)
    have htail : ∑ i ∈ Finset.range n, a (i + 1) * K ^ i = 0 := by
      have hmul : K * ∑ i ∈ Finset.range n, a (i + 1) * K ^ i = 0 := by
        linarith [hsum, hsplit, ha0]
      exact (mul_eq_zero.1 hmul).resolve_left hK.ne'
    have ih := eq_zero_of_sum_mul_pow_eq_zero
      (fun i hi => ha (i + 1) (Nat.succ_lt_succ hi)) htail
    rcases k with _ | k
    · exact ha0
    · exact ih k (Nat.lt_of_succ_lt_succ hk)

end Int
