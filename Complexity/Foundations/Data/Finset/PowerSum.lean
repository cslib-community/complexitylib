/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Order/Chebyshev.lean`)

public import Complexity.Init
public import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# A power-sum inequality

For nonnegative `c₁, …, cₙ` and `k ≥ 1`, Alon, Matias and Szegedy bound the product of the first
and `(2 k - 1)`-th power sums by the `k`-th one [AlonMatiasSzegedy1999, Fact in the proof of
Theorem 2.1]:

  `(∑ cᵢ) (∑ cᵢ ^ (2 k - 1)) ≤ n ^ (1 - 1 / k) (∑ cᵢ ^ k) ^ 2`.

`Finset.sum_mul_sum_pow_le` states it raised to the `k`-th power, which avoids real exponents, with
`k + 1` in place of `k`. The proof is the source's: with `M = max cᵢ`, `M ^ k ≤ ∑ cᵢ ^ k` and
`∑ cᵢ ^ (2 k - 1) ≤ M ^ (k - 1) ∑ cᵢ ^ k`, while `(∑ cᵢ) ^ k ≤ n ^ (k - 1) ∑ cᵢ ^ k` is the power
mean inequality `pow_sum_le_card_mul_sum_pow`. The source notes that `c₁ = n ^ (1 / k)`,
`c₂ = ⋯ = cₙ = 1` shows the inequality is tight up to a constant factor.

## Main results

* `Finset.sum_mul_sum_pow_le`: `((∑ cᵢ) (∑ cᵢ ^ (2 k + 1))) ^ (k + 1) ≤
  n ^ k (∑ cᵢ ^ (k + 1)) ^ (2 (k + 1))`.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, proof of Theorem 2.1][AlonMatiasSzegedy1999]
-/

public section

namespace Finset

variable {ι α : Type*} [CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]

/-- **The AMS power-sum inequality** [AlonMatiasSzegedy1999, Fact in the proof of Theorem 2.1]:
for nonnegative `c` on a finite set of size `n`,
`((∑ cᵢ) (∑ cᵢ ^ (2 k + 1))) ^ (k + 1) ≤ n ^ k (∑ cᵢ ^ (k + 1)) ^ (2 (k + 1))`, that is,
`(∑ cᵢ) (∑ cᵢ ^ (2 k' - 1)) ≤ n ^ (1 - 1 / k') (∑ cᵢ ^ k') ^ 2` for `k' = k + 1`. -/
theorem sum_mul_sum_pow_le (s : Finset ι) {c : ι → α} (hc : ∀ i ∈ s, 0 ≤ c i) (k : ℕ) :
    ((∑ i ∈ s, c i) * ∑ i ∈ s, c i ^ (2 * k + 1)) ^ (k + 1) ≤
      (#s : α) ^ k * (∑ i ∈ s, c i ^ (k + 1)) ^ (2 * (k + 1)) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨i₀, hi₀, hM⟩ := s.exists_mem_eq_sup' hs c
  have hF : 0 ≤ ∑ i ∈ s, c i ^ (k + 1) := sum_nonneg fun i hi => pow_nonneg (hc i hi) _
  have hM0 : 0 ≤ s.sup' hs c := hM ▸ hc i₀ hi₀
  -- The largest term: `M ^ (k + 1) ≤ F_{k + 1}`.
  have hMk : (s.sup' hs c) ^ (k + 1) ≤ ∑ i ∈ s, c i ^ (k + 1) := by
    rw [hM]
    exact single_le_sum (f := fun i => c i ^ (k + 1)) (fun i hi => pow_nonneg (hc i hi) _) hi₀
  -- `F_{2k+1} ≤ M ^ k F_{k+1}`.
  have h2k : ∑ i ∈ s, c i ^ (2 * k + 1) ≤ (s.sup' hs c) ^ k * ∑ i ∈ s, c i ^ (k + 1) := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have : c i ^ (2 * k + 1) = c i ^ k * c i ^ (k + 1) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hc i hi) (le_sup' c hi) k)
      (pow_nonneg (hc i hi) _)
  have hJ := pow_sum_le_card_mul_sum_pow hc k
  have h2k0 : 0 ≤ ∑ i ∈ s, c i ^ (2 * k + 1) := sum_nonneg fun i hi => pow_nonneg (hc i hi) _
  have hs0 : (0 : α) ≤ (#s : α) ^ k := pow_nonneg (Nat.cast_nonneg _) _
  calc ((∑ i ∈ s, c i) * ∑ i ∈ s, c i ^ (2 * k + 1)) ^ (k + 1)
      = (∑ i ∈ s, c i) ^ (k + 1) * (∑ i ∈ s, c i ^ (2 * k + 1)) ^ (k + 1) := mul_pow _ _ _
    _ ≤ (#s ^ k * ∑ i ∈ s, c i ^ (k + 1)) *
          ((s.sup' hs c) ^ k * ∑ i ∈ s, c i ^ (k + 1)) ^ (k + 1) :=
        mul_le_mul hJ (pow_le_pow_left₀ h2k0 h2k _) (pow_nonneg h2k0 _) (mul_nonneg hs0 hF)
    _ = #s ^ k * (∑ i ∈ s, c i ^ (k + 1)) *
          (((s.sup' hs c) ^ (k + 1)) ^ k * (∑ i ∈ s, c i ^ (k + 1)) ^ (k + 1)) := by ring
    _ ≤ #s ^ k * (∑ i ∈ s, c i ^ (k + 1)) *
          ((∑ i ∈ s, c i ^ (k + 1)) ^ k * (∑ i ∈ s, c i ^ (k + 1)) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (pow_nonneg hM0 _) hMk k) (pow_nonneg hF _)) (mul_nonneg hs0 hF)
    _ = #s ^ k * (∑ i ∈ s, c i ^ (k + 1)) ^ (2 * (k + 1)) := by ring

end Finset
