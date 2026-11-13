/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# The balanced multinomial coefficient is the largest

For `r` parts of total `r m`, the multinomial coefficient is largest at the balanced composition
`(m, …, m)`: `∏ i, (k i)! ≥ (m !) ^ r` whenever `∑ i, k i = r m` (`pow_factorial_le_prod_factorial`,
from `m ! m ^ n ≤ n ! m ^ m`, `factorial_mul_pow_le_factorial_mul_pow`). Since the `r ^ d`
words of length `d = r m` over `r` letters fall into at most `(d + 1) ^ r` compositions, the
balanced coefficient is at least `r ^ d / (d + 1) ^ r` (`pow_mul_pow_factorial_le`):

`r ^ (r m) (m !) ^ r ≤ (r m + 1) ^ r (r m)!`.

This is an explicit lower bound used in the estimate
`d! / ((d/r)!)^r = r^d / d^{Θ(r)}` in [ChanItakuraMaYu2026], proof of Theorem 3.4. The full
`Θ` estimate, including a complementary upper bound with polynomial deficit, is not proved here.

## Main results

* `Nat.factorial_mul_pow_le_factorial_mul_pow`, `Nat.pow_factorial_le_prod_factorial`,
  `Nat.multinomial_mul_pow_factorial_le`, `Nat.pow_mul_pow_factorial_le`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Nat

open Finset

/-- `m ! m ^ n ≤ n ! m ^ m` for all `m`, `n`: comparing `n !` with `m !` costs at most a factor `m`
per step. -/
theorem factorial_mul_pow_le_factorial_mul_pow (n m : ℕ) : m ! * m ^ n ≤ n ! * m ^ m := by
  rcases le_total m n with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 : m ! * m ^ j ≤ (m + j)! :=
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ m) j)).trans
        factorial_mul_pow_le_factorial
    calc m ! * m ^ (m + j) = m ! * m ^ j * m ^ m := by ring
      _ ≤ (m + j)! * m ^ m := Nat.mul_le_mul_right _ h1
  · have h1 : m ! ≤ n ! * m ^ (m - n) := by
      rw [← factorial_mul_descFactorial (Nat.sub_le m n), Nat.sub_sub_self h]
      exact Nat.mul_le_mul_left _ (descFactorial_le_pow m _)
    calc m ! * m ^ n ≤ n ! * m ^ (m - n) * m ^ n := Nat.mul_le_mul_right _ h1
      _ = n ! * m ^ m := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]

/-- **The balanced factorial product is the smallest**: if `∑_{i ∈ s} k i = |s| m`, then
`(m !) ^ |s| ≤ ∏_{i ∈ s} (k i)!`. -/
theorem pow_factorial_le_prod_factorial {ι : Type*} (s : Finset ι) (k : ι → ℕ) {m : ℕ}
    (hk : ∑ i ∈ s, k i = #s * m) : (m !) ^ #s ≤ ∏ i ∈ s, (k i)! := by
  have h := prod_le_prod (s := s) fun i _ => factorial_mul_pow_le_factorial_mul_pow (k i) m
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_pow_eq_pow_sum, hk, prod_const,
    ← pow_mul, mul_comm m] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos' m _)
where
  pow_pos' (m e : ℕ) : 0 < m ^ (e * m) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact pow_pos hm _

/-- **The balanced multinomial coefficient is the largest**: if `∑_{i ∈ s} k i = |s| m`, then
`multinomial s k · (m !) ^ |s| ≤ (|s| m)!`. -/
theorem multinomial_mul_pow_factorial_le {ι : Type*} (s : Finset ι) (k : ι → ℕ) {m : ℕ}
    (hk : ∑ i ∈ s, k i = #s * m) : multinomial s k * (m !) ^ #s ≤ (#s * m)! := by
  rw [← hk, ← multinomial_spec s k, mul_comm (∏ i ∈ s, _)]
  exact Nat.mul_le_mul_left _ (pow_factorial_le_prod_factorial s k hk)

/-- **The balanced multinomial coefficient is large**: `r ^ (r m) (m !) ^ r ≤ (r m + 1) ^ r (r m)!`,
that is, `(r m)! / (m !) ^ r ≥ r ^ (r m) / (r m + 1) ^ r`. -/
theorem pow_mul_pow_factorial_le (r m : ℕ) :
    r ^ (r * m) * (m !) ^ r ≤ (r * m + 1) ^ r * (r * m)! := by
  classical
  have hsum := sum_pow_eq_sum_piAntidiag (univ : Finset (Fin r)) (fun _ => (1 : ℕ)) (r * m)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow,
    prod_const_one, Nat.cast_id] at hsum
  have hterm : ∀ k ∈ piAntidiag (univ : Finset (Fin r)) (r * m),
      multinomial univ k * (m !) ^ r ≤ (r * m)! := by
    intro k hk
    have h := multinomial_mul_pow_factorial_le univ k (m := m)
      (by rw [(mem_piAntidiag.mp hk).1, card_univ, Fintype.card_fin])
    simpa [card_univ, Fintype.card_fin] using h
  have hcard : #(piAntidiag (univ : Finset (Fin r)) (r * m)) ≤ (r * m + 1) ^ r := by
    have : piAntidiag (univ : Finset (Fin r)) (r * m) ⊆
        Fintype.piFinset fun _ => range (r * m + 1) := by
      intro k hk
      refine Fintype.mem_piFinset.mpr fun i => mem_range.mpr (Nat.lt_succ_of_le ?_)
      rw [← (mem_piAntidiag.mp hk).1]
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    refine (card_le_card this).trans ?_
    simp [Fintype.card_piFinset]
  calc r ^ (r * m) * (m !) ^ r
      = ∑ k ∈ piAntidiag (univ : Finset (Fin r)) (r * m), multinomial univ k * (m !) ^ r := by
        rw [hsum, sum_mul]
    _ ≤ ∑ _k ∈ piAntidiag (univ : Finset (Fin r)) (r * m), (r * m)! := sum_le_sum hterm
    _ = #(piAntidiag (univ : Finset (Fin r)) (r * m)) * (r * m)! := by rw [sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hcard

end Nat
