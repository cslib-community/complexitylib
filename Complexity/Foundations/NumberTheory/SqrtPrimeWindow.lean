/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.NumberTheory.PrimeWindow

/-!
# Prime windows below a square root

This finite window is independent of the application that chooses a prime from it. Membership
has both real-endpoint and integer-square characterizations, including the closed lower and
open upper endpoints. Counting reuses the general prime-window estimates.

## Main definitions

* `Nat.sqrtPrimeWindow`: the primes in `[sqrt D / 2, sqrt D)`.

## Main results

* `Real.four_le_sqrt_natCast`: the shared endpoint bound for natural parameters at least 16.
* `Nat.mem_sqrtPrimeWindow`, `Nat.mem_sqrtPrimeWindow_iff_sq`: membership tests.
* `Nat.sqrtPrimeWindow_eq_filter`: an integer-only enumeration.
* `Nat.card_sqrtPrimeWindow_lt_sqrt`: the upper cardinality bound.
* `Nat.exists_pos_mul_sqrt_div_log_le_card_sqrtPrimeWindow`: a uniform lower bound.

## References

Adapted from the prime-window definitions and estimates in
[Anthropic's pinned hashing source](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem17/Hashing.lean).
-/

@[expose] public section

/-- The real square root of a natural window parameter at least 16 is at least four. -/
theorem Real.four_le_sqrt_natCast {D : ℕ} (hD : 16 ≤ D) : 4 ≤ Real.sqrt (D : ℝ) :=
  Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hD)

namespace Nat

open Classical in
/-- Prime numbers in the half-open real interval `[sqrt D / 2, sqrt D)`.
-/
noncomputable def sqrtPrimeWindow (D : ℕ) : Finset ℕ :=
  (Finset.range D).filter fun p => p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D

/-- Window membership is equivalent to primality and the two real endpoint inequalities. The
finite enumeration bound in `sqrtPrimeWindow` excludes no member of the interval.
-/
theorem mem_sqrtPrimeWindow {D p : ℕ} :
    p ∈ sqrtPrimeWindow D ↔ p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D := by
  unfold sqrtPrimeWindow
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  -- From `p < √D` we get `p ≤ p² < D`.
  have hsq : p ^ 2 < D := by exact_mod_cast (Real.lt_sqrt (Nat.cast_nonneg p)).1 h.2.2
  exact (Nat.le_self_pow two_ne_zero p).trans_lt hsq

/-- Characterize window membership using primality and integer-square inequalities, including the
closed lower and open upper endpoints.
-/
theorem mem_sqrtPrimeWindow_iff_sq {D p : ℕ} :
    p ∈ sqrtPrimeWindow D ↔ p.Prime ∧ D ≤ 4 * p ^ 2 ∧ p ^ 2 < D := by
  rw [mem_sqrtPrimeWindow]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsqrt0 : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hsqrt : (Real.sqrt (D : ℝ)) ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
  constructor
  · rintro ⟨hp, hlo, hhi⟩
    refine ⟨hp, ?_, ?_⟩
    · have h : (D : ℝ) ≤ 4 * (p : ℝ) ^ 2 := by nlinarith
      exact_mod_cast h
    · exact_mod_cast (Real.lt_sqrt hp0).1 hhi
  · rintro ⟨hp, hlo, hhi⟩
    refine ⟨hp, ?_, (Real.lt_sqrt hp0).2 (by exact_mod_cast hhi)⟩
    have h : (D : ℝ) ≤ 4 * (p : ℝ) ^ 2 := by exact_mod_cast hlo
    nlinarith

/-- Enumerate the real prime window using a decidable filter of the integers below `D`.
-/
theorem sqrtPrimeWindow_eq_filter (D : ℕ) :
    sqrtPrimeWindow D = (Finset.range D).filter fun p => p.Prime ∧ D ≤ 4 * p ^ 2 ∧ p ^ 2 < D := by
  ext p
  rw [mem_sqrtPrimeWindow_iff_sq, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨(Nat.le_self_pow two_ne_zero p).trans_lt h.2.2, h⟩, fun h => h.2⟩

/-- For `D ≥ 16`, the number of primes in `sqrtPrimeWindow D` is strictly less than `sqrt D`.
-/
theorem card_sqrtPrimeWindow_lt_sqrt (D : ℕ) (hD : 16 ≤ D) :
    ((sqrtPrimeWindow D).card : ℝ) < Real.sqrt D := by
  have hpos : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < D))
  -- The primes in the range are among the numbers `1, …, ⌈√D⌉ - 1`.
  have hsub : sqrtPrimeWindow D ⊆ Finset.Ico 1 ⌈Real.sqrt D⌉₊ := by
    intro p hp
    obtain ⟨hprime, -, hlt⟩ := mem_sqrtPrimeWindow.1 hp
    exact Finset.mem_Ico.2 ⟨hprime.one_lt.le, Nat.lt_ceil.2 hlt⟩
  have hcard : (sqrtPrimeWindow D).card + 1 ≤ ⌈Real.sqrt D⌉₊ := by
    have hle := Finset.card_le_card hsub
    have hone : 1 ≤ ⌈Real.sqrt D⌉₊ := Nat.one_le_ceil_iff.2 hpos
    rw [Nat.card_Ico] at hle
    omega
  have hcast : ((sqrtPrimeWindow D).card : ℝ) + 1 ≤ (⌈Real.sqrt D⌉₊ : ℝ) := by exact_mod_cast hcard
  linarith [Nat.ceil_lt_add_one hpos.le]

/-- There is a universal positive `c` such that every window with `D ≥ 16` contains at least `c *
sqrt D / log D` primes. The proof uses the all-window counting form of Bertrand’s postulate from
`PrimeWindow`, with no prime-number-theorem assumption.
-/
theorem exists_pos_mul_sqrt_div_log_le_card_sqrtPrimeWindow :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 16 ≤ D →
      c * (Real.sqrt D / Real.log D) ≤ ((sqrtPrimeWindow D).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := Nat.exists_forall_mul_sqrt_div_log_le_card_primes
  exact ⟨c, hc, fun D hD => hcount D hD _
    fun _ hp hge hlt => mem_sqrtPrimeWindow.2 ⟨hp, hge, hlt⟩⟩

end Nat
