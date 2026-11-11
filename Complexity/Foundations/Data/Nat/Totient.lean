/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Totient.lean`)

public import Complexity.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# An elementary lower bound for Euler's totient function

Euler's product formula `φ n / n = ∏_{p ∣ n} (1 - 1/p)` together with the fact that the `i`-th
smallest prime factor of `n` is at least `i + 1` gives `φ n / n ≥ 1 / (ω n + 1)`, where `ω n` is the
number of distinct prime factors; since `2 ^ ω n ≤ n`, also `φ n / n ≥ 1 / (log₂ n + 1)`. The
bound is much weaker than the optimal order `φ n / n ≫ 1 / log log n` (Hardy and Wright's
Theorem 328, as cited in [de Wolf][deWolf2019], §5.3), but it already shows that a uniformly random
residue modulo `n` is a unit with inverse-logarithmic probability, as needed in the classical
post-processing of Shor's algorithm.

## Main results

* `Nat.prod_le_card_add_one_mul_prod_sub_one`: `∏ p ∈ s, p ≤ (#s + 1) * ∏ p ∈ s, (p - 1)` for a
  finset `s` of numbers at least `2`.
* `Nat.le_totient_mul_card_primeFactors_add_one`: `n ≤ φ n * (#n.primeFactors + 1)`.
* `Nat.card_primeFactors_le_log`: `#n.primeFactors ≤ Nat.log 2 n`.
* `Nat.le_totient_mul_log_add_one`: `n ≤ φ n * (Nat.log 2 n + 1)`.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

open Finset

namespace Nat

/-- If every element of `s` is at least `2`, then `∏ p ∈ s, p ≤ (#s + 1) * ∏ p ∈ s, (p - 1)`: the
`i`-th smallest element is at least `i + 1`, so `∏ p ∈ s, (1 - 1/p) ≥ ∏ i < #s, (1 - 1/(i+2))
= 1 / (#s + 1)`. -/
theorem prod_le_card_add_one_mul_prod_sub_one (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    ∏ p ∈ s, p ≤ (#s + 1) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hs' : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (mem_insert_of_mem hp)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    -- `s ⊆ Ico 2 a`, so `#s + 2 ≤ a`.
    have hcard : #s + 2 ≤ a := by
      have := card_le_card fun p hp => mem_Ico.mpr ⟨hs' p hp, ha p hp⟩
      rw [card_Ico] at this
      have := hs a (mem_insert_self a s)
      omega
    rw [prod_insert has, prod_insert has, card_insert_of_notMem has]
    obtain ⟨m, rfl⟩ : ∃ m, a = #s + 2 + m := ⟨a - (#s + 2), by omega⟩
    calc (#s + 2 + m) * ∏ p ∈ s, p
        ≤ (#s + 2 + m) * ((#s + 1) * ∏ p ∈ s, (p - 1)) := Nat.mul_le_mul_left _ (ih hs')
      _ ≤ (#s + 1 + 1) * ((#s + 2 + m - 1) * ∏ p ∈ s, (p - 1)) := by
        rw [← mul_assoc, ← mul_assoc]
        refine Nat.mul_le_mul_right _ ?_
        rw [show #s + 2 + m - 1 = #s + 1 + m by omega]
        nlinarith

/-- An elementary lower bound for Euler's totient function: `n ≤ φ n * (ω n + 1)`, where
`ω n = #n.primeFactors`; equivalently `φ n / n ≥ 1 / (ω n + 1)`. -/
theorem le_totient_mul_card_primeFactors_add_one (n : ℕ) :
    n ≤ φ n * (#n.primeFactors + 1) := by
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    prod_pos fun p hp => Nat.sub_pos_of_lt (prime_of_mem_primeFactors hp).one_lt
  refine le_of_mul_le_mul_right ?_ hpos
  rw [← totient_mul_prod_primeFactors, mul_assoc]
  exact Nat.mul_le_mul_left _
    (prod_le_card_add_one_mul_prod_sub_one _ fun p hp => (prime_of_mem_primeFactors hp).two_le)

/-- A number has at most `log₂ n` distinct prime factors. -/
theorem card_primeFactors_le_log (n : ℕ) : #n.primeFactors ≤ Nat.log 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine le_log_of_pow_le one_lt_two ?_
  calc 2 ^ #n.primeFactors ≤ ∏ p ∈ n.primeFactors, p :=
        pow_card_le_prod _ _ _ fun p hp => (prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd hn (prod_primeFactors_dvd n)

/-- `n ≤ φ n * (log₂ n + 1)`, i.e. `φ n / n ≥ 1 / (log₂ n + 1)` for `n ≠ 0`. -/
theorem le_totient_mul_log_add_one (n : ℕ) : n ≤ φ n * (Nat.log 2 n + 1) :=
  (le_totient_mul_card_primeFactors_add_one n).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (card_primeFactors_le_log n) 1))

end Nat
