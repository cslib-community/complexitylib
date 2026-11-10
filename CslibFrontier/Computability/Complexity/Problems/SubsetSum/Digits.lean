/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Ring

/-!
# Sums of numbers with digits zero and one

Each of finitely many numbers has, in base `b`, the digit one at the positions of a finite set and
zero elsewhere. If, at every position, fewer than `b` of the numbers have the digit one, then adding
any of them produces no carries: the sum has, at each position, the number of chosen summands with
the digit one there. This is the arithmetic behind the digit construction reducing 3SAT to subset
sum [Sipser, Theorem 7.56][Sipser2013].

## Main results

* `Nat.sum_range_mul_pow_inj`: base-`b` digits below `b` are determined by the number.
* `Nat.sum_range_mul_pow_lt`: a number with `N` base-`b` digits is less than `b ^ N`.
* `Cslib.Complexity.sum_sum_pow_eq_iff`: without carries, a subfamily sums to the number with
  digits `T` exactly when, at each position, `T` of its members have the digit one there.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

open Finset

namespace Nat

private theorem sum_range_mul_pow_eq_ofDigits (b N : ℕ) (a : ℕ → ℕ) :
    ∑ p ∈ range N, a p * b ^ p = ofDigits b ((List.range N).map a) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sum_range_succ, ih, List.range_succ, List.map_append, List.map_singleton, ofDigits_append]
    simp [mul_comm]

/-- Base-`b` digits that are less than `b` are determined by the number they represent. -/
theorem sum_range_mul_pow_inj {b N : ℕ} {a c : ℕ → ℕ} (ha : ∀ p < N, a p < b)
    (hc : ∀ p < N, c p < b) :
    ∑ p ∈ range N, a p * b ^ p = ∑ p ∈ range N, c p * b ^ p ↔ ∀ p < N, a p = c p := by
  refine ⟨fun h p hp => ?_, fun h => sum_congr rfl fun p hp => by rw [h p (mem_range.1 hp)]⟩
  rcases le_or_gt b 1 with hb | hb
  · have := ha p hp; have := hc p hp; omega
  · rw [sum_range_mul_pow_eq_ofDigits, sum_range_mul_pow_eq_ofDigits] at h
    have hL := ofDigits_inj_of_len_eq hb (by simp) (by simpa using ha) (by simpa using hc) h
    have := congrArg (·[p]?) hL
    simpa [hp] using this

/-- A number with base-`b` digits below `b` at the positions below `N` is less than `b ^ N`. -/
theorem sum_range_mul_pow_lt {b N : ℕ} {a : ℕ → ℕ} (ha : ∀ p < N, a p < b) :
    ∑ p ∈ range N, a p * b ^ p < b ^ N := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  rcases le_or_gt b 1 with hb | hb
  · obtain rfl : b = 1 := by have := ha 0 hN; omega
    simpa using fun i hi => by have := ha i hi; omega
  · rw [sum_range_mul_pow_eq_ofDigits]
    simpa using ofDigits_lt_base_pow_length (l := (List.range N).map a) hb (by simpa using ha)

end Nat

namespace Cslib.Complexity

/-- **No carries.** Let each `x ∈ U` have base-`b` digit one exactly at the positions `col x`, all
below `N`, with fewer than `b` members of `U` having digit one at each position. Then a subfamily
`F ⊆ U` sums to the number with digits `T < b` exactly when, at each position `p < N`, exactly
`T p` members of `F` have digit one at `p`. -/
theorem sum_sum_pow_eq_iff {ι : Type*} {U F : Finset ι} (hF : F ⊆ U)
    {col : ι → Finset ℕ} {b N : ℕ} {T : ℕ → ℕ} (hcol : ∀ x ∈ U, col x ⊆ range N)
    (hU : ∀ p < N, #{x ∈ U | p ∈ col x} < b) (hT : ∀ p < N, T p < b) :
    ∑ x ∈ F, ∑ p ∈ col x, b ^ p = ∑ p ∈ range N, T p * b ^ p ↔
      ∀ p < N, #{x ∈ F | p ∈ col x} = T p := by
  have hswap : ∑ x ∈ F, ∑ p ∈ col x, b ^ p = ∑ p ∈ range N, #{x ∈ F | p ∈ col x} * b ^ p := by
    calc ∑ x ∈ F, ∑ p ∈ col x, b ^ p
        = ∑ x ∈ F, ∑ p ∈ range N, if p ∈ col x then b ^ p else 0 := by
          refine sum_congr rfl fun x hx => ?_
          rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 (hcol x (hF hx))]
      _ = ∑ p ∈ range N, ∑ x ∈ F, if p ∈ col x then b ^ p else 0 := sum_comm
      _ = ∑ p ∈ range N, #{x ∈ F | p ∈ col x} * b ^ p := by
          refine sum_congr rfl fun p _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.cast_id]
  rw [hswap]
  exact Nat.sum_range_mul_pow_inj
    (fun p hp => (card_le_card (filter_subset_filter _ hF)).trans_lt (hU p hp)) hT

end Cslib.Complexity
